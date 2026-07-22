package proverinterface.webserver;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.zip.GZIPOutputStream;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import com.sun.net.httpserver.HttpServer;

import logic.problem.Problem;
import logic.signedFormulas.SignedFormulaCreator;
import main.newstrategy.Prover;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer;
import main.tableau.Method;
import main.tableau.Proof;
import proverinterface.RuleStructureFactory;
import proverinterface.proofviewer.IPLHtmlExporter;
import proverinterface.proofviewer.IPLProofTreeExporter;

/**
 * Minimal HTTP server exposing the IPL KE-tableau prover over the web.
 *
 * <p>Endpoints:</p>
 * <ul>
 *   <li>{@code GET  /}             — landing page (HTML embedded below)</li>
 *   <li>{@code GET  /api/examples} — JSON list of preset formulas</li>
 *   <li>{@code POST /api/prove}    — body {@code {"formula":"...", "name":"..."}};
 *                                    returns the full self-contained HTML produced by
 *                                    {@link IPLHtmlExporter}</li>
 * </ul>
 *
 * <p>Uses only the JDK's {@link HttpServer} so the project doesn't gain any new
 * runtime dependency. The IPL prover currently relies on global static state
 * (notably {@link IPLTracer}), so all proof requests are serialized through
 * a single-thread executor under a global lock. A per-request refactor is
 * tracked separately.</p>
 *
 * <p>Port: defaults to 8080, overridable via CLI arg or {@code PORT} env var
 * (used by Fly.io / Heroku-style platforms).</p>
 */
public final class IPLWebServer {

    private static final int DEFAULT_PORT = 8080;
    private static final int PROOF_TIMEOUT_SECONDS = 300; // 5 minutes
    private static final Object PROVER_LOCK = new Object();

    private static final ExecutorService PROVER_EXECUTOR =
            Executors.newSingleThreadExecutor(r -> {
                Thread t = new Thread(r, "ipl-prover");
                t.setDaemon(true);
                return t;
            });

    public static void main(String[] args) throws IOException {
        int port = resolvePort(args);

        HttpServer server = HttpServer.create(new InetSocketAddress(port), 0);
        server.createContext("/api/examples", new ExamplesHandler());
        server.createContext("/api/prove",    new ProveHandler());
        // "/" must be registered last because HttpServer dispatches by longest-prefix match.
        server.createContext("/", new IndexHandler());
        server.setExecutor(Executors.newFixedThreadPool(8, r -> {
            Thread t = new Thread(r, "ipl-http");
            t.setDaemon(true);
            return t;
        }));
        server.start();
        System.out.println("[IPLWebServer] listening on http://0.0.0.0:" + port);
    }

    private static int resolvePort(String[] args) {
        // CLI > env > default
        if (args != null && args.length > 0) {
            try { return Integer.parseInt(args[0]); }
            catch (NumberFormatException ignored) {}
        }
        String env = System.getenv("PORT");
        if (env != null) {
            try { return Integer.parseInt(env); }
            catch (NumberFormatException ignored) {}
        }
        return DEFAULT_PORT;
    }

    // ====================================================================
    //  Handlers
    // ====================================================================

    private static final class IndexHandler implements HttpHandler {
        @Override
        public void handle(HttpExchange ex) throws IOException {
            if (!"GET".equals(ex.getRequestMethod())) {
                respondText(ex, 405, "Method Not Allowed");
                return;
            }
            String path = ex.getRequestURI().getPath();
            if (!"/".equals(path) && !"/index.html".equals(path)) {
                respondText(ex, 404, "Not Found: " + path);
                return;
            }
            byte[] html = INDEX_HTML.getBytes(StandardCharsets.UTF_8);
            ex.getResponseHeaders().add("Content-Type", "text/html; charset=utf-8");
            ex.sendResponseHeaders(200, html.length);
            try (OutputStream out = ex.getResponseBody()) { out.write(html); }
        }
    }

    private static final class ExamplesHandler implements HttpHandler {
        @Override
        public void handle(HttpExchange ex) throws IOException {
            if (!"GET".equals(ex.getRequestMethod())) {
                respondText(ex, 405, "Method Not Allowed");
                return;
            }
            List<IPLExamplesProvider.Example> all = IPLExamplesProvider.getExamples();
            StringBuilder sb = new StringBuilder();
            sb.append("[");
            for (int i = 0; i < all.size(); i++) {
                IPLExamplesProvider.Example e = all.get(i);
                if (i > 0) sb.append(",");
                sb.append("{")
                  .append("\"name\":").append(IPLProofTreeExporter.jsonStr(e.name)).append(",")
                  .append("\"formula\":").append(IPLProofTreeExporter.jsonStr(e.formula)).append(",")
                  .append("\"validity\":").append(IPLProofTreeExporter.jsonStr(e.validity))
                  .append("}");
            }
            sb.append("]");
            byte[] body = sb.toString().getBytes(StandardCharsets.UTF_8);
            ex.getResponseHeaders().add("Content-Type", "application/json; charset=utf-8");
            ex.getResponseHeaders().add("Cache-Control", "public, max-age=60");
            ex.sendResponseHeaders(200, body.length);
            try (OutputStream out = ex.getResponseBody()) { out.write(body); }
        }
    }

    private static final class ProveHandler implements HttpHandler {
        @Override
        public void handle(HttpExchange ex) throws IOException {
            if (!"POST".equals(ex.getRequestMethod())) {
                respondText(ex, 405, "Method Not Allowed");
                return;
            }
            String body = readAll(ex.getRequestBody());
            String formula = extractJsonString(body, "formula");
            String name    = extractJsonString(body, "name");
            if (formula == null || formula.trim().isEmpty()) {
                respondJsonError(ex, 400, "Missing 'formula' field");
                return;
            }

            try {
                String html = runProveWithTimeout(formula.trim(),
                                                  (name != null && !name.isEmpty()) ? name : "Custom");
                respondHtmlCompressed(ex, html);
            } catch (TimeoutException te) {
                respondJsonError(ex, 504,
                        "Proof timed out after " + PROOF_TIMEOUT_SECONDS + " seconds. "
                      + "Try a smaller formula or increase the timeout.");
            } catch (Exception e) {
                Throwable cause = (e.getCause() != null) ? e.getCause() : e;
                System.err.println("[IPLWebServer] /api/prove failed for formula: " + formula);
                cause.printStackTrace();
                respondJsonError(ex, 500,
                        "Prove error (" + cause.getClass().getSimpleName() + "): "
                      + (cause.getMessage() != null ? cause.getMessage() : "unknown"));
            }
        }

        private static String runProveWithTimeout(String formula, String name) throws Exception {
            Future<String> future = PROVER_EXECUTOR.submit(() -> {
                synchronized (PROVER_LOCK) {
                    return runProveBlocking(formula, name);
                }
            });
            try {
                return future.get(PROOF_TIMEOUT_SECONDS, TimeUnit.SECONDS);
            } catch (TimeoutException te) {
                future.cancel(true);
                throw te;
            }
        }

        private static String runProveBlocking(String formula, String name) {
            SignedFormulaCreator creator = new SignedFormulaCreator("ipl");
            creator.setTwoPhases(false);
            IPLTracer.setEnabled(true);
            IPLTracer.getInstance().reset();

            Problem problem = creator.parseText(formula);
            problem.setName(name);

            Method method = new Method(
                    RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
            IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
            strategy.setComparator(new InsertionOrderSignedFormulaComparator());

            Prover prover = new Prover();
            prover.setMethod(method);
            prover.setStrategy(strategy);

            Proof proof = prover.prove(problem);
            return IPLHtmlExporter.generateHtml(proof, IPLTracer.getInstance());
        }
    }

    // ====================================================================
    //  Helpers
    // ====================================================================

    private static String readAll(InputStream in) throws IOException {
        try (in) {
            byte[] buf = new byte[8192];
            StringBuilder sb = new StringBuilder();
            int n;
            while ((n = in.read(buf)) > 0) {
                sb.append(new String(buf, 0, n, StandardCharsets.UTF_8));
            }
            return sb.toString();
        }
    }

    /**
     * Tiny ad-hoc extractor for {@code "key":"value"} pairs from a flat JSON
     * object. Avoids adding a JSON library dependency. Handles common
     * escape sequences; does not support nested objects or arrays as values
     * (which the prove endpoint never receives anyway).
     */
    private static String extractJsonString(String json, String key) {
        if (json == null) return null;
        String needle = "\"" + key + "\"";
        int i = json.indexOf(needle);
        if (i < 0) return null;
        i += needle.length();
        while (i < json.length() && Character.isWhitespace(json.charAt(i))) i++;
        if (i >= json.length() || json.charAt(i) != ':') return null;
        i++;
        while (i < json.length() && Character.isWhitespace(json.charAt(i))) i++;
        if (i >= json.length() || json.charAt(i) != '"') return null;
        i++;
        StringBuilder sb = new StringBuilder();
        while (i < json.length()) {
            char c = json.charAt(i);
            if (c == '\\' && i + 1 < json.length()) {
                char next = json.charAt(i + 1);
                switch (next) {
                    case 'n':  sb.append('\n'); break;
                    case 'r':  sb.append('\r'); break;
                    case 't':  sb.append('\t'); break;
                    case '"':  sb.append('"');  break;
                    case '\\': sb.append('\\'); break;
                    case '/':  sb.append('/');  break;
                    default:   sb.append(next);
                }
                i += 2;
            } else if (c == '"') {
                return sb.toString();
            } else {
                sb.append(c);
                i++;
            }
        }
        return sb.toString();
    }

    /**
     * Writes a UTF-8 HTML response, applying gzip compression when the client
     * advertised support via the {@code Accept-Encoding} header. Some IPL
     * proofs (notably Long PB) produce tens of megabytes of self-contained
     * HTML, so gzip is worth ~95% bandwidth savings on the wire.
     */
    private static void respondHtmlCompressed(HttpExchange ex, String html) throws IOException {
        byte[] htmlBytes = html.getBytes(StandardCharsets.UTF_8);
        String acceptEnc = ex.getRequestHeaders().getFirst("Accept-Encoding");
        boolean gzip = acceptEnc != null && acceptEnc.toLowerCase().contains("gzip");
        ex.getResponseHeaders().add("Content-Type", "text/html; charset=utf-8");
        if (gzip) {
            ex.getResponseHeaders().add("Content-Encoding", "gzip");
            // Length unknown ahead of compression; use chunked transfer.
            ex.sendResponseHeaders(200, 0);
            try (GZIPOutputStream out = new GZIPOutputStream(ex.getResponseBody())) {
                out.write(htmlBytes);
            }
        } else {
            ex.sendResponseHeaders(200, htmlBytes.length);
            try (OutputStream out = ex.getResponseBody()) { out.write(htmlBytes); }
        }
    }

    private static void respondText(HttpExchange ex, int status, String text) throws IOException {
        byte[] body = text.getBytes(StandardCharsets.UTF_8);
        ex.getResponseHeaders().add("Content-Type", "text/plain; charset=utf-8");
        ex.sendResponseHeaders(status, body.length);
        try (OutputStream out = ex.getResponseBody()) { out.write(body); }
    }

    private static void respondJsonError(HttpExchange ex, int status, String msg) throws IOException {
        String json = "{\"error\":" + IPLProofTreeExporter.jsonStr(msg) + "}";
        byte[] body = json.getBytes(StandardCharsets.UTF_8);
        ex.getResponseHeaders().add("Content-Type", "application/json; charset=utf-8");
        ex.sendResponseHeaders(status, body.length);
        try (OutputStream out = ex.getResponseBody()) { out.write(body); }
    }

    // ====================================================================
    //  Embedded landing page
    // ====================================================================

    // Single-page UI: preset dropdown + textarea + Solve button. On submit
    // we POST to /api/prove and inject the response HTML into an iframe so
    // the existing IPLHtmlExporter scripts run isolated from our shell.
    private static final String INDEX_HTML = ""
        + "<!doctype html>\n"
        + "<html lang=\"en\">\n"
        + "<head>\n"
        + "  <meta charset=\"utf-8\">\n"
        + "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        + "  <title>IPL KE-tableau Prover</title>\n"
        + "  <style>\n"
        + "    *, *::before, *::after { box-sizing: border-box; }\n"
        + "    body { font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\", Roboto, sans-serif;\n"
        + "           margin: 0; padding: 20px; background: #f7f8fa; color: #222; }\n"
        + "    header { margin-bottom: 16px; }\n"
        + "    h1 { margin: 0; font-size: 22px; letter-spacing: -0.01em; }\n"
        + "    .subtitle { color: #555; font-size: 13px; margin-top: 4px; max-width: 800px; line-height: 1.45; }\n"
        + "    .subtitle code { background: #eef0f3; padding: 1px 5px; border-radius: 4px; font-size: 12px; }\n"
        + "    .controls { background: #fff; border: 1px solid #e0e2e6; border-radius: 8px;\n"
        + "                padding: 16px 18px; box-shadow: 0 1px 2px rgba(0,0,0,0.04); margin-bottom: 16px; }\n"
        + "    label { display: block; font-size: 11px; font-weight: 700;\n"
        + "            text-transform: uppercase; color: #555; margin-bottom: 6px; letter-spacing: 0.6px; }\n"
        + "    select, textarea, button { font-family: inherit; font-size: 14px;\n"
        + "                               border: 1px solid #d0d3d8; border-radius: 6px; padding: 8px 10px;\n"
        + "                               background: #fff; outline: none; }\n"
        + "    select:focus, textarea:focus { border-color: #2563eb; box-shadow: 0 0 0 3px rgba(37,99,235,0.15); }\n"
        + "    select { width: 100%; max-width: 720px; }\n"
        + "    textarea { width: 100%; min-height: 70px; margin-top: 12px;\n"
        + "               font-family: ui-monospace, \"JetBrains Mono\", Menlo, Consolas, monospace;\n"
        + "               font-size: 13px; line-height: 1.5; }\n"
        + "    button { cursor: pointer; background: #2563eb; color: #fff; border-color: #2563eb;\n"
        + "             font-weight: 600; padding: 9px 22px; margin-top: 12px; }\n"
        + "    button:hover { background: #1d4ed8; }\n"
        + "    button:disabled { opacity: 0.55; cursor: wait; }\n"
        + "    .hint { font-size: 12px; color: #777; margin-top: 8px; line-height: 1.5; }\n"
        + "    .hint code { background: #eef0f3; padding: 1px 5px; border-radius: 4px; font-size: 11.5px; }\n"
        + "    .row { display: flex; gap: 14px; align-items: center; flex-wrap: wrap; }\n"
        + "    .status { font-size: 13px; min-height: 1.2em; }\n"
        + "    .status.error { color: #c2410c; }\n"
        + "    .status.ok    { color: #15803d; }\n"
        + "    .status.busy  { color: #555; }\n"
        + "    .iframe-wrap { background: #fff; border: 1px solid #e0e2e6; border-radius: 8px;\n"
        + "                   overflow: hidden; box-shadow: 0 1px 2px rgba(0,0,0,0.04); }\n"
        // No fixed height: the iframe is resized in JS to match its own content
        // height after each load, so the whole page scrolls naturally in one
        // place instead of trapping the proof view in a small box with its own
        // separate internal scrollbar.
        + "    #result { width: 100%; height: 300px; border: 0; display: block; }\n"
        + "    .placeholder { padding: 60px 40px; color: #888; font-style: italic;\n"
        + "                   text-align: center; }\n"
        + "  </style>\n"
        + "</head>\n"
        + "<body>\n"
        + "  <header>\n"
        + "    <h1>IPL KE-tableau Prover</h1>\n"
        + "    <div class=\"subtitle\">Pick a preset or write your own formula in the internal Polish notation"
        + "      (e.g. <code>F -&gt;(-(-A) A) c0</code>). Click <strong>Solve</strong> to run the prover and view"
        + "      the proof tree, rule instances and trace.</div>\n"
        + "  </header>\n"
        + "  <div class=\"controls\">\n"
        + "    <label for=\"example\">Preset example</label>\n"
        + "    <select id=\"example\">\n"
        + "      <option value=\"\">\u2014 Select an example \u2014</option>\n"
        + "    </select>\n"
        + "    <label for=\"formula\" style=\"margin-top:16px\">Formula</label>\n"
        + "    <textarea id=\"formula\" placeholder=\"F -&gt;(-(-A) A) c0\" spellcheck=\"false\"></textarea>\n"
        + "    <div class=\"row\">\n"
        + "      <button id=\"solve\">Solve</button>\n"
        + "      <span class=\"status\" id=\"status\"></span>\n"
        + "    </div>\n"
        + "    <div class=\"hint\">\n"
        + "      Connectives: <code>-X</code> = \u00acX, <code>*(X Y)</code> = X\u2227Y, <code>+(X Y)</code> = X\u2228Y,"
        + "      <code>-&gt;(X Y)</code> = X\u2192Y. Labels: <code>c0, c1, \u2026</code>."
        + "      Sign + formula + label, e.g. <code>F -&gt;(p q) c0</code>."
        + "      Multi-formula problems: one signed formula per line. Hint: Cmd/Ctrl+Enter submits.\n"
        + "    </div>\n"
        + "  </div>\n"
        + "  <div class=\"iframe-wrap\">\n"
        + "    <iframe id=\"result\" title=\"Proof viewer\"></iframe>\n"
        + "  </div>\n"
        + "  <script>\n"
        + "    const examplesSel = document.getElementById('example');\n"
        + "    const formulaEl   = document.getElementById('formula');\n"
        + "    const solveBtn    = document.getElementById('solve');\n"
        + "    const statusEl    = document.getElementById('status');\n"
        + "    const resultEl    = document.getElementById('result');\n"
        // The generated proof page has its own fixed-height panels (Proof Tree,
        // Kripke Context) that manage overflow internally via pan/zoom/scroll, so
        // its total document height is stable after load. Resize the iframe to
        // match it once per load so the OUTER page scrolls as a single surface,
        // instead of trapping the proof view in a small box with a separate
        // internal scrollbar a user would have to discover on their own.
        + "    resultEl.addEventListener('load', () => {\n"
        + "      try {\n"
        + "        const h = resultEl.contentDocument.documentElement.scrollHeight;\n"
        + "        if (h > 0) resultEl.style.height = h + 'px';\n"
        + "      } catch (e) {}\n"
        + "    });\n"
        + "    function setStatus(text, cls) { statusEl.textContent = text; statusEl.className = 'status ' + (cls||''); }\n"
        + "    function showPlaceholder(text) {\n"
        + "      resultEl.srcdoc = '<div class=\"placeholder\" style=\"font-family:sans-serif;padding:60px 40px;color:#888;font-style:italic;text-align:center\">' + text + '</div>';\n"
        + "    }\n"
        + "    showPlaceholder('Pick an example or type a formula above, then click <b>Solve</b>.');\n"
        + "    fetch('/api/examples').then(r => r.json()).then(list => {\n"
        + "      for (const ex of list) {\n"
        + "        const opt = document.createElement('option');\n"
        + "        opt.value = ex.formula;\n"
        + "        opt.dataset.name = ex.name;\n"
        + "        opt.dataset.validity = ex.validity;\n"
        + "        opt.textContent = ex.name + '  \u2014  ' + ex.validity;\n"
        + "        examplesSel.appendChild(opt);\n"
        + "      }\n"
        + "    }).catch(err => setStatus('Failed to load presets: ' + err.message, 'error'));\n"
        + "    examplesSel.addEventListener('change', () => {\n"
        + "      if (examplesSel.value) { formulaEl.value = examplesSel.value; setStatus('', ''); }\n"
        + "    });\n"
        + "    async function solve() {\n"
        + "      const formula = formulaEl.value.trim();\n"
        + "      if (!formula) { setStatus('Please enter a formula or pick a preset.', 'error'); return; }\n"
        + "      const opt  = examplesSel.selectedOptions[0];\n"
        + "      const name = (opt && opt.dataset.name && formula === opt.value) ? opt.dataset.name : 'Custom';\n"
        + "      solveBtn.disabled = true;\n"
        + "      setStatus('Running prover\u2026', 'busy');\n"
        + "      const t0 = performance.now();\n"
        + "      try {\n"
        + "        const resp = await fetch('/api/prove', {\n"
        + "          method: 'POST',\n"
        + "          headers: { 'Content-Type': 'application/json' },\n"
        + "          body: JSON.stringify({ formula, name })\n"
        + "        });\n"
        + "        if (!resp.ok) {\n"
        + "          let msg = 'HTTP ' + resp.status;\n"
        + "          try { const j = await resp.json(); if (j.error) msg = j.error; } catch (e) {}\n"
        + "          throw new Error(msg);\n"
        + "        }\n"
        + "        const html = await resp.text();\n"
        + "        resultEl.srcdoc = html;\n"
        + "        const elapsed = ((performance.now() - t0) / 1000).toFixed(2);\n"
        + "        setStatus('Done in ' + elapsed + 's.', 'ok');\n"
        + "      } catch (err) {\n"
        + "        setStatus('Error: ' + err.message, 'error');\n"
        + "      } finally {\n"
        + "        solveBtn.disabled = false;\n"
        + "      }\n"
        + "    }\n"
        + "    solveBtn.addEventListener('click', solve);\n"
        + "    formulaEl.addEventListener('keydown', e => {\n"
        + "      if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) { e.preventDefault(); solve(); }\n"
        + "    });\n"
        + "  </script>\n"
        + "</body>\n"
        + "</html>\n";

    private IPLWebServer() {}
}
