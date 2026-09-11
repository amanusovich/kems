# IPL KE-tableau Web Server

A minimal HTTP server that exposes the IPL prover over the web. Built so
co-authors and reviewers can try the prover without checking out the repo or
running IntelliJ.

## What it serves

| Method | Path             | What it does                                             |
| ------ | ---------------- | -------------------------------------------------------- |
| `GET`  | `/`              | Single-page UI (preset dropdown, textarea, "Solve" button, iframe for the proof). |
| `GET`  | `/api/examples`  | JSON list of the 11 IPL formula presets from `IPLExamplesProvider`. |
| `POST` | `/api/prove`     | Body `{"formula":"…","name":"…"}`. Runs `IPLSimpleStrategy`, returns the full self-contained HTML produced by `IPLHtmlExporter`. Gzip-encoded when the client advertises it (~28× smaller for Long PB). |

The formula uses the same internal Polish notation accepted by
`SignedFormulaCreator`:

```
F ->(*(->(A B) ->(A -B)) -A) c0      # Paper 1
F ->(->(->(p q) p) p) c0             # Peirce (not valid in IPL)
```

## Run locally

### Option A — IntelliJ

1. Open the existing IntelliJ project.
2. Right-click `proverinterface.webserver.IPLWebServer` → **Run 'IPLWebServer.main()'**.
3. The first run will create a Run Configuration; open it and (optionally)
   set `PORT=8080` under Environment Variables.
4. Server prints `[IPLWebServer] listening on http://0.0.0.0:8080`.
5. Browse to <http://localhost:8080>.

The Swing GUI keeps working in parallel — they share the same prover code and
the same preset list (via `IPLExamplesProvider`).

### Option B — Docker

From the repo root:

```bash
docker build -t kems-ipl .
docker run --rm -p 8080:8080 kems-ipl
```

The Dockerfile is multi-stage: a JDK image compiles every `.java` in
`kems.prover/src` with `javac`, then the runtime image only carries the
classes plus the bundled jars (Alpine JRE, ~250 MB).

## Deploy to Fly.io

The repo includes a `fly.toml` ready for a free-tier deploy. One-time setup:

```bash
brew install flyctl
flyctl auth signup            # or `flyctl auth login`
flyctl launch --no-deploy     # if you want to override defaults; else skip
flyctl deploy
```

After deploy, the app is reachable at <https://kems-ipl.fly.dev> (or whatever
name you picked). Auto-stop is on, so the machine sleeps when idle and
cold-starts on the next request (~3 s). Bump `vm.memory` in `fly.toml` to
`1gb` if Long PB / Scott axiom run out of memory.

## Implementation notes

- **No new runtime dependency.** The server uses
  `com.sun.net.httpserver.HttpServer` from the JDK; the only third-party jar
  added is `jdom2`, which the existing prover already requires (the Dockerfile
  fetches it from Maven Central; locally IntelliJ provides it).
- **Concurrency.** `IPLTracer` is a process-wide singleton, so the prove
  endpoint serializes work through a single-thread executor under a global
  lock. A per-request refactor is tracked separately.
- **Timeout.** Each `/api/prove` request is given 5 minutes. After that the
  worker future is cancelled and the client gets HTTP 504. The cancelled
  thread may keep computing briefly — restart the server if Long PB / Scott
  leak.
- **Gzip.** Proofs that produce huge HTML (Long PB ≈ 49 MB raw) are gzip-encoded
  on the wire when `Accept-Encoding: gzip` is present. Compression ratio is
  about 28× because the JSON-in-HTML payload is highly repetitive.

## What it does not do (yet)

- Per-request tracer / context isolation (so we can drop the global lock).
- Animation of the proof tree as it grows (planned for the React frontend
  in Phase C).
- Saving / linking individual proofs (`/proofs/<id>` permalinks).
- Auth, rate-limiting.
