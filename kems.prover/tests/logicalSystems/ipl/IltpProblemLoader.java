package logicalSystems.ipl;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Loads a minimal subset of ILTP v1.1.2 propositional {@code .p} files: one or
 * more {@code fof(name,axiom|conjecture,( ... ))} entries with a single
 * parenthesised formula in the last argument.
 */
final class IltpProblemLoader {

    static final class FofEntry {
        final String name;
        /** {@code "axiom"} or {@code "conjecture"} (lower case). */
        final String role;
        /** Raw TPTP body inside the outermost {@code (...)} of the third argument. */
        final String tptpBody;

        FofEntry(String name, String role, String tptpBody) {
            this.name = name;
            this.role = role;
            this.tptpBody = tptpBody;
        }
    }

    private static final Pattern FOF_HEAD = Pattern.compile(
            "fof\\(\\s*([^,]+)\\s*,\\s*(axiom|conjecture)\\s*,",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);

    static List<FofEntry> load(Path path) throws IOException {
        String text = new String(Files.readAllBytes(path), StandardCharsets.UTF_8);
        List<FofEntry> out = new ArrayList<>();
        Matcher m = FOF_HEAD.matcher(text);
        while (m.find()) {
            String name = m.group(1).trim();
            String role = m.group(2).trim().toLowerCase(Locale.ROOT);
            int startExpr = m.end();
            int open = text.indexOf('(', startExpr);
            if (open < 0) {
                throw new IOException("Malformed fof after header in " + path);
            }
            int end = indexOfMatchingClose(text, open);
            if (end < 0) {
                throw new IOException("Unbalanced parens in " + path);
            }
            String body = text.substring(open + 1, end).trim();
            out.add(new FofEntry(name, role, body));
        }
        return out;
    }

    private static int indexOfMatchingClose(String text, int openParenIndex) {
        int depth = 0;
        for (int i = openParenIndex; i < text.length(); i++) {
            char c = text.charAt(i);
            if (c == '(') depth++;
            else if (c == ')') {
                depth--;
                if (depth == 0) return i;
            }
        }
        return -1;
    }
}
