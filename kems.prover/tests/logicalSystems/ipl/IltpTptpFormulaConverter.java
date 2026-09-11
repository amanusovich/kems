package logicalSystems.ipl;

/**
 * Converts ILTP / TPTP propositional FOF bodies (parenthesised infix with
 * {@code ~}, {@code &}, {@code |}, {@code =>}, {@code <=>}) into the KEMS IPL
 * text syntax used by {@link logic.signedFormulas.SignedFormulaCreator}:
 * {@code -} (not), {@code *} (and), {@code +} (or), {@code ->} (implies),
 * atoms as given ({@code p}, {@code p1}, …).
 */
final class IltpTptpFormulaConverter {

    private final String s;
    private int pos;

    private IltpTptpFormulaConverter(String input) {
        this.s = input.replaceAll("\\s+", " ").trim();
        this.pos = 0;
    }

    /**
     * Converts the inner part of a TPTP {@code fof(...,( ... ))} formula (may
     * include outer parentheses).
     */
    static String toKemsIpl(String tptpBody) {
        String t = tptpBody.replaceAll("\\s+", " ").trim();
        if (t.startsWith("(") && t.endsWith(")")) {
            t = stripMatchingOuterParens(t);
        }
        return new IltpTptpFormulaConverter(t).parseEquiv();
    }

    private static String stripMatchingOuterParens(String t) {
        int depth = 0;
        for (int i = 0; i < t.length(); i++) {
            char c = t.charAt(i);
            if (c == '(') depth++;
            else if (c == ')') {
                depth--;
                if (depth == 0 && i < t.length() - 1) {
                    return t;
                }
            }
        }
        if (t.startsWith("(") && t.endsWith(")") && depth == 0) {
            return t.substring(1, t.length() - 1).trim();
        }
        return t;
    }

    private void skipSpaces() {
        while (pos < s.length() && s.charAt(pos) == ' ') pos++;
    }

    private String parseEquiv() {
        String left = parseImply();
        skipSpaces();
        if (match("<=>")) {
            String right = parseEquiv();
            return "*(->(" + left + " " + right + ")(->(" + right + " " + left + ")))";
        }
        return left;
    }

    private String parseImply() {
        String left = parseOr();
        skipSpaces();
        if (match("=>")) {
            String right = parseImply();
            return "->(" + left + " " + right + ")";
        }
        return left;
    }

    private String parseOr() {
        String left = parseAnd();
        skipSpaces();
        if (match("|")) {
            String right = parseOr();
            return "+(" + left + " " + right + ")";
        }
        return left;
    }

    private String parseAnd() {
        String left = parseUnary();
        skipSpaces();
        if (match("&")) {
            String right = parseAnd();
            return "*(" + left + " " + right + ")";
        }
        return left;
    }

    private String parseUnary() {
        skipSpaces();
        if (match("~")) {
            return "-(" + parseUnary() + ")";
        }
        return parsePrimary();
    }

    private String parsePrimary() {
        skipSpaces();
        if (match("(")) {
            String inner = parseEquiv();
            skipSpaces();
            if (!match(")")) {
                throw new IllegalArgumentException("Expected ')' at " + pos + " in: " + s);
            }
            return inner;
        }
        return parseAtom();
    }

    private String parseAtom() {
        skipSpaces();
        int start = pos;
        while (pos < s.length()) {
            char c = s.charAt(pos);
            if (Character.isLetterOrDigit(c) || c == '_') pos++;
            else break;
        }
        if (start == pos) {
            throw new IllegalArgumentException("Expected atom at " + pos + " in: " + s);
        }
        return s.substring(start, pos);
    }

    private boolean match(String token) {
        skipSpaces();
        if (s.regionMatches(pos, token, 0, token.length())) {
            pos += token.length();
            return true;
        }
        return false;
    }
}
