package proverinterface.proofviewer;

import java.awt.Color;

/**
 * Color scheme for IPL rule types in proof visualization.
 * Provides consistent colors across the Swing viewer and HTML exporter.
 */
public class IPLColorScheme {

    public static final Color ONE_PREMISE = new Color(0, 100, 0);        // dark green
    public static final Color TWO_PREMISE = new Color(0, 0, 160);        // dark blue
    public static final Color PB          = new Color(180, 100, 0);      // orange
    public static final Color CLOSURE     = new Color(200, 0, 0);        // red
    public static final Color PROPAGATION = new Color(128, 0, 128);      // purple
    public static final Color PROBLEM     = Color.BLACK;                 // black
    public static final Color DEFAULT     = Color.DARK_GRAY;

    public static Color getColor(String ruleName) {
        if (ruleName == null) return DEFAULT;
        String r = ruleName.toUpperCase();
        if (r.contains("CLOSE"))        return CLOSURE;
        if (r.contains("PB"))           return PB;
        if (r.contains("PROPAGAT"))     return PROPAGATION;
        if (r.contains("PROBLEM") || r.contains("DEFINITION")) return PROBLEM;
        if (isTwoPremise(r))            return TWO_PREMISE;
        if (isOnePremise(r))            return ONE_PREMISE;
        return DEFAULT;
    }

    public static String getCssClass(String ruleName) {
        if (ruleName == null) return "default";
        String r = ruleName.toUpperCase();
        if (r.contains("CLOSE"))        return "closure";
        if (r.contains("PB"))           return "pb";
        if (r.contains("PROPAGAT"))     return "propagation";
        if (r.contains("PROBLEM") || r.contains("DEFINITION")) return "problem";
        if (isTwoPremise(r))            return "two-premise";
        if (isOnePremise(r))            return "one-premise";
        return "default";
    }

    /** Returns a category string suitable for the JSON export and D3 coloring. */
    public static String getRuleCategory(String ruleName) {
        if (ruleName == null) return "default";
        String r = ruleName.toUpperCase();
        if (r.contains("CLOSE"))        return "CLOSURE";
        if (r.contains("PB"))           return "PB";
        if (r.contains("PROPAGAT"))     return "PROPAGATION";
        if (isTwoPremise(r))            return "TWO_PREMISE";
        if (isOnePremise(r))            return "ONE_PREMISE";
        return "default";
    }

    private static boolean isOnePremise(String r) {
        return r.contains("T_AND") || r.contains("F_OR")
            || r.contains("T_NOT") || r.contains("F_NOT")
            || r.contains("F_A_IMPLIES_B");
    }

    private static boolean isTwoPremise(String r) {
        return r.contains("T_OR_F") || r.contains("F_AND")
            || r.contains("T_IMPLIES") || r.contains("X_IMPLIES")
            || r.contains("F_IMPLIES_T");
    }
}
