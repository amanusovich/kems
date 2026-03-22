package main.newstrategy.ipl;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

/**
 * Structured trace system for the IPL KE-tableau prover.
 * Captures proof steps as TraceEvent records and supports both
 * human-readable text output and JSON export.
 *
 * Toggle via {@link #setEnabled(boolean)}. Off by default for performance.
 *
 * Paper reference: Algorithm 1 - Canonical procedure (S5, p.16).
 */
public class IPLTracer {

    // -- Event types -------------------------------------------------------

    public enum EventType {
        ALGORITHM_START,
        ALGORITHM_END,
        BRANCH_START,
        BRANCH_COMPLETED,
        FORMULA_SELECTED,
        RULE_APPLIED,
        RULE_BLOCKED,
        PB_APPLIED,
        PB_SKIPPED,
        PROPAGATION,
        CLOSURE,
        RINSTANCE_REGISTERED,
        LABEL_REGISTERED,
        INFO
    }

    // -- TraceEvent record --------------------------------------------------

    public static class TraceEvent {
        private final int step;
        private final EventType type;
        private final String branchId;
        private final String message;
        private final String detail;
        private final long timestampMs;

        public TraceEvent(int step, EventType type, String branchId,
                          String message, String detail) {
            this.step = step;
            this.type = type;
            this.branchId = branchId;
            this.message = message;
            this.detail = detail;
            this.timestampMs = System.currentTimeMillis();
        }

        public int getStep()         { return step; }
        public EventType getType()   { return type; }
        public String getBranchId()  { return branchId; }
        public String getMessage()   { return message; }
        public String getDetail()    { return detail; }
        public long getTimestampMs() { return timestampMs; }
    }

    // -- Singleton / global state --------------------------------------------

    private static boolean enabled = false;
    private static final IPLTracer INSTANCE = new IPLTracer();

    private final List<TraceEvent> events = new ArrayList<>();
    private int stepCounter = 0;
    private String currentBranch = "root";

    private IPLTracer() {}

    public static IPLTracer getInstance() { return INSTANCE; }

    public static boolean isEnabled() { return enabled; }

    public static void setEnabled(boolean on) { enabled = on; }

    // -- Reset (call before each new proof) ----------------------------------

    public void reset() {
        events.clear();
        stepCounter = 0;
        currentBranch = "root";
    }

    // -- Branch tracking -----------------------------------------------------

    public void setCurrentBranch(String branchId) {
        this.currentBranch = branchId;
    }

    public String getCurrentBranch() { return currentBranch; }

    // -- Logging helpers -----------------------------------------------------

    private int nextStep() { return ++stepCounter; }

    private void record(EventType type, String message, String detail) {
        if (!enabled) return;
        events.add(new TraceEvent(nextStep(), type, currentBranch, message, detail));
    }

    private void recordNoStep(EventType type, String message, String detail) {
        if (!enabled) return;
        events.add(new TraceEvent(stepCounter, type, currentBranch, message, detail));
    }

    // -- Public logging API --------------------------------------------------

    public void logAlgorithmStart() {
        record(EventType.ALGORITHM_START, "IPL Canonical Algorithm: Starting execution", null);
    }

    public void logAlgorithmEnd(boolean closed) {
        record(EventType.ALGORITHM_END,
               "IPL Canonical Algorithm: Execution complete",
               closed ? "CLOSED" : "OPEN");
    }

    public void logBranchStart(String branchId) {
        setCurrentBranch(branchId);
        record(EventType.BRANCH_START, "Processing branch: " + branchId, null);
    }

    public void logBranchCompleted(String branchId, boolean closed) {
        record(EventType.BRANCH_COMPLETED,
               "Branch " + branchId + (closed ? " CLOSED" : " completed (open)"),
               null);
    }

    public void logFormulaSelected(String formula, String reason) {
        record(EventType.FORMULA_SELECTED, "SELECT " + formula, reason);
    }

    public void logRuleApplied(String ruleName, String premise, String conclusion) {
        record(EventType.RULE_APPLIED,
               "APPLY " + ruleName,
               "Premise: " + premise + " -> Conclusion: " + conclusion);
    }

    public void logRuleApplied(String ruleName, String mainPremise,
                               String auxPremise, String conclusion) {
        record(EventType.RULE_APPLIED,
               "APPLY " + ruleName,
               "Main: " + mainPremise + ", Aux: " + auxPremise +
               " -> Conclusion: " + conclusion);
    }

    public void logRuleBlocked(String ruleName, String formula, String reason) {
        record(EventType.RULE_BLOCKED,
               "BLOCKED " + ruleName + " on " + formula,
               reason);
    }

    public void logPBApplied(String mainPremise, String rule,
                             String auxGenerated, String leftBranch, String rightBranch) {
        record(EventType.PB_APPLIED,
               "PB for " + rule,
               "Main: " + mainPremise + " | Left: " + auxGenerated +
               " | Right: opposite | Branches: L=" + leftBranch + ", R=" + rightBranch);
    }

    public void logPBSkipped(String formula, String reason) {
        record(EventType.PB_SKIPPED,
               "PB skipped for " + formula,
               reason);
    }

    public void logPropagation(String formula, String fromLabel, String toLabel) {
        record(EventType.PROPAGATION,
               "PROPAGATE " + formula,
               fromLabel + " -> " + toLabel);
    }

    public void logClosure(String tFormula, String fFormula, String labelRelation) {
        record(EventType.CLOSURE,
               "CLOSURE",
               "T " + tFormula + ", F " + fFormula + " (" + labelRelation + ")");
    }

    public void logRinstanceRegistered(String ruleInstance) {
        recordNoStep(EventType.RINSTANCE_REGISTERED,
                     "rinstance: " + ruleInstance, null);
    }

    public void logLabelRegistered(String label, String branchId) {
        recordNoStep(EventType.LABEL_REGISTERED,
                     "Label " + label + " registered in branch " + branchId, null);
    }

    public void logInfo(String message) {
        recordNoStep(EventType.INFO, message, null);
    }

    // -- Text formatter ------------------------------------------------------

    public String formatText() {
        StringBuilder sb = new StringBuilder();
        sb.append("=== IPL Proof Trace ===\n\n");
        for (TraceEvent e : events) {
            formatEvent(sb, e);
        }
        sb.append("\n=== End of Trace (").append(events.size()).append(" events) ===\n");
        return sb.toString();
    }

    private void formatEvent(StringBuilder sb, TraceEvent e) {
        String prefix = "[" + e.getBranchId() + "] ";
        switch (e.getType()) {
            case ALGORITHM_START:
                sb.append("\n").append(prefix).append("Step ").append(e.getStep()).append(": ")
                  .append(e.getMessage()).append("\n");
                break;
            case ALGORITHM_END:
                sb.append("\n").append(prefix).append("Step ").append(e.getStep()).append(": ")
                  .append(e.getMessage()).append("\n");
                if (e.getDetail() != null) sb.append(prefix).append("  Result: ").append(e.getDetail()).append("\n");
                break;
            case BRANCH_START:
                sb.append("\n").append(prefix).append("Step ").append(e.getStep()).append(": --- ")
                  .append(e.getMessage()).append(" ---\n");
                break;
            case BRANCH_COMPLETED:
                sb.append(prefix).append("Step ").append(e.getStep()).append(": ")
                  .append(e.getMessage()).append("\n");
                break;
            case FORMULA_SELECTED:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  (").append(e.getDetail()).append(")\n");
                }
                break;
            case RULE_APPLIED:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  ").append(e.getDetail()).append("\n");
                }
                break;
            case RULE_BLOCKED:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  Reason: ").append(e.getDetail()).append("\n");
                }
                break;
            case PB_APPLIED:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  ").append(e.getDetail()).append("\n");
                }
                break;
            case PB_SKIPPED:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  Reason: ").append(e.getDetail()).append("\n");
                }
                break;
            case PROPAGATION:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  ").append(e.getDetail()).append("\n");
                }
                break;
            case CLOSURE:
                sb.append(prefix).append("Step ").append(e.getStep())
                  .append(": ").append(e.getMessage()).append("\n");
                if (e.getDetail() != null) {
                    sb.append(prefix).append("  ").append(e.getDetail()).append("\n");
                }
                break;
            case RINSTANCE_REGISTERED:
            case LABEL_REGISTERED:
                sb.append(prefix).append("       ").append(e.getMessage()).append("\n");
                break;
            case INFO:
                sb.append(prefix).append("       ").append(e.getMessage()).append("\n");
                break;
        }
    }

    // -- JSON exporter -------------------------------------------------------

    public String formatJSON() {
        StringBuilder sb = new StringBuilder();
        sb.append("{\n  \"events\": [\n");
        for (int i = 0; i < events.size(); i++) {
            TraceEvent e = events.get(i);
            sb.append("    {\n");
            sb.append("      \"step\": ").append(e.getStep()).append(",\n");
            sb.append("      \"type\": \"").append(e.getType()).append("\",\n");
            sb.append("      \"branch\": \"").append(escapeJson(e.getBranchId())).append("\",\n");
            sb.append("      \"message\": \"").append(escapeJson(e.getMessage())).append("\"");
            if (e.getDetail() != null) {
                sb.append(",\n      \"detail\": \"").append(escapeJson(e.getDetail())).append("\"");
            }
            sb.append(",\n      \"timestamp\": ").append(e.getTimestampMs());
            sb.append("\n    }");
            if (i < events.size() - 1) sb.append(",");
            sb.append("\n");
        }
        sb.append("  ]\n}\n");
        return sb.toString();
    }

    private static String escapeJson(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\t", "\\t");
    }

    // -- File output ---------------------------------------------------------

    public void writeTextTo(String path) throws IOException {
        try (PrintWriter pw = new PrintWriter(new FileWriter(path))) {
            pw.print(formatText());
        }
    }

    public void writeJsonTo(String path) throws IOException {
        try (PrintWriter pw = new PrintWriter(new FileWriter(path))) {
            pw.print(formatJSON());
        }
    }

    // -- Access to raw events (for HTML exporter, GUI, etc.) ----------------

    public List<TraceEvent> getEvents() {
        return new ArrayList<>(events);
    }

    public int getEventCount() { return events.size(); }
}
