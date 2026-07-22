package proverinterface.proofviewer;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import main.newstrategy.ipl.IPLTracer;
import main.tableau.IProof;

/**
 * Generates a self-contained interactive HTML file from an IPL proof.
 *
 * The HTML embeds:
 *  - Full proof data as PROOF_DATA JSON (via IPLProofTreeExporter)
 *  - D3.js v7 loaded from CDN (with offline-embedding instructions in comments)
 *  - Two-column layout: proof tree (D3 tree) on the left, detail panel on the right
 *  - Kripke context DAG (D3 force simulation) at the top right
 *  - Click any node to see its rinstances and formula details
 *  - Collapsible trace section at the bottom
 */
public class IPLHtmlExporter {

    public static void export(IProof proof, String outputPath) throws IOException {
        export(proof, outputPath, null);
    }

    public static void export(IProof proof, String outputPath, IPLTracer tracer) throws IOException {
        try (PrintWriter pw = new PrintWriter(new FileWriter(outputPath))) {
            pw.println(generateHtml(proof, tracer));
        }
    }

    public static String generateHtml(IProof proof, IPLTracer tracer) {
        String proofJson = IPLProofTreeExporter.toJson(proof, tracer);
        String title = (proof.getProblem() != null && proof.getProblem().getName() != null)
                ? proof.getProblem().getName() : "IPL Proof";

        StringBuilder sb = new StringBuilder();
        sb.append("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
        sb.append("<meta charset=\"UTF-8\">\n");
        sb.append("<title>IPL Proof: ").append(esc(title)).append("</title>\n");
        appendStyles(sb);
        sb.append("</head>\n<body>\n");
        sb.append("<h1>IPL Proof: ").append(esc(title)).append("</h1>\n");

        // Embed proof data
        sb.append("<script>\n");
        sb.append("// To use offline: download d3.v7.min.js and replace the CDN script tag below.\n");
        sb.append("const PROOF_DATA = ");
        sb.append(proofJson);
        sb.append(";\n</script>\n");

        // Main layout -- Proof Tree keeps its own dedicated vertical space; Kripke
        // Context (below) does not compete with it for height.
        sb.append("<div id=\"main-layout\">\n");
        sb.append("  <div id=\"left-pane\">\n");
        sb.append("    <h2><span>Proof Tree "
                + "<span id=\"tree-stats\" style=\"font-size:0.78em;font-weight:normal;color:#5c6bc0\"></span></span>"
                + "<span id=\"proof-status\"></span></h2>\n");
        sb.append("    <div id=\"tree-toolbar\">\n");
        sb.append("      <button id=\"btn-fit\" title=\"Zoom to fit entire tree\">Fit</button>\n");
        sb.append("      <button id=\"btn-zoom-in\" title=\"Zoom in\">+</button>\n");
        sb.append("      <button id=\"btn-zoom-out\" title=\"Zoom out\">&minus;</button>\n");
        sb.append("      <button id=\"btn-expand-all\" title=\"Expand all branches\">Expand all</button>\n");
        sb.append("      <button id=\"btn-collapse-all\" title=\"Collapse all sub-branches\">Collapse all</button>\n");
        sb.append("      <span style=\"font-size:0.78em;color:#666;margin-left:6px\">Scroll/pinch to zoom &bull; drag to pan &bull; click &#9654;/&#9660; to collapse</span>\n");
        sb.append("    </div>\n");
        sb.append("    <div id=\"tree-container\"><svg id=\"tree-svg\"></svg></div>\n");
        sb.append("  </div>\n");
        sb.append("  <div id=\"right-pane\">\n");
        sb.append("    <div id=\"detail-pane\">\n");
        sb.append("      <h2>Node Detail</h2>\n");
        sb.append("      <p id=\"detail-hint\" style=\"color:#888;font-style:italic\">Click a node in the proof tree to see details.</p>\n");
        sb.append("      <div id=\"detail-content\" style=\"display:none\">\n");
        sb.append("        <div class=\"detail-section\">\n");
        sb.append("          <h3>Formula</h3>\n");
        sb.append("          <div id=\"detail-formula\"></div>\n");
        sb.append("        </div>\n");
        sb.append("        <div class=\"detail-section\">\n");
        sb.append("          <h3>rinstances <span class=\"info-icon\" title=\"Rule instances that block re-application on this branch path (includes ancestor branches)\">?</span></h3>\n");
        sb.append("          <ul id=\"detail-rinstances\"></ul>\n");
        sb.append("        </div>\n");
        sb.append("      </div>\n");
        sb.append("    </div>\n");
        sb.append("  </div>\n");
        sb.append("</div>\n");

        // Kripke context -- below the Proof Tree, always full page width and with
        // generous vertical space of its own (doesn't shrink Proof Tree or any
        // other pane). Wide levels (many sibling states, common in PB-heavy
        // proofs) have room to lay out before needing to scroll.
        sb.append("<div id=\"kripke-pane\">\n");
        sb.append("  <h2>Kripke Context</h2>\n");
        sb.append("  <div id=\"kripke-container\"><svg id=\"kripke-svg\"></svg></div>\n");
        sb.append("</div>\n");

        // Legend
        sb.append("<div id=\"legend\">\n");
        sb.append("  <span class=\"legend-item\"><span class=\"dot problem\"></span>Problem</span>\n");
        sb.append("  <span class=\"legend-item\"><span class=\"dot one-premise\"></span>1-premise</span>\n");
        sb.append("  <span class=\"legend-item\"><span class=\"dot two-premise\"></span>2-premise</span>\n");
        sb.append("  <span class=\"legend-item\"><span class=\"dot pb\"></span>PB</span>\n");
        sb.append("  <span class=\"legend-item\"><span class=\"dot closure\"></span>Closure</span>\n");
        sb.append("</div>\n");

        // Trace section
        sb.append("<div id=\"trace-section\">\n");
        sb.append("  <details>\n");
        sb.append("    <summary><strong>Proof Trace</strong></summary>\n");
        sb.append("    <div id=\"trace-content\"></div>\n");
        sb.append("  </details>\n");
        sb.append("</div>\n");

        // D3 script
        sb.append("<script src=\"https://d3js.org/d3.v7.min.js\"></script>\n");
        appendD3Script(sb);

        sb.append("</body>\n</html>\n");
        return sb.toString();
    }

    // -------------------------------------------------------------------------
    // CSS styles
    // -------------------------------------------------------------------------

    private static void appendStyles(StringBuilder sb) {
        sb.append("<style>\n");
        sb.append("* { box-sizing: border-box; margin: 0; padding: 0; }\n");
        sb.append("body { font-family: 'Segoe UI', Arial, sans-serif; font-size: 14px; background: #f5f5f5; color: #222; }\n");
        sb.append("h1 { padding: 14px 20px; background: #1a237e; color: #fff; font-size: 1.3em; }\n");
        sb.append("h2 { font-size: 1em; padding: 6px 10px; background: #e8eaf6; border-bottom: 1px solid #c5cae9; color: #1a237e; display:flex; align-items:center; justify-content:space-between; }\n");
        sb.append("h3 { font-size: 0.9em; margin: 8px 0 4px; color: #333; }\n");
        sb.append("#main-layout { display: flex; height: 600px; }\n");
        sb.append("#left-pane { flex: 3; display: flex; flex-direction: column; border-right: 2px solid #c5cae9; background: #fff; overflow: hidden; }\n");
        sb.append("#tree-toolbar { display:flex; gap:6px; padding:4px 8px; background:#f0f4ff; border-bottom:1px solid #c5cae9; flex-shrink:0; }\n");
        sb.append("#tree-toolbar button { font-size:0.8em; padding:2px 8px; cursor:pointer; border:1px solid #9fa8da; border-radius:3px; background:#fff; color:#1a237e; }\n");
        sb.append("#tree-toolbar button:hover { background:#e8eaf6; }\n");
        sb.append("#tree-container { flex: 1; overflow: hidden; position: relative; cursor: grab; }\n");
        sb.append("#tree-container:active { cursor: grabbing; }\n");
        sb.append("#tree-svg { display: block; width: 100%; height: 100%; }\n");
        sb.append("#right-pane { flex: 1; min-width: 280px; max-width: 400px; display: flex; flex-direction: column; background: #fff; }\n");
        sb.append("#detail-pane { flex: 1; overflow-y: auto; padding: 10px; }\n");
        sb.append(".detail-section { margin-bottom: 12px; }\n");
        sb.append(".detail-section ul { list-style: none; padding-left: 8px; }\n");
        sb.append(".detail-section ul li { padding: 2px 0; border-bottom: 1px solid #eee; font-size: 0.85em; font-family: monospace; }\n");
        sb.append("#kripke-pane { border-top: 2px solid #c5cae9; border-bottom: 2px solid #c5cae9; background: #fff; }\n");
        sb.append("#kripke-container { height: 420px; overflow-x: auto; overflow-y: hidden; }\n");
        sb.append("#kripke-svg { display: block; height: 420px; }\n");
        sb.append("#legend { display: flex; gap: 14px; padding: 5px 16px; background: #ede7f6; font-size: 0.82em; flex-wrap: wrap; }\n");
        sb.append(".legend-item { display: flex; align-items: center; gap: 5px; }\n");
        sb.append(".dot { display: inline-block; width: 11px; height: 11px; border-radius: 50%; border: 1px solid #999; }\n");
        sb.append(".dot.problem { background: #555; }\n");
        sb.append(".dot.one-premise { background: #1b5e20; }\n");
        sb.append(".dot.two-premise { background: #0d47a1; }\n");
        sb.append(".dot.pb { background: #e65100; }\n");
        sb.append(".dot.closure { background: #b71c1c; }\n");
        sb.append("#trace-section { padding: 8px 20px; background: #fafafa; border-top: 1px solid #ddd; }\n");
        sb.append("#trace-section details { max-height: 200px; overflow-y: auto; }\n");
        sb.append("#trace-content { font-family: monospace; font-size: 0.82em; white-space: pre-wrap; background: #f8f8f8; padding: 10px; border: 1px solid #ddd; margin-top: 6px; }\n");
        sb.append("#detail-formula { font-family: monospace; font-size: 0.88em; padding: 6px; background: #f0f0f0; border-radius: 4px; line-height: 1.5; }\n");
        sb.append(".info-icon { cursor: help; color: #888; font-size: 0.85em; border: 1px solid #ccc; border-radius: 50%; padding: 0 4px; }\n");
        sb.append(".node text { font-family: monospace; }\n");
        sb.append(".branch-box { cursor: pointer; }\n");
        sb.append(".branch-box.selected { stroke-width: 3px !important; filter: drop-shadow(0 0 4px rgba(0,0,0,0.3)); }\n");
        // Formula rows: invisible rect captures pointer events across the whole row.
        // Hover lights the background; the row text stays click-through so the rect handles it.
        sb.append(".formula-row { cursor: pointer; }\n");
        sb.append(".formula-row .formula-row-bg { fill: transparent; transition: fill 80ms ease; }\n");
        sb.append(".formula-row:hover .formula-row-bg { fill: rgba(33,150,243,0.10); }\n");
        sb.append(".formula-row:hover .formula-row-text { text-decoration: underline; }\n");
        sb.append(".formula-row.selected .formula-row-bg { fill: rgba(33,150,243,0.22); stroke: #1976d2; stroke-width: 1px; }\n");
        sb.append(".formula-row.selected .formula-row-text { font-weight: bold; }\n");
        sb.append(".formula-row-text { pointer-events: none; }\n");
        sb.append(".link { fill: none; stroke: #bbb; stroke-width: 1.5px; }\n");
        sb.append(".kripke-node circle { fill: #e8eaf6; stroke: #3949ab; stroke-width: 2px; }\n");
        sb.append(".kripke-node text { font-size: 11px; text-anchor: middle; dominant-baseline: central; fill: #1a237e; font-weight: bold; }\n");
        sb.append(".kripke-node.summary circle { fill: #ede7f6; stroke-dasharray: 4 2; cursor: pointer; }\n");
        sb.append(".kripke-node.summary text { fill: #4527a0; }\n");
        sb.append(".kripke-link { stroke: #3949ab; stroke-width: 1.5px; fill: none; marker-end: url(#arrow); }\n");
        sb.append("</style>\n");
    }

    // -------------------------------------------------------------------------
    // D3 JavaScript
    // -------------------------------------------------------------------------

    private static void appendD3Script(StringBuilder sb) {
        sb.append("<script>\n");
        sb.append("(function() {\n");
        sb.append("const DATA = PROOF_DATA;\n\n");

        // Status badge
        sb.append("document.getElementById('proof-status').innerHTML =\n");
        sb.append("  DATA.closed\n");
        sb.append("    ? '<span style=\"color:#b71c1c;font-weight:bold\">[CLOSED]</span>'\n");
        sb.append("    : '<span style=\"color:#1b5e20;font-weight:bold\">[OPEN]</span>';\n\n");

        // Color map
        sb.append("const COLORS = {\n");
        sb.append("  PROBLEM:     '#555',\n");
        sb.append("  ONE_PREMISE: '#1b5e20',\n");
        sb.append("  TWO_PREMISE: '#0d47a1',\n");
        sb.append("  PB:          '#e65100',\n");
        sb.append("  CLOSURE:     '#b71c1c',\n");
        sb.append("  default:     '#444'\n");
        sb.append("};\n");
        sb.append("function nodeColor(f) { return COLORS[f.ruleType] || COLORS.default; }\n\n");

        // Build hierarchical data for D3 from the branch tree.
        // Only branch nodes appear in the hierarchy; formulas are stored as data
        // and rendered as rows inside each branch box.
        sb.append("// --- Build D3 hierarchy from proof tree ---\n");
        sb.append("function buildHierarchy(branch) {\n");
        sb.append("  const node = {\n");
        sb.append("    id: branch.branchId,\n");
        sb.append("    label: branch.branchId,\n");
        sb.append("    closed: branch.closed,\n");
        sb.append("    formulas: branch.formulas || [],\n");
        sb.append("    rinstances: branch.rinstances || [],\n");
        sb.append("    _collapsed: false,\n");
        sb.append("    _allChildren: []\n");
        sb.append("  };\n");
        sb.append("  if (branch.left)  node._allChildren.push(buildHierarchy(branch.left));\n");
        sb.append("  if (branch.right) node._allChildren.push(buildHierarchy(branch.right));\n");
        sb.append("  return node;\n");
        sb.append("}\n\n");

        // D3 tree layout -- top-down, each node is a branch box containing its formulas.
        // Children are collapsed/expanded interactively; zoom+pan is enabled.
        sb.append("// --- D3 tree rendering ---\n");
        sb.append("const BOX_W       = 210;  // branch box width (px)\n");
        sb.append("const ROW_H       = 14;   // height per formula row (px)\n");
        sb.append("const HDR_H       = 20;   // header row height (px)\n");
        sb.append("const PAD         = 6;    // inner padding (px)\n");
        sb.append("const V_LEVEL_GAP = 50;   // vertical gap between box bottom and child box top\n");
        sb.append("const H_NODE_GAP  = 14;   // extra horizontal gap between sibling boxes\n\n");
        sb.append("function boxH(nodeData) {\n");
        sb.append("  return PAD * 2 + HDR_H + ROW_H * nodeData.formulas.length;\n");
        sb.append("}\n\n");
        sb.append("const hierarchyData = buildHierarchy(DATA.tree);\n\n");
        sb.append("// --- Initial collapse: reveal as much as fits a budget, breadth-first ---\n");
        sb.append("// Large proofs (thousands of nodes) would otherwise render fully expanded\n");
        sb.append("// on first paint -- unreadable and slow. Instead we expand branches\n");
        sb.append("// level-by-level from the root while the running total of visible formula\n");
        sb.append("// rows stays under REVEAL_BUDGET, then collapse the remaining frontier.\n");
        sb.append("// Small proofs (well under budget) are unaffected: nothing ends up collapsed.\n");
        sb.append("const REVEAL_BUDGET = 60;\n");
        sb.append("function computeSubtreeCount(node) {\n");
        sb.append("  let count = node.formulas.length;\n");
        sb.append("  node._allChildren.forEach(c => { count += computeSubtreeCount(c); });\n");
        sb.append("  node._subtreeCount = count;\n");
        sb.append("  return count;\n");
        sb.append("}\n");
        sb.append("const TOTAL_FORMULAS = computeSubtreeCount(hierarchyData);\n");
        sb.append("(function applyInitialCollapse() {\n");
        sb.append("  let shown = hierarchyData.formulas.length;\n");
        sb.append("  const queue = [hierarchyData];\n");
        sb.append("  while (queue.length) {\n");
        sb.append("    const node = queue.shift();\n");
        sb.append("    if (node._allChildren.length === 0) continue;\n");
        sb.append("    const childrenCost = node._allChildren.reduce((s, c) => s + c.formulas.length, 0);\n");
        sb.append("    if (shown + childrenCost <= REVEAL_BUDGET) {\n");
        sb.append("      node._collapsed = false;\n");
        sb.append("      shown += childrenCost;\n");
        sb.append("      node._allChildren.forEach(c => queue.push(c));\n");
        sb.append("    } else {\n");
        sb.append("      node._collapsed = true;\n");
        sb.append("    }\n");
        sb.append("  }\n");
        sb.append("})();\n\n");
        sb.append("let zoomBehavior;\n\n");
        sb.append("function renderTree() {\n");
        sb.append("  const svg = d3.select('#tree-svg');\n");
        sb.append("  const container = document.getElementById('tree-container');\n");
        sb.append("  const cW = container.clientWidth  || 800;\n");
        sb.append("  const cH = container.clientHeight || 600;\n");
        sb.append("  svg.attr('width', cW).attr('height', cH);\n\n");
        sb.append("  svg.selectAll('*').remove();\n\n");
        sb.append("  // Zoom + pan\n");
        sb.append("  zoomBehavior = d3.zoom().scaleExtent([0.05, 4])\n");
        sb.append("    .on('zoom', (e) => gRoot.attr('transform', e.transform));\n");
        sb.append("  svg.call(zoomBehavior);\n\n");
        sb.append("  const gRoot = svg.append('g');\n\n");
        sb.append("  update(gRoot, svg);\n");
        sb.append("}\n\n");
        sb.append("function update(gRoot, svg) {\n");
        sb.append("  gRoot.selectAll('*').remove();\n\n");
        sb.append("  // Build d3 hierarchy using visible children only\n");
        sb.append("  const root = d3.hierarchy(hierarchyData,\n");
        sb.append("    d => d._collapsed ? [] : d._allChildren);\n\n");
        sb.append("  // Update the \"N of M formulas shown\" stats badge in the header.\n");
        sb.append("  let visibleFormulas = 0;\n");
        sb.append("  root.each(d => { visibleFormulas += d.data.formulas.length; });\n");
        sb.append("  const statsEl = document.getElementById('tree-stats');\n");
        sb.append("  if (statsEl) {\n");
        sb.append("    statsEl.textContent = (visibleFormulas < TOTAL_FORMULAS)\n");
        sb.append("      ? '(' + visibleFormulas + ' of ' + TOTAL_FORMULAS + ' formulas shown)'\n");
        sb.append("      : '(' + TOTAL_FORMULAS + ' formulas)';\n");
        sb.append("  }\n\n");
        sb.append("  // Compute per-node box heights\n");
        sb.append("  root.each(d => { d._bh = boxH(d.data); });\n\n");
        sb.append("  // nodeSize: [horizontal-spacing, vertical-spacing]\n");
        sb.append("  // In a top-down d3.tree: x spreads left/right, y goes top/down.\n");
        sb.append("  const treeLayout = d3.tree()\n");
        sb.append("    .nodeSize([BOX_W + H_NODE_GAP, 1])\n");
        sb.append("    .separation((a, b) => 1);\n");
        sb.append("  treeLayout(root);\n\n");
        sb.append("  // Assign y positions manually so each level starts below the tallest\n");
        sb.append("  // box of its parent level, rather than using d3's uniform y spacing.\n");
        sb.append("  const levelMaxH = {};\n");
        sb.append("  root.each(d => {\n");
        sb.append("    const dep = d.depth;\n");
        sb.append("    if (!levelMaxH[dep] || d._bh > levelMaxH[dep]) levelMaxH[dep] = d._bh;\n");
        sb.append("  });\n");
        sb.append("  const levelY = {};\n");
        sb.append("  levelY[0] = 0;\n");
        sb.append("  const maxDepth = root.height;\n");
        sb.append("  for (let i = 1; i <= maxDepth; i++) {\n");
        sb.append("    levelY[i] = levelY[i-1] + (levelMaxH[i-1] || 40) + V_LEVEL_GAP;\n");
        sb.append("  }\n");
        sb.append("  root.each(d => { d.y = levelY[d.depth]; });\n\n");
        sb.append("  // Compute full extent for fit-to-screen\n");
        sb.append("  let xMin = Infinity, xMax = -Infinity, yMax = 0;\n");
        sb.append("  root.each(d => {\n");
        sb.append("    xMin = Math.min(xMin, d.x - BOX_W / 2);\n");
        sb.append("    xMax = Math.max(xMax, d.x + BOX_W / 2);\n");
        sb.append("    yMax = Math.max(yMax, d.y + d._bh);\n");
        sb.append("  });\n");
        sb.append("  const treeW = xMax - xMin + PAD * 2;\n");
        sb.append("  const treeH = yMax + PAD * 2;\n\n");
        sb.append("  // Store bounds for fit button\n");
        sb.append("  gRoot._bounds = { xMin, treeW, treeH };\n\n");
        sb.append("  // Links: curved vertical path from bottom-center of parent to top-center of child\n");
        sb.append("  gRoot.selectAll('.link').data(root.links()).enter().append('path')\n");
        sb.append("    .attr('class', 'link')\n");
        sb.append("    .attr('d', d => {\n");
        sb.append("      const sx = d.source.x;\n");
        sb.append("      const sy = d.source.y + d.source._bh;\n");
        sb.append("      const tx = d.target.x;\n");
        sb.append("      const ty = d.target.y;\n");
        sb.append("      const my = (sy + ty) / 2;\n");
        sb.append("      return `M${sx},${sy} C${sx},${my} ${tx},${my} ${tx},${ty}`;\n");
        sb.append("    });\n\n");
        sb.append("  // Branch box groups -- each placed at (x - BOX_W/2, y).\n");
        sb.append("  // We track both the selected branch box and the selected formula row\n");
        sb.append("  // separately so clicking a formula highlights *only* that row (with the\n");
        sb.append("  // containing branch outlined for context), while clicking the branch\n");
        sb.append("  // background clears any row selection.\n");
        sb.append("  let selectedBox = null;\n");
        sb.append("  let selectedRow = null;\n");
        sb.append("  function clearSelection() {\n");
        sb.append("    if (selectedBox) { d3.select(selectedBox).classed('selected', false); selectedBox = null; }\n");
        sb.append("    if (selectedRow) { d3.select(selectedRow).classed('selected', false); selectedRow = null; }\n");
        sb.append("  }\n");
        sb.append("  const node = gRoot.selectAll('.node').data(root.descendants()).enter()\n");
        sb.append("    .append('g')\n");
        sb.append("    .attr('class', 'node')\n");
        sb.append("    .attr('transform', d => `translate(${d.x - BOX_W / 2},${d.y})`);\n\n");
        sb.append("  // Background rectangle -- click to select branch in detail panel\n");
        sb.append("  node.append('rect')\n");
        sb.append("    .attr('class', 'branch-box')\n");
        sb.append("    .attr('x', 0).attr('y', 0)\n");
        sb.append("    .attr('width', BOX_W)\n");
        sb.append("    .attr('height', d => d._bh)\n");
        sb.append("    .attr('rx', 4)\n");
        sb.append("    .style('fill', d => d.data.closed ? '#fff3f3' : '#f3fff3')\n");
        sb.append("    .style('stroke', d => d.data.closed ? '#c62828' : '#388e3c')\n");
        sb.append("    .style('stroke-width', '1.5px')\n");
        sb.append("    .on('click', function(event, d) {\n");
        sb.append("      event.stopPropagation();\n");
        sb.append("      clearSelection();\n");
        sb.append("      selectedBox = this;\n");
        sb.append("      d3.select(this).classed('selected', true);\n");
        sb.append("      showDetail(d.data, null);\n");
        sb.append("    });\n\n");
        sb.append("  // Header separator\n");
        sb.append("  node.append('line')\n");
        sb.append("    .attr('x1', 0).attr('y1', HDR_H)\n");
        sb.append("    .attr('x2', BOX_W).attr('y2', HDR_H)\n");
        sb.append("    .style('stroke', d => d.data.closed ? '#ef9a9a' : '#a5d6a7')\n");
        sb.append("    .style('stroke-width', '1px');\n\n");
        sb.append("  // Branch ID\n");
        sb.append("  node.append('text')\n");
        sb.append("    .attr('x', PAD).attr('y', HDR_H - 5)\n");
        sb.append("    .style('font-size', '10px').style('font-weight', 'bold')\n");
        sb.append("    .style('fill', d => d.data.closed ? '#b71c1c' : '#2e7d32')\n");
        sb.append("    .text(d => d.data.label + (d.data.closed ? '  \\u00d7' : ''));\n\n");
        sb.append("  // Collapse/expand toggle -- shown only if branch has children. While\n");
        sb.append("  // collapsed, shows how many formula rows are hidden below (subtree count\n");
        sb.append("  // minus this box's own rows) so users know how much is being skipped.\n");
        sb.append("  node.filter(d => d.data._allChildren.length > 0)\n");
        sb.append("    .append('text')\n");
        sb.append("    .attr('x', BOX_W - PAD - 2).attr('y', HDR_H - 5)\n");
        sb.append("    .attr('text-anchor', 'end')\n");
        sb.append("    .style('font-size', '11px').style('fill', '#555').style('cursor', 'pointer')\n");
        sb.append("    .text(d => d.data._collapsed\n");
        sb.append("      ? '\\u25b6 +' + (d.data._subtreeCount - d.data.formulas.length)\n");
        sb.append("      : '\\u25bc')\n");
        sb.append("    .on('click', function(event, d) {\n");
        sb.append("      event.stopPropagation();\n");
        sb.append("      d.data._collapsed = !d.data._collapsed;\n");
        sb.append("      update(gRoot, svg);\n");
        sb.append("    });\n\n");
        sb.append("  // Formula rows inside each box.\n");
        sb.append("  // Each row is a <g.formula-row> with (1) a transparent background\n");
        sb.append("  // rect that captures pointer events across the full row width and\n");
        sb.append("  // (2) the text drawn on top. The text itself has pointer-events:none\n");
        sb.append("  // so the rect always receives clicks even on whitespace between glyphs.\n");
        sb.append("  // CSS adds a hover background + selected style so each formula reads\n");
        sb.append("  // as its own clickable entity.\n");
        sb.append("  node.each(function(d) {\n");
        sb.append("    const grp = d3.select(this);\n");
        sb.append("    d.data.formulas.forEach((f, i) => {\n");
        sb.append("      const rowY = HDR_H + PAD + ROW_H * i;\n");
        sb.append("      const rowG = grp.append('g')\n");
        sb.append("        .attr('class', 'formula-row')\n");
        sb.append("        .attr('transform', `translate(0, ${rowY})`);\n");
        sb.append("      rowG.append('rect')\n");
        sb.append("        .attr('class', 'formula-row-bg')\n");
        sb.append("        .attr('x', 2).attr('y', 0)\n");
        sb.append("        .attr('width', BOX_W - 4).attr('height', ROW_H)\n");
        sb.append("        .attr('rx', 2);\n");
        sb.append("      rowG.append('text')\n");
        sb.append("        .attr('class', 'formula-row-text')\n");
        sb.append("        .attr('x', PAD)\n");
        sb.append("        .attr('y', ROW_H - 3)\n");
        sb.append("        .style('font-size', '9px').style('fill', nodeColor(f))\n");
        sb.append("        .text(f.text)\n");
        sb.append("        .append('title').text(f.text);\n");
        sb.append("      rowG.on('click', function(event) {\n");
        sb.append("        event.stopPropagation();\n");
        sb.append("        clearSelection();\n");
        sb.append("        selectedRow = this;\n");
        sb.append("        d3.select(this).classed('selected', true);\n");
        sb.append("        // Outline the containing branch for context so users still see\n");
        sb.append("        // which branch the selected formula belongs to.\n");
        sb.append("        selectedBox = grp.select('.branch-box').node();\n");
        sb.append("        d3.select(selectedBox).classed('selected', true);\n");
        sb.append("        showDetail(d.data, f);\n");
        sb.append("      });\n");
        sb.append("    });\n");
        sb.append("  });\n\n");
        sb.append("  // Auto-fit on first render or when tree structure changes\n");
        sb.append("  fitTree(gRoot, svg);\n");
        sb.append("}\n\n");
        sb.append("function fitTree(gRoot, svg) {\n");
        sb.append("  const b = gRoot._bounds;\n");
        sb.append("  if (!b) return;\n");
        sb.append("  const container = document.getElementById('tree-container');\n");
        sb.append("  const cW = container.clientWidth  || 800;\n");
        sb.append("  const cH = container.clientHeight || 600;\n");
        sb.append("  const scale = Math.min(0.95, Math.min(cW / b.treeW, cH / b.treeH));\n");
        sb.append("  const tx = (cW - b.treeW * scale) / 2 - b.xMin * scale;\n");
        sb.append("  const ty = 20;\n");
        sb.append("  const svgSel = d3.select('#tree-svg');\n");
        sb.append("  svgSel.call(zoomBehavior.transform,\n");
        sb.append("    d3.zoomIdentity.translate(tx, ty).scale(scale));\n");
        sb.append("}\n\n");

        // Detail panel -- branchData is always the branch node; formula is the clicked
        // formula row (null if the branch box background was clicked).
        sb.append("// --- Detail panel ---\n");
        sb.append("function showDetail(branchData, formula) {\n");
        sb.append("  document.getElementById('detail-hint').style.display = 'none';\n");
        sb.append("  document.getElementById('detail-content').style.display = 'block';\n\n");
        sb.append("  const fDiv = document.getElementById('detail-formula');\n");
        sb.append("  if (formula) {\n");
        sb.append("    fDiv.innerHTML = '<strong>' + esc(formula.text) + '</strong>'\n");
        sb.append("      + '<br>Sign: ' + esc(formula.sign)\n");
        sb.append("      + '<br>Label: ' + esc(formula.label)\n");
        sb.append("      + '<br>Rule type: <span style=\"color:' + (COLORS[formula.ruleType]||'#444') + '\">' + esc(formula.ruleType) + '</span>'\n");
        sb.append("      + (formula.rule ? '<br>Rule: ' + esc(formula.rule) : '')\n");
        sb.append("      + (formula.main ? '<br>Main premise: ' + esc(formula.main) : '')\n");
        sb.append("      + (formula.auxiliaries && formula.auxiliaries.length\n");
        sb.append("          ? '<br>Auxiliaries: ' + formula.auxiliaries.map(a=>esc(a)).join(', ') : '')\n");
        sb.append("      + '<br><span style=\"color:#888;font-size:0.9em\">Branch: ' + esc(branchData.label) + '</span>';\n");
        sb.append("  } else {\n");
        sb.append("    fDiv.innerHTML = '<strong>Branch:</strong> ' + esc(branchData.label)\n");
        sb.append("      + (branchData.closed\n");
        sb.append("          ? ' <span style=\"color:#b71c1c\">(closed)</span>'\n");
        sb.append("          : ' <span style=\"color:#1b5e20\">(open)</span>')\n");
        sb.append("      + '<br><span style=\"color:#888;font-size:0.9em\">' + branchData.formulas.length + ' formula(s)</span>';\n");
        sb.append("  }\n\n");
        sb.append("  const riList = document.getElementById('detail-rinstances');\n");
        sb.append("  riList.innerHTML = '';\n");
        sb.append("  const allRinst = branchData.rinstances || [];\n");
        sb.append("  // When a formula is selected, slice the branch's rinstances list\n");
        sb.append("  // to the temporal state at the time that node was added (snapshot\n");
        sb.append("  // captured in IPLProofTree.addLast). When the branch box itself\n");
        sb.append("  // is selected, show the full list.\n");
        sb.append("  let visibleRinst = allRinst;\n");
        sb.append("  let trimmedCount = 0;\n");
        sb.append("  if (formula && typeof formula.rinstancesAtCreation === 'number' && formula.rinstancesAtCreation >= 0) {\n");
        sb.append("    const cut = Math.min(formula.rinstancesAtCreation, allRinst.length);\n");
        sb.append("    visibleRinst = allRinst.slice(0, cut);\n");
        sb.append("    trimmedCount = allRinst.length - cut;\n");
        sb.append("  }\n");
        sb.append("  visibleRinst.forEach(r => {\n");
        sb.append("    const li = document.createElement('li');\n");
        sb.append("    li.textContent = r;\n");
        sb.append("    riList.appendChild(li);\n");
        sb.append("  });\n");
        sb.append("  if (!visibleRinst.length) {\n");
        sb.append("    riList.innerHTML = '<li style=\"color:#aaa\">None at this point in the proof</li>';\n");
        sb.append("  }\n");
        sb.append("  if (trimmedCount > 0) {\n");
        sb.append("    const li = document.createElement('li');\n");
        sb.append("    li.style.color = '#aaa';\n");
        sb.append("    li.style.fontStyle = 'italic';\n");
        sb.append("    li.textContent = '(+' + trimmedCount + ' more registered after this node was added)';\n");
        sb.append("    riList.appendChild(li);\n");
        sb.append("  }\n");
        sb.append("}\n\n");

        // Kripke DAG -- layered/hierarchical layout instead of a force simulation,
        // so it stays readable as the number of constants grows (proofs with many
        // states would otherwise collapse into an unreadable tangle). Nodes are
        // placed by level = longest-path distance from a root (a label with no
        // predecessor under the Hasse-reduced relation the exporter already sends);
        // levels compress vertically to fit the fixed-height container. Levels with
        // more than LEVEL_COLLAPSE_THRESHOLD siblings collapse by default into a
        // single clickable summary node, so a wide fan-out (common with heavy PB)
        // does not force excessive horizontal scrolling.
        sb.append("// --- Kripke context graph (layered layout, collapsible dense levels) ---\n");
        sb.append("const expandedKripkeLevels = new Set();\n");
        sb.append("function renderKripke() {\n");
        sb.append("  const kripke = DATA.kripke;\n");
        sb.append("  if (!kripke) return;\n");
        sb.append("  const container = document.getElementById('kripke-container');\n");
        sb.append("  const H = 420;\n");
        sb.append("  const NODE_R = 16;\n");
        sb.append("  const SUMMARY_R = 22;\n");
        sb.append("  const MIN_SPACING = 52;\n");
        sb.append("  const LEVEL_COLLAPSE_THRESHOLD = 12;\n\n");
        sb.append("  const ids = kripke.labels;\n");
        sb.append("  const incoming = new Map(ids.map(id => [id, []]));\n");
        sb.append("  const outgoing = new Map(ids.map(id => [id, []]));\n");
        sb.append("  kripke.relations.forEach(([a, b]) => { outgoing.get(a).push(b); incoming.get(b).push(a); });\n\n");
        sb.append("  // level(v) = 0 for a root (no predecessor); otherwise 1 + max level of predecessors.\n");
        sb.append("  const level = new Map();\n");
        sb.append("  function computeLevel(id, visiting) {\n");
        sb.append("    if (level.has(id)) return level.get(id);\n");
        sb.append("    if (visiting.has(id)) return 0;\n");
        sb.append("    visiting.add(id);\n");
        sb.append("    const preds = incoming.get(id);\n");
        sb.append("    const lvl = preds.length === 0 ? 0 : 1 + Math.max(...preds.map(p => computeLevel(p, visiting)));\n");
        sb.append("    level.set(id, lvl);\n");
        sb.append("    return lvl;\n");
        sb.append("  }\n");
        sb.append("  ids.forEach(id => computeLevel(id, new Set()));\n\n");
        sb.append("  const byLevel = new Map();\n");
        sb.append("  ids.forEach(id => {\n");
        sb.append("    const l = level.get(id);\n");
        sb.append("    if (!byLevel.has(l)) byLevel.set(l, []);\n");
        sb.append("    byLevel.get(l).push(id);\n");
        sb.append("  });\n");
        sb.append("  const maxLevel = Math.max(0, ...ids.map(id => level.get(id)));\n\n");
        sb.append("  // Decide, per level, whether to render individual nodes or a single\n");
        sb.append("  // collapsed summary node standing in for all of them.\n");
        sb.append("  const renderNodes = [];\n");
        sb.append("  const idToRenderId = new Map();\n");
        sb.append("  for (let l = 0; l <= maxLevel; l++) {\n");
        sb.append("    const atLevel = byLevel.get(l) || [];\n");
        sb.append("    if (atLevel.length > LEVEL_COLLAPSE_THRESHOLD && !expandedKripkeLevels.has(l)) {\n");
        sb.append("      const summaryId = '__summary_' + l;\n");
        sb.append("      renderNodes.push({ id: summaryId, level: l, isSummary: true, count: atLevel.length });\n");
        sb.append("      atLevel.forEach(id => idToRenderId.set(id, summaryId));\n");
        sb.append("    } else {\n");
        sb.append("      atLevel.forEach(id => {\n");
        sb.append("        renderNodes.push({ id, level: l, isSummary: false });\n");
        sb.append("        idToRenderId.set(id, id);\n");
        sb.append("      });\n");
        sb.append("    }\n");
        sb.append("  }\n\n");
        sb.append("  const byRenderLevel = new Map();\n");
        sb.append("  renderNodes.forEach(n => {\n");
        sb.append("    if (!byRenderLevel.has(n.level)) byRenderLevel.set(n.level, []);\n");
        sb.append("    byRenderLevel.get(n.level).push(n);\n");
        sb.append("  });\n");
        sb.append("  const maxPerLevel = Math.max(1, ...[...byRenderLevel.values()].map(a => a.length));\n\n");
        sb.append("  // Width: comfortable spacing per node at the widest level, but never\n");
        sb.append("  // narrower than the container (so small graphs still fill the pane).\n");
        sb.append("  const W = Math.max(container.clientWidth || 300, maxPerLevel * MIN_SPACING);\n");
        sb.append("  const svg = d3.select('#kripke-svg').attr('width', W).attr('height', H);\n");
        sb.append("  svg.selectAll('*').remove();\n\n");
        sb.append("  svg.append('defs').append('marker')\n");
        sb.append("    .attr('id', 'arrow').attr('viewBox', '0 -5 10 10')\n");
        sb.append("    .attr('refX', 9).attr('refY', 0)\n");
        sb.append("    .attr('markerWidth', 8).attr('markerHeight', 8)\n");
        sb.append("    .attr('orient', 'auto')\n");
        sb.append("    .append('path').attr('d', 'M0,-5L10,0L0,5').attr('fill', '#3949ab');\n\n");
        sb.append("  // Vertical spacing compresses so deep chains still fit in the fixed height.\n");
        sb.append("  const topPad = 24, bottomPad = 16;\n");
        sb.append("  const levelGap = maxLevel > 0 ? (H - topPad - bottomPad) / maxLevel : 0;\n");
        sb.append("  const pos = new Map();\n");
        sb.append("  for (let l = 0; l <= maxLevel; l++) {\n");
        sb.append("    const atLevel = byRenderLevel.get(l) || [];\n");
        sb.append("    const y = topPad + l * levelGap;\n");
        sb.append("    atLevel.forEach((n, i) => {\n");
        sb.append("      const x = (W / (atLevel.length + 1)) * (i + 1);\n");
        sb.append("      pos.set(n.id, { x, y });\n");
        sb.append("    });\n");
        sb.append("  }\n\n");
        sb.append("  // Deduplicate edges through collapsed summaries; drop edges that end up\n");
        sb.append("  // entirely inside the same summary node (both endpoints collapsed together).\n");
        sb.append("  const edgeMap = new Map();\n");
        sb.append("  kripke.relations.forEach(([a, b]) => {\n");
        sb.append("    const ra = idToRenderId.get(a), rb = idToRenderId.get(b);\n");
        sb.append("    if (ra === rb) return;\n");
        sb.append("    edgeMap.set(ra + '|' + rb, [ra, rb]);\n");
        sb.append("  });\n");
        sb.append("  const renderRelations = [...edgeMap.values()];\n\n");
        sb.append("  // Links, trimmed to the target node's circle boundary (plus a small gap)\n");
        sb.append("  // so the arrowhead is drawn in open space instead of under the node circle,\n");
        sb.append("  // which is painted on top of the links.\n");
        sb.append("  function radiusOf(id) {\n");
        sb.append("    const n = renderNodes.find(rn => rn.id === id);\n");
        sb.append("    return (n && n.isSummary) ? SUMMARY_R : NODE_R;\n");
        sb.append("  }\n");
        sb.append("  svg.append('g').selectAll('line').data(renderRelations).enter().append('line')\n");
        sb.append("    .attr('class', 'kripke-link')\n");
        sb.append("    .attr('x1', d => pos.get(d[0]).x)\n");
        sb.append("    .attr('y1', d => pos.get(d[0]).y)\n");
        sb.append("    .attr('x2', d => {\n");
        sb.append("      const s = pos.get(d[0]), t = pos.get(d[1]);\n");
        sb.append("      const dx = t.x - s.x, dy = t.y - s.y, dist = Math.sqrt(dx * dx + dy * dy) || 1;\n");
        sb.append("      return t.x - (dx / dist) * (radiusOf(d[1]) + 4);\n");
        sb.append("    })\n");
        sb.append("    .attr('y2', d => {\n");
        sb.append("      const s = pos.get(d[0]), t = pos.get(d[1]);\n");
        sb.append("      const dx = t.x - s.x, dy = t.y - s.y, dist = Math.sqrt(dx * dx + dy * dy) || 1;\n");
        sb.append("      return t.y - (dy / dist) * (radiusOf(d[1]) + 4);\n");
        sb.append("    });\n\n");
        sb.append("  const gnode = svg.append('g').selectAll('.kripke-node').data(renderNodes).enter()\n");
        sb.append("    .append('g')\n");
        sb.append("    .attr('class', n => 'kripke-node' + (n.isSummary ? ' summary' : ''))\n");
        sb.append("    .attr('transform', n => `translate(${pos.get(n.id).x},${pos.get(n.id).y})`);\n");
        sb.append("  gnode.append('circle').attr('r', n => n.isSummary ? SUMMARY_R : NODE_R);\n");
        sb.append("  gnode.append('text').text(n => n.isSummary ? ('+' + n.count) : n.id);\n");
        sb.append("  gnode.append('title').text(n => n.isSummary\n");
        sb.append("    ? n.count + ' states at this level -- click to expand'\n");
        sb.append("    : n.id);\n");
        sb.append("  gnode.filter(n => n.isSummary).on('click', function(event, n) {\n");
        sb.append("    event.stopPropagation();\n");
        sb.append("    expandedKripkeLevels.add(n.level);\n");
        sb.append("    renderKripke();\n");
        sb.append("  });\n");
        sb.append("}\n\n");

        // Trace -- formato analogo al de los logs de tests (IPLTracer.formatText):
        // "[branch] Step N: <message>" seguido (opcionalmente) por
        // "[branch]   <detail-indented>" en una linea adicional.
        sb.append("// --- Trace ---\n");
        sb.append("function renderTrace() {\n");
        sb.append("  const div = document.getElementById('trace-content');\n");
        sb.append("  if (!DATA.trace || !DATA.trace.events) { div.textContent = 'No trace available.'; return; }\n");
        sb.append("  const lines = [];\n");
        sb.append("  DATA.trace.events.forEach(e => {\n");
        sb.append("    const branchTag = e.branch ? '[' + e.branch + '] ' : '';\n");
        sb.append("    // Events without their own step number (INFO, RINSTANCE_REGISTERED,\n");
        sb.append("    // LABEL_REGISTERED) are sub-lines of the previous step; mimic the\n");
        sb.append("    // .log format by indenting them with spaces.\n");
        sb.append("    const isSubline = (e.type === 'INFO' || e.type === 'RINSTANCE_REGISTERED' || e.type === 'LABEL_REGISTERED');\n");
        sb.append("    if (isSubline) {\n");
        sb.append("      lines.push(branchTag + '       ' + (e.message || ''));\n");
        sb.append("    } else {\n");
        sb.append("      lines.push(branchTag + 'Step ' + e.step + ': ' + (e.message || ''));\n");
        sb.append("      if (e.detail) {\n");
        sb.append("        // Some event types use a labelled detail; others just indent it.\n");
        sb.append("        let prefix = '  ';\n");
        sb.append("        if (e.type === 'RULE_BLOCKED' || e.type === 'PB_SKIPPED') prefix = '  Reason: ';\n");
        sb.append("        else if (e.type === 'FORMULA_SELECTED') prefix = '  (';\n");
        sb.append("        let suffix = (e.type === 'FORMULA_SELECTED') ? ')' : '';\n");
        sb.append("        lines.push(branchTag + prefix + e.detail + suffix);\n");
        sb.append("      }\n");
        sb.append("      if (e.type === 'ALGORITHM_END' && e.detail) {\n");
        sb.append("        // Already handled above, but ALGORITHM_END uses 'Result:' prefix.\n");
        sb.append("        // Replace the last pushed detail line.\n");
        sb.append("        lines[lines.length - 1] = branchTag + '  Result: ' + e.detail;\n");
        sb.append("      }\n");
        sb.append("    }\n");
        sb.append("  });\n");
        sb.append("  div.textContent = lines.join('\\n');\n");
        sb.append("}\n\n");

        // HTML escape helper
        sb.append("function esc(s) {\n");
        sb.append("  if (!s) return '';\n");
        sb.append("  return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');\n");
        sb.append("}\n\n");

        // Init
        sb.append("renderTree();\n");
        sb.append("renderKripke();\n");
        sb.append("renderTrace();\n\n");
        sb.append("// Toolbar buttons\n");
        sb.append("document.getElementById('btn-fit').addEventListener('click', () => {\n");
        sb.append("  const gRoot = d3.select('#tree-svg g');\n");
        sb.append("  fitTree(gRoot.node() ? gRoot : null, d3.select('#tree-svg'));\n");
        sb.append("  // Re-render to get fresh gRoot reference\n");
        sb.append("  renderTree();\n");
        sb.append("});\n");
        sb.append("document.getElementById('btn-zoom-in').addEventListener('click', () => {\n");
        sb.append("  d3.select('#tree-svg').call(zoomBehavior.scaleBy, 1.4);\n");
        sb.append("});\n");
        sb.append("document.getElementById('btn-zoom-out').addEventListener('click', () => {\n");
        sb.append("  d3.select('#tree-svg').call(zoomBehavior.scaleBy, 1 / 1.4);\n");
        sb.append("});\n");
        sb.append("function setAllCollapsed(node, val) {\n");
        sb.append("  node._collapsed = val;\n");
        sb.append("  (node._allChildren || []).forEach(c => setAllCollapsed(c, val));\n");
        sb.append("}\n");
        sb.append("document.getElementById('btn-expand-all').addEventListener('click', () => {\n");
        sb.append("  setAllCollapsed(hierarchyData, false);\n");
        sb.append("  renderTree();\n");
        sb.append("});\n");
        sb.append("document.getElementById('btn-collapse-all').addEventListener('click', () => {\n");
        sb.append("  // Collapse all children but keep the root visible\n");
        sb.append("  (hierarchyData._allChildren || []).forEach(c => setAllCollapsed(c, true));\n");
        sb.append("  renderTree();\n");
        sb.append("});\n");
        sb.append("// Re-render on window resize\n");
        sb.append("window.addEventListener('resize', () => renderTree());\n");
        sb.append("})();\n");
        sb.append("</script>\n");
    }

    // -------------------------------------------------------------------------
    // Utility
    // -------------------------------------------------------------------------

    private static String esc(String s) {
        if (s == null) return "";
        return s.replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\"", "&quot;")
                .replace("'", "&#39;");
    }
}
