// Figures and tables for the margin of the tours. Each figure is an inline SVG about as wide
// as the margin column, and it takes its colours from the theme through the classes of
// assets/guide.css. The numbers of the tables come from the module that the interactive
// examples use, so the build computes them.
import { ringGraph, forestDistribution, horakKim, logStar, secondMomentBound } from '../site/assets/math-core.mjs';

const round = (value) => Math.round(value * 100) / 100;
const line = (a, b, cls) => `<line x1="${round(a[0])}" y1="${round(a[1])}" x2="${round(b[0])}" y2="${round(b[1])}" class="${cls}"/>`;
const node = (p, cls = 'fig-node', radius = 3.6) => `<circle cx="${round(p[0])}" cy="${round(p[1])}" r="${radius}" class="${cls}"/>`;
const label = (p, text, cls = 'fig-text', anchor = 'middle') => `<text x="${round(p[0])}" y="${round(p[1])}" text-anchor="${anchor}" class="${cls}">${text}</text>`;
const svg = (width, height, title, body) => `<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${title}">${body}</svg>`;
const number = (value) => value.toLocaleString('en-US');

// Four small copies of one graph, each with one even subgraph drawn thick.
// `marked` is the set P. An edge of the even subgraph without an end in P is in the outside part.
function panels({ points, edges, subgraphs, notes, marked = [], title }) {
  const width = 168, height = 108;
  const parts = [];
  subgraphs.forEach((chosen, index) => {
    const dx = (index % 2) * width, dy = Math.floor(index / 2) * height;
    const at = (v) => [points[v][0] + dx, points[v][1] + dy];
    const keys = new Set(chosen.map(([u, v]) => `${Math.min(u, v)}-${Math.max(u, v)}`));
    for (const [u, v] of edges) parts.push(line(at(u), at(v), 'fig-edge'));
    for (const [u, v] of edges) {
      if (!keys.has(`${Math.min(u, v)}-${Math.max(u, v)}`)) continue;
      const outside = marked.length && !marked.includes(u) && !marked.includes(v);
      parts.push(line(at(u), at(v), outside ? 'fig-warm' : 'fig-main'));
    }
    points.forEach((_, v) => parts.push(node(at(v), marked.includes(v) ? 'fig-node fig-node-marked' : 'fig-node')));
    parts.push(label([dx + width / 2, dy + height - 8], notes[index], 'fig-text fig-text-note'));
  });
  return svg(2 * width, 2 * height, title, parts.join(''));
}

// Two triangles with one common vertex: rank 2, four even subgraphs.
function evenSubgraphs() {
  const points = [[84, 50], [34, 20], [34, 80], [134, 20], [134, 80]];
  const left = [[0, 1], [1, 2], [2, 0]], right = [[0, 3], [3, 4], [4, 0]];
  return panels({
    points, edges: [...left, ...right], subgraphs: [[], left, right, [...left, ...right]],
    notes: ['the empty set', 'a cycle', 'a cycle', 'two cycles'],
    title: 'A graph of two triangles with one common vertex, drawn four times. The four even subgraphs are the empty set, the left triangle, the right triangle, and the two triangles together.',
  });
}

// Two triangles joined by one edge. P is the vertex set of the left triangle.
function outsideParts() {
  const points = [[20, 76], [47, 26], [74, 76], [94, 76], [121, 26], [148, 76]];
  const left = [[0, 1], [1, 2], [2, 0]], right = [[3, 4], [4, 5], [5, 3]];
  return panels({
    points, edges: [...left, ...right, [2, 3]], subgraphs: [[], left, right, [...left, ...right]],
    marked: [0, 1, 2],
    notes: ['outside part: empty', 'outside part: empty', 'outside part: a triangle', 'outside part: a triangle'],
    title: 'Two triangles joined by one edge, drawn four times. The set P is the left triangle. For the empty set and for the left triangle the outside part is empty. For the right triangle and for the two triangles together the outside part is the right triangle.',
  });
}

// A ring of four squares. The marked set P is the top square. One cycle goes around the ring.
function ringMarked() {
  const cx = 168, cy = 148, outer = 112, inner = 68, half = 0.34;
  const at = (angle, radius) => [cx + radius * Math.cos(angle), cy + radius * Math.sin(angle)];
  const tiles = [0, 1, 2, 3].map((i) => {
    const angle = -Math.PI / 2 + i * Math.PI / 2;
    return { a: at(angle - half, outer), b: at(angle - half, inner), c: at(angle + half, outer), d: at(angle + half, inner) };
  });
  const parts = [`<ellipse cx="${cx}" cy="${cy - (outer + inner) / 2}" rx="62" ry="40" class="fig-region"/>`];
  tiles.forEach((tile, i) => {
    const next = tiles[(i + 1) % 4];
    for (const [u, v] of [[tile.a, tile.c], [tile.a, tile.d], [tile.b, tile.c], [tile.b, tile.d], [tile.c, next.a], [tile.d, next.b]]) {
      parts.push(line(u, v, 'fig-edge'));
    }
  });
  const [t0, t1, t2, t3] = tiles;
  // The cycle: a0 d0 b0 c0 | a1 c1 | a2 d2 | b3 c3 | back to a0.
  for (const [u, v] of [[t0.a, t0.d], [t0.d, t0.b], [t0.b, t0.c], [t0.c, t1.a], [t3.c, t0.a]]) parts.push(line(u, v, 'fig-warm fig-dash'));
  for (const [u, v] of [[t1.a, t1.c], [t1.c, t2.a], [t2.a, t2.d], [t2.d, t3.b], [t3.b, t3.c]]) parts.push(line(u, v, 'fig-warm'));
  tiles.forEach((tile, i) => {
    for (const p of [tile.a, tile.b, tile.c, tile.d]) parts.push(node(p, i === 0 ? 'fig-node fig-node-marked' : 'fig-node'));
  });
  parts.push(label([cx - 84, cy - (outer + inner) / 2 - 22], 'P', 'fig-text fig-text-math'));
  return svg(336, 296, 'A ring of four squares. The marked set P is the top square. A cycle goes once around the ring. Its edges that touch P are dashed. Its other edges form a path.', parts.join(''));
}

// Two cycles, an edge between them, a component joined to both, and a component joined to one.
function links() {
  const parts = [];
  const c = [64, 78], d = [272, 78], radius = 44;
  parts.push('<ellipse cx="168" cy="124" rx="42" ry="17" class="fig-piece"/>', '<ellipse cx="64" cy="170" rx="34" ry="14" class="fig-piece"/>');
  parts.push(`<circle cx="${c[0]}" cy="${c[1]}" r="${radius}" class="fig-accent"/>`, `<circle cx="${d[0]}" cy="${d[1]}" r="${radius}" class="fig-accent"/>`);
  const onto = (centre, angle) => [centre[0] + radius * Math.cos(angle), centre[1] + radius * Math.sin(angle)];
  const e1 = onto(c, -0.45), e2 = onto(d, Math.PI + 0.45);
  parts.push(line(e1, e2, 'fig-warm'));
  const y1 = onto(c, 0.62), y2 = onto(d, Math.PI - 0.62), y3 = [132, 119], y4 = [204, 119];
  parts.push(line(y1, y3, 'fig-edge'), line(y2, y4, 'fig-edge'));
  const z1 = onto(c, Math.PI / 2), z2 = [64, 158];
  parts.push(line(z1, z2, 'fig-edge'));
  for (const p of [e1, e2, y1, y2, y3, y4, z1, z2]) parts.push(node(p, 'fig-node', 3.2));
  parts.push(label([64, 83], 'C', 'fig-text fig-text-math'), label([272, 83], 'C′', 'fig-text fig-text-math'));
  parts.push(label([168, 50], 'link', 'fig-text fig-text-warm'), label([168, 128], 'link', 'fig-text fig-text-warm'), label([104, 174], 'no link', 'fig-text fig-text-note', 'start'));
  return svg(336, 192, 'Two cycles C and C prime. One edge joins them, and one component of the rest of the graph is joined to both. These are two links. A third component is joined to C only, so it is not a link.', parts.join(''));
}

// A vertex of degree five becomes a path of three vertices.
function splitVertex() {
  const parts = [];
  const v = [50, 62];
  for (const end of [[10, 26], [10, 98]]) parts.push(line(v, end, 'fig-accent'));
  for (const end of [[60, 12], [100, 36], [100, 88]]) parts.push(line(v, end, 'fig-edge'));
  parts.push(node(v));
  parts.push(label([52, 84], 'v', 'fig-text fig-text-math'));
  parts.push(line([112, 62], [136, 62], 'fig-arrow'), '<path d="M142 62 l-9 -4.5 v9 z" class="fig-arrow-head"/>');
  const v1 = [190, 62], v2 = [244, 62], v3 = [298, 62];
  for (const end of [[154, 26], [154, 98]]) parts.push(line(v1, end, 'fig-accent'));
  parts.push(line(v1, v2, 'fig-warm'), line(v2, v3, 'fig-warm'));
  parts.push(line(v2, [244, 12], 'fig-edge'), line(v3, [330, 36], 'fig-edge'), line(v3, [330, 88], 'fig-edge'));
  parts.push(node(v1, 'fig-node fig-node-marked'), node(v2), node(v3));
  for (const [x, index] of [[190, 1], [244, 2], [298, 3]]) parts.push(label([x, 86], `v<tspan dy="-6" font-size="10.5">${index}</tspan>`, 'fig-text fig-text-math'));
  return svg(336, 110, 'Left: a vertex v of degree five on two edges of W. Right: a path of three vertices in the place of v. The two edges of W end at the first vertex of the path, and this vertex is put into P.', parts.join(''));
}

// A square with one diagonal. W is a triangle, and the cycle around the square has two edges in W.
function outsidePart() {
  const p = [[52, 34], [164, 34], [164, 146], [52, 146]];
  const parts = [line(p[0], p[2], 'fig-accent')];
  parts.push(line(p[0], p[1], 'fig-accent fig-thick'), line(p[1], p[2], 'fig-accent fig-thick'));
  parts.push(line(p[2], p[3], 'fig-warm'), line(p[3], p[0], 'fig-warm'));
  p.forEach((point) => parts.push(node(point, 'fig-node', 4)));
  const offsets = [[-14, -8], [14, -8], [14, 18], [-14, 18]];
  p.forEach((point, i) => parts.push(label([point[0] + offsets[i][0], point[1] + offsets[i][1]], String(i), 'fig-text fig-text-note')));
  parts.push(label([126, 76], 'W', 'fig-text fig-text-math'));
  return svg(216, 180, 'A square with the vertices 0, 1, 2 and 3 and the diagonal from 0 to 2. The subgraph W is the triangle 0, 1, 2. The cycle around the square has the two edges 0 to 1 and 1 to 2 in W. Its other two edges form a path from 2 through 3 to 0.', parts.join(''));
}

// The density at four ranks of the tower. Each bar is half of the bar before.
function tower() {
  const parts = [line([14, 122], [322, 122], 'fig-edge')];
  [96, 48, 24, 12].forEach((height, j) => {
    const x = 34 + j * 78;
    parts.push(`<rect x="${x}" y="${122 - height}" width="40" height="${height}" class="fig-bar"/>`);
    parts.push(label([x + 20, 142], `R<tspan dy="4" font-size="10.5">${j}</tspan>`, 'fig-text fig-text-math'));
  });
  return svg(336, 152, 'Four bars for the density at the ranks R0, R1, R2 and R3. Each bar is about half as high as the bar before it.', parts.join(''));
}

// A capped ladder: a chain of a square, a single rung and a square between the ends s and t.
function ladder() {
  const top = 34, bottom = 106, parts = [];
  const pair = (x) => [[x, top], [x, bottom]];
  const s = [16, 70], t = [320, 70];
  const [a, b, c, d, e] = [60, 114, 168, 222, 276].map(pair);
  const square = (left, right) => { for (const u of left) for (const w of right) parts.push(line(u, w, 'fig-accent')); };
  const join = (left, right) => { parts.push(line(left[0], right[0], 'fig-edge'), line(left[1], right[1], 'fig-edge')); };
  parts.push(line(s, a[0], 'fig-edge'), line(s, a[1], 'fig-edge'));
  square(a, b); join(b, c);
  parts.push(line(c[0], c[1], 'fig-warm'));
  join(c, d); square(d, e);
  parts.push(line(t, e[0], 'fig-edge'), line(t, e[1], 'fig-edge'));
  for (const p of [s, t, ...a, ...b, ...c, ...d, ...e]) parts.push(node(p));
  parts.push(label([16, 56], 's', 'fig-text fig-text-math'), label([320, 56], 't', 'fig-text fig-text-math'));
  parts.push(label([87, 130], 'square', 'fig-text fig-text-note'), label([168, 130], 'rung', 'fig-text fig-text-note'), label([249, 130], 'square', 'fig-text fig-text-note'));
  return svg(336, 138, 'A ladder between two ends s and t. It is a chain of a square, a single rung and a square. Two edges join each tile to the next tile.', parts.join(''));
}

// Two large pieces with small boundaries, away from the marked set P.
function pieces() {
  const parts = ['<rect x="4" y="8" width="328" height="150" class="fig-frame"/>'];
  parts.push('<ellipse cx="40" cy="84" rx="24" ry="19" class="fig-region"/>', label([40, 89], 'P', 'fig-text fig-text-math'));
  for (const cx of [136, 258]) {
    parts.push(`<ellipse cx="${cx}" cy="84" rx="50" ry="40" class="fig-piece"/>`, label([cx, 81], 'piece', 'fig-text fig-text-note'), label([cx, 99], 'at most 3/5', 'fig-text fig-text-warm'));
  }
  for (const [u, w] of [[[64, 84], [86, 84]], [[183, 70], [211, 70]], [[183, 98], [211, 98]], [[136, 44], [136, 22]], [[258, 124], [258, 146]], [[305, 70], [322, 58]]]) {
    parts.push(line(u, w, 'fig-edge'), node(u, 'fig-node', 3), node(w, 'fig-node', 3));
  }
  return svg(336, 166, 'A graph with a small marked set P and two large pieces. Few edges leave each piece. In each piece, at most three fifths of the possible edge sets are forests.', parts.join(''));
}

export const figures = {
  'even-subgraphs': evenSubgraphs,
  'outside-parts': outsideParts,
  'ring-marked': ringMarked,
  links,
  'split-vertex': splitVertex,
  'outside-part': outsidePart,
  tower,
  ladder,
  pieces,
};

const table = (head, rows) => `<table class="values"><thead><tr>${head.map((cell) => `<th scope="col">${cell}</th>`).join('')}</tr></thead><tbody>${rows.map((row) => `<tr>${row.map((cell) => `<td>${cell}</td>`).join('')}</tr>`).join('')}</tbody></table>`;

// The proportion q for a ring of k squares, where the marked set is one square.
function ringProportions() {
  const rows = [2, 3, 4, 5, 6].map((squares) => {
    const ring = ringGraph(squares);
    const marked = new Set([...ring.tiles[0].left, ...ring.tiles[0].right]);
    const atMarked = ring.edges.filter(([u, v]) => marked.has(u) || marked.has(v));
    const { favorable, total } = forestDistribution(ring.n, ring.edges, atMarked);
    return [squares, number(total), number(favorable), (favorable / total).toFixed(3)];
  });
  return `<div class="table-scroll">${table(['Squares', 'Even subgraphs', 'Outside part is a forest', '\\(q\\)'], rows)}</div>`;
}

// The largest n for each value of the iterated logarithm: 2, 4, 16, 65,536 and 2^65,536.
function logStarTable() {
  const rows = [2, 4, 16, 65536].map((n) => {
    if (logStar(n + 1) !== logStar(n) + 1) throw new Error(`${n} is not the largest number with its iterated logarithm`);
    return [number(n), logStar(n)];
  });
  rows.push(['\\(2^{65{,}536}\\)', logStar(65536) + 1]);
  return table(['\\(n\\)', '\\(\\log^{*} n\\)'], rows);
}

// The closing edges for 16 segments: the edge that closes j segments gives the cycle lengths j + 1 to 2^j + j.
function closingEdges() {
  const rows = [];
  for (let j = 16; ; j = Math.ceil(Math.log2(j))) {
    rows.push([j, `${number(j + 1)} to ${number(2 ** j + j)}`]);
    if (j === 2) break;
  }
  if (rows.length !== logStar(16)) throw new Error('The number of closing edges is the iterated logarithm');
  return table(['Segments', 'Cycle lengths'], rows);
}

// The two sides of the second-moment inequality with K = 2.
function momentTable() {
  const rows = [1, 10, 100].map((mu) => [mu, secondMomentBound(mu, 2).toFixed(3), (0.5 + 1 / (2 * mu)).toFixed(3)]);
  return table(['\\(\\mu\\)', 'Left side', 'Right side'], rows);
}

// The first term and the whole formula of Horak and Kim.
function formulaTable() {
  return table(['\\(r\\)', '\\(2^{r-1}\\)', '\\(H(r)\\)'], [9, 10, 20, 27].map((r) => [r, number(2 ** (r - 1)), number(horakKim(r))]));
}

export const tables = {
  'ring-proportions': ringProportions,
  logstar: logStarTable,
  'closing-edges': closingEdges,
  moment: momentTable,
  formula: formulaTable,
};
