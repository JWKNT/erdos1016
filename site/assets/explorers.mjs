import {
  edgeKey, enumerateSimpleCycles, cycleEdges, binaryConstruction, countSimpleCycles, horakKim, ringGraph,
} from './math-core.mjs?v=20261112-graphs';

const SVG_NS = 'http://www.w3.org/2000/svg';
const CYCLE_SIX = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]];

function element(tag, attributes = {}, text) {
  const node = document.createElement(tag);
  if (tag === 'select') node.setAttribute('data-ui-select', '');
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  if (text !== undefined) node.textContent = text;
  return node;
}
function svgElement(tag, attributes = {}, text) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
  if (text !== undefined) node.textContent = text;
  return node;
}
function svgFrame(width, height, title) {
  const svg = svgElement('svg', {
    viewBox: `0 0 ${width} ${height}`, role: 'img', 'aria-label': title,
    class: 'demo-svg', width, height,
  });
  svg.append(svgElement('title', {}, title));
  return svg;
}
function paragraph(className, text) { return element('p', { class: className }, text); }
// Readout markup: @x sets one italic variable; ^{…} and _{…} set scripts.
function richNodes(text) {
  const nodes = [];
  let plain = '';
  const flush = () => { if (plain) nodes.push(plain); plain = ''; };
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '@' && i + 1 < text.length) { flush(); nodes.push(element('var', {}, text[++i])); continue; }
    if ((ch === '^' || ch === '_') && text[i + 1] === '{') {
      let depth = 1, j = i + 2;
      for (; j < text.length && depth; j++) depth += text[j] === '{' ? 1 : text[j] === '}' ? -1 : 0;
      flush();
      const script = element(ch === '^' ? 'sup' : 'sub');
      script.append(...richNodes(text.slice(i + 2, j - 1)));
      nodes.push(script);
      i = j - 1;
      continue;
    }
    plain += ch;
  }
  flush();
  return nodes;
}
function rich(node, text) { node.replaceChildren(...richNodes(text)); }
function output(id) { return element('p', { class: 'demo-output', id, 'aria-live': 'polite', 'aria-atomic': 'true' }); }
function button(text, onClick, attributes = {}) {
  const node = element('button', { type: 'button', class: 'demo-button', ...attributes }, text);
  node.addEventListener('click', onClick);
  return node;
}
function control(labelText, input) {
  const wrapper = element('div', { class: 'demo-control' });
  wrapper.append(element('label', { for: input.id }, labelText), input);
  return wrapper;
}
function checkControl(id, labelText, onChange) {
  const input = element('input', { type: 'checkbox', id });
  input.addEventListener('change', onChange);
  const label = element('label', { class: 'demo-check', for: id });
  label.append(input, document.createTextNode(labelText));
  return { input, label };
}
function option(value, label) { return element('option', { value }, label); }
function markCurrent(buttons, value) {
  for (const [key, node] of buttons) node.setAttribute('aria-pressed', String(key === value));
}
function circlePoints(n, cx = 270, cy = 155, radius = 110) {
  return Array.from({ length: n }, (_, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / n;
    return [cx + radius * Math.cos(a), cy + radius * Math.sin(a)];
  });
}
function drawGraph(svg, points, edges, active = []) {
  const activeKeys = new Set(active.map(edgeKey));
  for (const [u, v] of edges) {
    const [x1, y1] = points[u], [x2, y2] = points[v];
    svg.append(svgElement('line', { x1, y1, x2, y2, class: `graph-edge${activeKeys.has(edgeKey([u, v])) ? ' graph-edge-active' : ''}` }));
  }
  points.forEach(([cx, cy], i) => {
    svg.append(svgElement('circle', { cx, cy, r: 15, class: 'graph-node' }));
    svg.append(svgElement('text', { x: cx, y: cy + 5, 'text-anchor': 'middle', class: 'graph-label' }, String(i)));
  });
}
function mountGraph(container) {
  const baseKeys = new Set(CYCLE_SIX.map(edgeKey));
  const chords = [];
  for (let u = 0; u < 6; u++) for (let v = u + 1; v < 6; v++) {
    if (!baseKeys.has(edgeKey([u, v]))) chords.push([u, v]);
  }
  const selected = new Set(['0-2', '0-3']);
  const toggles = new Map();
  const controls = element('fieldset', { class: 'demo-controls' });
  controls.append(element('legend', {}, 'Add edges to the cycle on six vertices'));
  const chordRow = element('div', { class: 'demo-button-row' });
  for (const edge of chords) {
    const key = edgeKey(edge);
    const toggle = button(`${edge[0]}–${edge[1]}`, () => {
      selected.has(key) ? selected.delete(key) : selected.add(key);
      refresh();
    }, { 'aria-pressed': String(selected.has(key)), 'aria-label': `Chord ${edge[0]}–${edge[1]}` });
    toggles.set(key, toggle);
    chordRow.append(toggle);
  }
  const presets = element('div', { class: 'demo-button-row' });
  presets.append(
    button('The cycle only', () => { selected.clear(); refresh(); }),
    button('All nine edges', () => { chords.forEach((edge) => selected.add(edgeKey(edge))); refresh(); }),
  );
  controls.append(chordRow, presets);
  const selectors = element('div', { class: 'demo-controls' });
  const lengthSelect = element('select', { id: 'graph-length' });
  const witnessSelect = element('select', { id: 'graph-witness' });
  selectors.append(control('Show a cycle of length', lengthSelect), control('Cycle', witnessSelect));
  const diagram = element('div', { class: 'demo-diagram' });
  const stats = output('graph-stats');
  const description = paragraph('demo-note', '');
  container.append(controls, selectors, diagram, stats, description);
  let edges = [], cycles = [], visibleCycles = [];
  function draw() {
    const cycle = visibleCycles[Number(witnessSelect.value)] || [];
    const length = cycle.length;
    const route = cycle.length ? [...cycle, cycle[0]].join(' → ') : 'none';
    const svg = svgFrame(540, 310, `Six-vertex graph. Highlighted ${length}-cycle: ${route}.`);
    drawGraph(svg, circlePoints(6), edges, cycle.length ? cycleEdges(cycle) : []);
    diagram.replaceChildren(svg);
    description.textContent = cycle.length ? `Shown: ${route}, one of ${visibleCycles.length} cycle${visibleCycles.length === 1 ? '' : 's'} of length ${length}.` : '';
  }
  function chooseLength() {
    visibleCycles = cycles.filter((cycle) => cycle.length === Number(lengthSelect.value));
    witnessSelect.replaceChildren(...visibleCycles.map((cycle, index) => option(index, `${index + 1}: ${[...cycle, cycle[0]].join(' → ')}`)));
    draw();
    globalThis.JehlpUI?.enhance(witnessSelect);
  }
  function refresh() {
    for (const [key, toggle] of toggles) toggle.setAttribute('aria-pressed', String(selected.has(key)));
    edges = [...CYCLE_SIX, ...chords.filter((edge) => selected.has(edgeKey(edge)))];
    cycles = enumerateSimpleCycles(6, edges);
    const lengths = [...new Set(cycles.map((cycle) => cycle.length))];
    const previousLength = Number(lengthSelect.value);
    lengthSelect.replaceChildren(...lengths.map((length) => option(length, `${length} edges`)));
    lengthSelect.value = String(lengths.includes(previousLength) ? previousLength : lengths[0]);
    globalThis.JehlpUI?.enhance(lengthSelect);
    const missing = [3, 4, 5, 6].filter((length) => !lengths.includes(length));
    stats.textContent = `${edges.length} edges. Cycle lengths: ${lengths.join(', ')}. ${missing.length ? `No cycle of length ${missing.join(' or ')}.` : 'The graph is pancyclic.'}`;
    chooseLength();
  }
  lengthSelect.addEventListener('change', chooseLength);
  witnessSelect.addEventListener('change', draw);
  refresh();
}

function mountBinary(container) {
  const controls = element('fieldset', { class: 'demo-controls' });
  controls.append(element('legend', {}, 'Shortcuts that the cycle takes'));
  const inputs = [1, 2, 4, 8].map((saving, i) => {
    const checkbox = checkControl(`binary-bit-${i}`, `Shortcut ${i + 1}: save ${saving} edge${saving === 1 ? '' : 's'}`, refresh);
    controls.append(checkbox.label);
    return checkbox.input;
  });
  const presets = element('div', { class: 'demo-button-row' });
  presets.append(button('No shortcut', () => { inputs.forEach((input) => { input.checked = false; }); refresh(); }),
    button('All shortcuts', () => { inputs.forEach((input) => { input.checked = true; }); refresh(); }));
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('binary-output');
  const lengths = element('div', { class: 'demo-button-row demo-length-strip', role: 'group', 'aria-label': 'Choose a cycle length from 5 to 20' });
  const lengthButtons = new Map();
  for (let length = 5; length <= 20; length++) {
    const choose = button(String(length), () => {
      const mask = 20 - length;
      inputs.forEach((input, i) => { input.checked = Boolean(mask & (2 ** i)); });
      refresh();
    }, { 'aria-label': `Make a cycle of length ${length}`, 'aria-pressed': 'false' });
    lengthButtons.set(length, choose);
    lengths.append(choose);
  }
  container.append(controls, presets, diagram, result, paragraph('demo-note', 'Or choose a cycle length.'), lengths);
  function refresh() {
    const mask = inputs.reduce((sum, input, i) => sum + (input.checked ? 2 ** i : 0), 0);
    const construction = binaryConstruction(4, mask);
    const svg = svgFrame(600, 305, `Four segments with shortcuts that save 1, 2, 4 and 8 edges. The chosen shortcuts save ${construction.saving}. The cycle length is ${construction.length}.`);
    for (const segment of construction.segments) {
      const start = 55 + segment.index * 120;
      const points = Array.from({ length: segment.originalLength + 1 }, (_, i) => {
        const t = i / segment.originalLength;
        return [start + 120 * t, 150 - 85 * Math.sin(Math.PI * t)];
      });
      svg.append(svgElement('text', { x: start + 60, y: 32, 'text-anchor': 'middle', class: 'graph-label' }, `${segment.originalLength} edges`));
      for (let i = 0; i < points.length - 1; i++) {
        svg.append(svgElement('line', { x1: points[i][0], y1: points[i][1], x2: points[i + 1][0], y2: points[i + 1][1], class: `graph-edge${segment.shortcut ? '' : ' graph-edge-active'}` }));
      }
      points.slice(1, -1).forEach(([cx, cy]) => svg.append(svgElement('circle', { cx, cy, r: 4, class: `graph-node${segment.shortcut ? ' graph-node-muted' : ''}` })));
      svg.append(svgElement('line', { x1: start, y1: 150, x2: start + 120, y2: 150,
        class: `graph-edge${segment.shortcut ? ' graph-edge-active' : ''}`, 'stroke-dasharray': segment.shortcut ? 'none' : '5 5' }));
      svg.append(svgElement('text', { x: start + 60, y: 178, 'text-anchor': 'middle', class: 'graph-label' }, `save ${segment.saving}`));
    }
    svg.append(svgElement('path', { d: 'M535 150 Q295 375 55 150', fill: 'none', class: 'graph-edge graph-edge-active' }));
    for (let i = 0; i <= 4; i++) svg.append(svgElement('circle', { cx: 55 + i * 120, cy: 150, r: 8, class: 'graph-node' }));
    svg.append(svgElement('text', { x: 295, y: 292, 'text-anchor': 'middle', class: 'graph-label' }, 'One closing edge'));
    diagram.replaceChildren(svg);
    const savings = construction.segments.filter((segment) => segment.shortcut).map((segment) => segment.saving);
    const total = savings.length ? `20 − (${savings.join(' + ')}) = ${construction.length}` : '20';
    result.textContent = `Cycle length ${total}.`;
    markCurrent(lengthButtons, construction.length);
  }
  refresh();
}

export function mountExplorers() {
  const demos = {
    'graph-demo': mountGraph,
    'binary-demo': mountBinary,
    'ring-demo': mountRing,
  };
  for (const [id, mount] of Object.entries(demos)) {
    const container = document.getElementById(id);
    if (!container || container.dataset.mounted === 'true') continue;
    mount(container);
    container.dataset.mounted = 'true';
    globalThis.JehlpUI?.enhance(container);
  }
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', mountExplorers, { once: true });
  else mountExplorers();
}

function mountRing(container) {
  const input = element('input', { type: 'range', id: 'ring-rank', min: '5', max: '14', step: '1', value: '9' });
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Rank r (5–14)', input));
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('ring-output');
  container.append(controls, diagram, result);
  function refresh() {
    const r = Number(input.value);
    const squares = Math.floor((r - 1) / 2), rungs = (r - 1) % 2;
    const ring = ringGraph(squares, rungs);
    const cycles = countSimpleCycles(ring.n, ring.edges);
    const tiles = `${squares} squares${rungs ? ' and one single rung' : ''}`;
    input.setAttribute('aria-valuetext', `Rank ${r}: ${tiles}, ${cycles} cycles`);
    const svg = svgFrame(300, 290, `A ring of ${tiles}. It has ${ring.n} vertices, rank ${r} and ${cycles} cycles.`);
    const count = ring.tiles.length, cx = 150, cy = 145, outer = 132, inner = 86;
    const at = (angle, radius) => [cx + radius * Math.cos(angle), cy + radius * Math.sin(angle)];
    const points = Array(ring.n);
    ring.tiles.forEach((tile, i) => {
      const angle = -Math.PI / 2 + i * 2 * Math.PI / count, half = 0.42 * Math.PI / count;
      if (tile.kind === 'square') {
        points[tile.left[0]] = at(angle - half, outer); points[tile.left[1]] = at(angle - half, inner);
        points[tile.right[0]] = at(angle + half, outer); points[tile.right[1]] = at(angle + half, inner);
      } else {
        points[tile.left[0]] = at(angle, outer); points[tile.left[1]] = at(angle, inner);
      }
    });
    const tileOf = Array(ring.n);
    ring.tiles.forEach((tile, i) => { for (const vertex of [...tile.left, ...tile.right]) tileOf[vertex] = i; });
    for (const [u, v] of ring.edges) {
      // An edge inside a tile belongs to a square or is the single rung. The other edges join two tiles.
      const kind = tileOf[u] !== tileOf[v] ? '' : ring.tiles[tileOf[u]].kind === 'square' ? ' ring-square' : ' ring-rung';
      svg.append(svgElement('line', { x1: points[u][0], y1: points[u][1], x2: points[v][0], y2: points[v][1], class: `graph-edge ring-edge${kind}` }));
    }
    points.forEach(([x, y]) => svg.append(svgElement('circle', { cx: x, cy: y, r: 4.5, class: 'graph-node' })));
    diagram.replaceChildren(svg);
    const formula = horakKim(r), half = 2 ** (r - 1);
    rich(result, `@r = ${r}: ${tiles}. Counted one by one, the ring has ${cycles.toLocaleString('en-US')} cycles, and @H(${r}) = ${formula.toLocaleString('en-US')}. The first term is 2^{${r - 1}} = ${half.toLocaleString('en-US')}.`);
  }
  input.addEventListener('input', refresh);
  refresh();
}
