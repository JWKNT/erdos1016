import {
  edgeKey, graphStats, edgeDegrees, enumerateSimpleCycles, cycleEdges,
  cycleBasis, xorEdgeSets, isSimpleCycle, isEvenEdgeSet, isForest, forestDistribution,
  binaryConstruction, logStarSteps, secondMomentBound, idealizedRecurrence,
  thetaCutDistribution, analyzeWalk,
} from './math-core.mjs';

const SVG_NS = 'http://www.w3.org/2000/svg';
const CYCLE_SIX = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]];
const BOW_TIE = [[0, 1], [1, 2], [2, 0], [0, 3], [3, 4], [4, 0]];
const BRIDGE_GRAPH = [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3], [2, 3]];
const LEFT_CYCLE = [[0, 1], [1, 2], [2, 0]];

function element(tag, attributes = {}, text) {
  const node = document.createElement(tag);
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
function edgeList(edges) { return edges.length ? edges.map(([u, v]) => `${u}–${v}`).join(', ') : '∅'; }
function fraction(denominator) { return denominator === 1 ? '1' : `1/${denominator}`; }
function numberText(value) {
  if (value === 0) return '0';
  return Math.abs(value) >= 1e8 || Math.abs(value) < 0.0001
    ? value.toExponential(4).replace(/\.0+(?=e)/, '')
    : Number(value.toPrecision(6)).toLocaleString('en-US', { maximumFractionDigits: 6 });
}
// Preserve the represented input: rounding across a tower threshold can make
// a correct log-star result appear to contradict its displayed argument.
function inputNumberText(value) {
  return value >= 1e8 || value < 0.0001
    ? value.toExponential()
    : value.toLocaleString('en-US', { maximumSignificantDigits: 21 });
}
function circlePoints(n, cx = 270, cy = 155, radius = 110) {
  return Array.from({ length: n }, (_, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / n;
    return [cx + radius * Math.cos(a), cy + radius * Math.sin(a)];
  });
}
function drawGraph(svg, points, edges, { active = [], witness = [], outside = [], mutedNodes = false } = {}) {
  const activeKeys = new Set(active.map(edgeKey));
  const witnessKeys = new Set(witness.map(edgeKey));
  const outsideKeys = new Set(outside.map(edgeKey));
  for (const [u, v] of edges) {
    const [x1, y1] = points[u], [x2, y2] = points[v];
    const key = edgeKey([u, v]);
    svg.append(svgElement('line', { x1, y1, x2, y2, class: 'graph-edge' }));
    if (witnessKeys.has(key)) svg.append(svgElement('line', {
      x1, y1, x2, y2, class: 'graph-edge graph-edge-witness', 'stroke-dasharray': '9 6',
    }));
    if (activeKeys.has(key)) svg.append(svgElement('line', {
      x1, y1, x2, y2, class: `graph-edge graph-edge-active${outsideKeys.has(key) ? ' graph-edge-outside' : ''}`,
    }));
  }
  points.forEach(([cx, cy], i) => {
    const used = active.some(([u, v]) => u === i || v === i);
    svg.append(svgElement('circle', { cx, cy, r: 15, class: `graph-node${mutedNodes && !used ? ' graph-node-muted' : ''}` }));
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
  controls.append(element('legend', {}, 'Choose chords for the fixed six-cycle'));
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
    button('Cycle only', () => { selected.clear(); refresh(); }),
    button('Complete graph K₆', () => { chords.forEach((edge) => selected.add(edgeKey(edge))); refresh(); }),
  );
  controls.append(chordRow, presets);
  const selectors = element('div', { class: 'demo-controls' });
  const lengthSelect = element('select', { id: 'graph-length' });
  const witnessSelect = element('select', { id: 'graph-witness' });
  selectors.append(control('Highlight a cycle length', lengthSelect), control('Choose a cycle of that length', witnessSelect));
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
    drawGraph(svg, circlePoints(6), edges, { active: cycle.length ? cycleEdges(cycle) : [] });
    diagram.replaceChildren(svg);
    description.textContent = `Highlighted cycle: ${route}. The graph has ${visibleCycles.length} distinct cycle${visibleCycles.length === 1 ? '' : 's'} with length ${length}. The six outer edges always remain in the graph.`;
  }
  function chooseLength() {
    visibleCycles = cycles.filter((cycle) => cycle.length === Number(lengthSelect.value));
    witnessSelect.replaceChildren(...visibleCycles.map((cycle, index) => option(index, `${index + 1}: ${[...cycle, cycle[0]].join(' → ')}`)));
    draw();
  }
  function refresh() {
    for (const [key, toggle] of toggles) toggle.setAttribute('aria-pressed', String(selected.has(key)));
    edges = [...CYCLE_SIX, ...chords.filter((edge) => selected.has(edgeKey(edge)))];
    cycles = enumerateSimpleCycles(6, edges);
    const lengths = [...new Set(cycles.map((cycle) => cycle.length))];
    const previousLength = Number(lengthSelect.value);
    lengthSelect.replaceChildren(...lengths.map((length) => option(length, `${length} edges`)));
    lengthSelect.value = String(lengths.includes(previousLength) ? previousLength : lengths[0]);
    const missing = [3, 4, 5, 6].filter((length) => !lengths.includes(length));
    const { edges: m, rank, excess } = graphStats(6, edges);
    stats.textContent = `${m} edges · excess m − n = ${excess}. Cycle-space dimension r = ${rank} (see chapter 3). ${cycles.length} simple cycles; ${lengths.length} distinct cycle lengths: ${lengths.join(', ')}. Missing lengths from 3–6: ${missing.length ? missing.join(', ') : 'none'}. ${lengths.length === 4 ? 'This graph is pancyclic.' : 'This graph is not pancyclic.'}`;
    chooseLength();
  }
  lengthSelect.addEventListener('change', chooseLength);
  witnessSelect.addEventListener('change', draw);
  refresh();
}

function mountSpace(container) {
  const basis = cycleBasis(5, BOW_TIE);
  const controls = element('fieldset', { class: 'demo-controls' });
  controls.append(element('legend', {}, 'Choose basis cycles for XOR'));
  const inputs = basis.map((_, i) => {
    const checkbox = checkControl(`space-bit-${i}`, `C${i + 1}: triangle ${i === 0 ? '0–1–2' : '0–3–4'}`, refresh);
    controls.append(checkbox.label);
    return checkbox.input;
  });
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('space-output');
  const degrees = paragraph('demo-note', '');
  container.append(controls, diagram, result, degrees);
  function refresh() {
    const word = xorEdgeSets(...basis.filter((_, i) => inputs[i].checked));
    const bits = inputs.map((input) => Number(input.checked)).join('');
    const selectedNames = inputs.flatMap((input, i) => input.checked ? [`C${i + 1}`] : []);
    const name = selectedNames.length ? selectedNames.join(' XOR ') : '∅';
    const svg = svgFrame(540, 290, `Basis choice ${bits}: ${name}. Selected edges: ${edgeList(word)}.`);
    drawGraph(svg, [[270, 145], [90, 55], [90, 235], [450, 55], [450, 235]], BOW_TIE, { active: word });
    diagram.replaceChildren(svg);
    const kind = !word.length ? 'The empty edge set is even. It is not a simple cycle.'
      : isSimpleCycle(5, word) ? 'This even edge set is one simple cycle.'
      : 'This even edge set is not one simple cycle. Vertex 0 has degree 4.';
    result.textContent = `Basis bits ${bits}: ${name}. ${word.length} selected edges. ${kind}`;
    degrees.textContent = `Degrees at vertices 0–4: ${edgeDegrees(5, word).join(', ')}. Every degree is even. Here r = 6 − 5 + 1 = 2. Thus, there are 2² = 4 even edge sets.`;
  }
  inputs[0].checked = true;
  inputs[1].checked = true;
  refresh();
}

function mountForest(container) {
  const distribution = forestDistribution(6, BRIDGE_GRAPH, LEFT_CYCLE);
  const names = ['∅', 'W (left triangle)', 'D (right triangle)', 'W XOR D (both triangles)'];
  const select = element('select', { id: 'forest-word' });
  select.append(...names.map((name, i) => option(i, name)));
  const controls = element('div', { class: 'demo-controls' });
  const nav = element('div', { class: 'demo-button-row' });
  nav.append(button('Previous set', () => { select.value = String((Number(select.value) + 3) % 4); refresh(); }),
    button('Next set', () => { select.value = String((Number(select.value) + 1) % 4); refresh(); }));
  controls.append(control('Choose one of the four equally likely even edge sets', select), nav);
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('forest-output');
  const summary = paragraph('demo-note', `Exactly ${distribution.favorable} of ${distribution.total} ambient even edge sets give a forest outside W. The probability is 2/4 = 1/2. The bridge 2–3 never appears in an even edge set.`);
  container.append(controls, diagram, result, summary);
  function refresh() {
    const index = Number(select.value);
    const { word, outside, forest } = distribution.words[index];
    const svg = svgFrame(720, 235, `${names[index]}. Outside W, ${outside.length ? 'the right triangle remains. It is not a forest' : 'the empty edge set remains. It is a forest'}.`);
    svg.append(svgElement('text', { x: 180, y: 26, 'text-anchor': 'middle', class: 'graph-label' }, 'Selected even edge set'));
    svg.append(svgElement('text', { x: 540, y: 26, 'text-anchor': 'middle', class: 'graph-label' }, 'Outside W: remove its edges'));
    const points = [[48, 156], [103, 68], [158, 156], [203, 156], [258, 68], [313, 156]];
    drawGraph(svg, points, BRIDGE_GRAPH, { active: word, witness: LEFT_CYCLE, outside });
    drawGraph(svg, points.map(([x, y]) => [x + 360, y]), outside, { active: outside, outside, mutedNodes: true });
    svg.append(svgElement('text', { x: 180, y: 210, 'text-anchor': 'middle', class: 'graph-label' }, 'Dashed outline = fixed witness W'));
    svg.append(svgElement('text', { x: 540, y: 210, 'text-anchor': 'middle', class: 'graph-label' }, forest ? 'FOREST (empty edge set)' : 'NOT A FOREST (cycle D)'));
    diagram.replaceChildren(svg);
    result.textContent = `Set ${index + 1} of 4: ${names[index]}. Outside edges: ${edgeList(outside)}. ${forest ? 'A forest remains.' : 'A cycle remains. The remaining edges do not form a forest.'}`;
  }
  select.addEventListener('change', refresh);
  refresh();
}

function mountBinary(container) {
  const controls = element('fieldset', { class: 'demo-controls' });
  controls.append(element('legend', {}, 'Replace long paths with shortcuts'));
  const inputs = [1, 2, 4, 8].map((saving, i) => {
    const checkbox = checkControl(`binary-bit-${i}`, `Shortcut ${i + 1}: save ${saving} edge${saving === 1 ? '' : 's'}`, refresh);
    controls.append(checkbox.label);
    return checkbox.input;
  });
  const presets = element('div', { class: 'demo-button-row' });
  presets.append(button('Use all long paths', () => { inputs.forEach((input) => { input.checked = false; }); refresh(); }),
    button('Use all shortcuts', () => { inputs.forEach((input) => { input.checked = true; }); refresh(); }));
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
  container.append(controls, presets, diagram, result, paragraph('demo-note', 'Choose a cycle length. The sums of binary savings give each integer from 0 to 15 exactly once.'), lengths);
  function refresh() {
    const mask = inputs.reduce((sum, input, i) => sum + (input.checked ? 2 ** i : 0), 0);
    const construction = binaryConstruction(4, mask);
    const svg = svgFrame(600, 305, `Four paths with shortcut savings 1, 2, 4, and 8. Chosen savings ${construction.saving}; cycle length ${construction.length}.`);
    for (const segment of construction.segments) {
      const start = 55 + segment.index * 120;
      const points = Array.from({ length: segment.originalLength + 1 }, (_, i) => {
        const t = i / segment.originalLength;
        return [start + 120 * t, 150 - 85 * Math.sin(Math.PI * t)];
      });
      svg.append(svgElement('text', { x: start + 60, y: 32, 'text-anchor': 'middle', class: 'graph-label' }, `${segment.originalLength}-edge path`));
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
    result.textContent = `Cycle length = 20 − (${savings.length ? savings.join(' + ') : '0'}) = ${construction.length}. ${construction.saving} edges saved. Available lengths: ${construction.min}–${construction.max}.`;
    markCurrent(lengthButtons, construction.length);
  }
  refresh();
}

function mountLogStar(container) {
  const input = element('input', { type: 'number', id: 'logstar-number', min: '0', step: 'any', value: '1000000000', inputmode: 'decimal', 'aria-describedby': 'logstar-note' });
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Positive number n (decimal or scientific notation)', input));
  const presets = element('div', { class: 'demo-button-row', role: 'group', 'aria-label': 'Log-star threshold examples' });
  [['1', '1'], ['2', '2'], ['4', '4'], ['16', '16'], ['65536', '65,536'], ['65537', '65,537'], ['1e100', '10¹⁰⁰']].forEach(([value, label]) => {
    presets.append(button(label, () => { input.value = value; refresh(); }));
  });
  controls.append(presets);
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('logstar-output');
  const steps = paragraph('demo-note', '');
  const note = paragraph('demo-note', 'Use base 2. If the value is at most 1, stop. Threshold classification is exact for the finite number that the input represents. The display rounds the logarithms.');
  note.id = 'logstar-note';
  container.append(controls, diagram, result, steps, note);
  function refresh() {
    const n = input.valueAsNumber;
    if (!Number.isFinite(n) || n <= 0) {
      input.setAttribute('aria-invalid', 'true');
      result.textContent = 'Enter a finite number greater than 0.';
      steps.textContent = '';
      diagram.replaceChildren();
      return;
    }
    input.removeAttribute('aria-invalid');
    const { count, values, roundedBoundary } = logStarSteps(n);
    const displayedInput = inputNumberText(n);
    const thresholds = ['1', '2', '4', '16', '65,536', '2^65,536'];
    const svg = svgFrame(620, 275, `Log-star threshold staircase. log-star of ${displayedInput} equals ${count}. Thresholds: 1, 2, 4, 16, 65536, and 2 to the 65536.`);
    for (let i = 0; i <= 5; i++) {
      const x = 55 + i * 102, y = 215 - i * 30;
      if (i < 5) svg.append(svgElement('path', { d: `M${x} ${y} H${x + 102} V${y - 30}`, fill: 'none', class: 'plot-line' }));
      svg.append(svgElement('circle', { cx: x, cy: y, r: i === count ? 10 : 5, class: i === count ? 'plot-point' : 'graph-node' }));
      svg.append(svgElement('text', { x, y: y - 17, 'text-anchor': 'middle', class: 'graph-label' }, `T${i} = ${thresholds[i]}`));
      svg.append(svgElement('text', { x, y: 253, 'text-anchor': 'middle', class: 'graph-label' }, `${i} logs`));
    }
    diagram.replaceChildren(svg);
    result.textContent = `log*₂(${displayedInput}) = ${count}. ${count ? `${count} repeated base-2 logarithm${count === 1 ? '' : 's'} ${count === 1 ? 'reduces' : 'reduce'} n to at most 1.` : 'n is at most 1. The calculation needs no logarithms.'}`;
    steps.textContent = `${count ? `Successive values (logarithms rounded): ${displayedInput} → ${values.slice(1).map(numberText).join(' → ')}` : `Starting value: ${displayedInput}`}${roundedBoundary ? '. At a boundary, rounding can change the displayed iteration. The exact threshold determines the answer' : ''}${count === 5 ? '. The next threshold, 2^65,536, is larger than every finite JavaScript number' : ''}.`;
  }
  input.addEventListener('input', refresh);
  refresh();
}

function mountMoment(container) {
  const input = element('input', { type: 'range', id: 'moment-mu', min: '1', max: '100', step: '1', value: '10' });
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Mean μ (1–100), with K = 1', input));
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('moment-output');
  container.append(controls, diagram, result, paragraph('demo-note', 'If E[Z²] ≤ 2μ² + μ, this formula gives an upper bound on P(Z = 0). This bound is not an empirical probability. This example does not establish the hypothesis for every graph.'));
  function refresh() {
    const mu = Number(input.value), bound = secondMomentBound(mu);
    input.setAttribute('aria-valuetext', `Mean ${mu}, probability upper bound ${(100 * bound).toFixed(2)} percent`);
    const svg = svgFrame(620, 300, `Second-moment upper bound 1/2 + 1/(4μ + 2). At mean ${mu}, the bound is ${bound.toFixed(6)}.`);
    const x = (value) => 66 + (value - 1) / 99 * 518;
    const y = (value) => 236 - (value - 0.5) / 0.2 * 195;
    svg.append(svgElement('path', { d: 'M66 30 V236 H590', fill: 'none', class: 'plot-axis' }));
    for (const value of [0.5, 0.6, 0.7]) {
      svg.append(svgElement('line', { x1: 66, y1: y(value), x2: 590, y2: y(value), class: 'plot-grid', 'stroke-dasharray': value === 0.5 ? '7 5' : '2 5' }));
      svg.append(svgElement('text', { x: 53, y: y(value) + 5, 'text-anchor': 'end', class: 'graph-label' }, value.toFixed(2)));
    }
    for (const value of [1, 25, 50, 75, 100]) {
      svg.append(svgElement('text', { x: x(value), y: 260, 'text-anchor': 'middle', class: 'graph-label' }, String(value)));
    }
    const points = Array.from({ length: 199 }, (_, i) => {
      const value = 1 + i * 0.5;
      return `${x(value)},${y(secondMomentBound(value))}`;
    }).join(' ');
    svg.append(svgElement('polyline', { points, fill: 'none', class: 'plot-line' }));
    svg.append(svgElement('line', { x1: x(mu), y1: y(bound), x2: x(mu), y2: 236, class: 'plot-grid', 'stroke-dasharray': '4 4' }));
    svg.append(svgElement('circle', { cx: x(mu), cy: y(bound), r: 7, class: 'plot-point' }));
    svg.append(svgElement('text', { x: 66, y: 18, class: 'graph-label' }, 'Upper bound on P(Z = 0)'));
    svg.append(svgElement('text', { x: 325, y: 289, 'text-anchor': 'middle', class: 'graph-label' }, 'Mean μ'));
    diagram.replaceChildren(svg);
    result.textContent = `μ = ${mu}: P(Z = 0) ≤ 1/2 + 1/${4 * mu + 2} = ${bound.toFixed(6)} (${(100 * bound).toFixed(2)}%). The excess above 1/2 is ${(bound - 0.5).toFixed(6)}.`;
  }
  input.addEventListener('input', refresh);
  refresh();
}

function mountRecurrence(container) {
  const input = element('input', { type: 'range', id: 'recurrence-steps', min: '0', max: '8', step: '1', value: '3' });
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Number of idealized halving steps j (0–8)', input));
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('recurrence-output');
  container.append(controls, diagram, result, paragraph('demo-note', 'This idealized model starts at Φmodel = 1. Each step halves this value exactly and adds one level to a tower-height proxy. The theorem includes error terms and requires a sufficiently large initial rank. This diagram does not give a numerical bound for finite n.'));
  function refresh() {
    const model = idealizedRecurrence(Number(input.value));
    input.setAttribute('aria-valuetext', `${model.steps} steps, idealized density ${fraction(model.denominator)}, tower-height increment ${model.steps}`);
    const svg = svgFrame(620, 300, `Idealized near-halving illustration. At step ${model.steps}, model density is ${fraction(model.denominator)}. The tower-height proxy has increased by ${model.steps}.`);
    const x = (j) => 85 + j * 61;
    const y = (j) => 42 + j * 23;
    svg.append(svgElement('path', { d: 'M85 30 V241 H590', fill: 'none', class: 'plot-axis' }));
    for (let j = 0; j <= 8; j++) {
      if (j % 2 === 0) {
        svg.append(svgElement('line', { x1: 85, y1: y(j), x2: 585, y2: y(j), class: 'plot-grid', 'stroke-dasharray': '2 5' }));
        svg.append(svgElement('text', { x: 72, y: y(j) + 5, 'text-anchor': 'end', class: 'graph-label' }, fraction(2 ** j)));
      }
      svg.append(svgElement('text', { x: x(j), y: 260, 'text-anchor': 'middle', class: 'graph-label' }, String(j)));
    }
    svg.append(svgElement('line', { x1: x(0), y1: y(0), x2: x(8), y2: y(8), class: 'plot-line' }));
    for (let j = 0; j <= 8; j++) svg.append(svgElement('circle', { cx: x(j), cy: y(j), r: j === model.steps ? 9 : 4, class: j === model.steps ? 'plot-point' : 'graph-node' }));
    svg.append(svgElement('text', { x: 85, y: 18, class: 'graph-label' }, 'Idealized density (logarithmic spacing)'));
    svg.append(svgElement('text', { x: 335, y: 290, 'text-anchor': 'middle', class: 'graph-label' }, 'Halving steps = added tower levels'));
    diagram.replaceChildren(svg);
    result.textContent = `j = ${model.steps}: Φmodel = 2^−${model.steps} = ${fraction(model.denominator)} = ${numberText(model.phi)}. Tower-height proxy: +${model.towerLevelIncrement} level${model.towerLevelIncrement === 1 ? '' : 's'}. In this idealized model, each extra factor 1/2 requires another exponentiation step.`;
  }
  input.addEventListener('input', refresh);
  refresh();
}

/** Mount once per container; importing this module in Node is safe. */
export function mountExplorers() {
  const demos = {
    'graph-demo': mountGraph,
    'space-demo': mountSpace,
    'forest-demo': mountForest,
    'binary-demo': mountBinary,
    'logstar-demo': mountLogStar,
    'moment-demo': mountMoment,
    'recurrence-demo': mountRecurrence,
    'cut-demo': mountCut,
    'walk-demo': mountWalk,
    'restriction-demo': mountRestriction,
  };
  for (const [id, mount] of Object.entries(demos)) {
    const container = document.getElementById(id);
    if (!container || container.dataset.mounted === 'true') continue;
    mount(container);
    container.dataset.mounted = 'true';
  }
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', mountExplorers, { once: true });
  else mountExplorers();
}

function mountCut(container) {
  const select = element('select', { id: 'cut-links' });
  select.append(...[1, 2, 3, 4].map((links) => option(links, `${links} link${links === 1 ? '' : 's'}`)));
  select.value = '3';
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Number ℓ of internally disjoint A–B paths', select));
  const choices = element('div', { class: 'demo-button-row', role: 'group', 'aria-label': 'Choose an ambient even edge set' });
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('cut-output');
  const probabilities = paragraph('demo-note', '');
  probabilities.id = 'cut-probabilities';
  container.append(controls, choices, diagram, result, probabilities,
    paragraph('demo-note', 'Each path has two edges. Without A and B, ℓ separate link vertices remain. An even edge set contains an even number of complete paths. In this family, either zero-cut event requires the empty edge set. Thus, the two events coincide.'));
  let distribution, selected = 0;
  const buttons = new Map();
  function draw() {
    const { links, total } = distribution;
    const chosen = distribution.words[selected];
    const points = [[80, 155], [540, 155], ...Array.from({ length: links }, (_, i) => [310, links === 1 ? 155 : 50 + i * 210 / (links - 1)])];
    const svg = svgFrame(620, 325, `${links} links connect region A (vertex 0) to region B (vertex 1). Selected paths: ${chosen.selectedPaths.length ? chosen.selectedPaths.map((p) => p + 1).join(', ') : 'none'}. Cut A is ${chosen.zeroA ? 'zero' : 'nonzero'}. Cut B is ${chosen.zeroB ? 'zero' : 'nonzero'}.`);
    svg.append(svgElement('circle', { cx: 80, cy: 155, r: 34, fill: 'none', class: 'graph-region', 'stroke-dasharray': '6 5' }));
    svg.append(svgElement('circle', { cx: 540, cy: 155, r: 34, fill: 'none', class: 'graph-region', 'stroke-dasharray': '6 5' }));
    drawGraph(svg, points, distribution.edges, { active: chosen.word });
    svg.append(svgElement('text', { x: 80, y: 210, 'text-anchor': 'middle', class: 'graph-label' }, 'A = {0}'));
    svg.append(svgElement('text', { x: 540, y: 210, 'text-anchor': 'middle', class: 'graph-label' }, 'B = {1}'));
    points.slice(2).forEach(([x, y], i) => svg.append(svgElement('text', { x: x + 25, y: y + 5, class: 'graph-label' }, `path ${i + 1}`)));
    svg.append(svgElement('text', { x: 310, y: 312, 'text-anchor': 'middle', class: 'graph-label' }, `${total} equally likely even edge set${total === 1 ? '' : 's'}`));
    diagram.replaceChildren(svg);
    const paths = chosen.selectedPaths.length ? chosen.selectedPaths.map((p) => p + 1).join(' + ') : 'none';
    result.textContent = `Selected paths: ${paths}. δA = 0: ${chosen.zeroA ? 'yes' : 'no'}. δB = 0: ${chosen.zeroB ? 'yes' : 'no'}. Selected edges: ${edgeList(chosen.word)}.`;
    probabilities.textContent = `Exact enumeration: P(δA = 0) = ${distribution.countA}/${total}. P(δB = 0) = ${distribution.countB}/${total}. P(both) = ${distribution.countBoth}/${total}. Joint probability ÷ product of marginals = ${distribution.correlationRatio} = 2^(${links} − 1).`;
    markCurrent(buttons, selected);
  }
  function refresh() {
    distribution = thetaCutDistribution(Number(select.value));
    selected = 0;
    choices.replaceChildren();
    buttons.clear();
    distribution.words.forEach(({ selectedPaths }, index) => {
      const label = selectedPaths.length ? `Paths ${selectedPaths.map((p) => p + 1).join(' + ')}` : 'Empty set ∅';
      const choose = button(label, () => { selected = index; draw(); }, { 'aria-pressed': String(index === selected) });
      choices.append(choose);
      buttons.set(index, choose);
    });
    draw();
  }
  select.addEventListener('change', refresh);
  refresh();
}

function mountWalk(container) {
  const examples = [
    { id: 'figure-eight', label: 'Figure-eight: repeated vertex, no reversal', vertices: [0, 1, 2, 0, 3, 4, 0] },
    { id: 'triangle', label: 'Triangle: a simple cycle', vertices: [0, 1, 2, 0] },
    { id: 'backtracking', label: 'Immediate backtracking: 0 → 1 → 0', vertices: [0, 1, 0, 3, 4, 0] },
    { id: 'seam', label: 'Reversal only at closure', vertices: [1, 0, 3, 4, 0, 1] },
  ];
  const select = element('select', { id: 'walk-example' });
  select.append(...examples.map(({ id, label }) => option(id, label)));
  const controls = element('div', { class: 'demo-controls' });
  controls.append(control('Choose a closed walk', select));
  const nav = element('div', { class: 'demo-button-row' });
  let step = 0;
  const previous = button('Previous step', () => { if (step > 0) { step--; draw(); } });
  const next = button('Next step', () => { if (step < model.length) { step++; draw(); } });
  nav.append(previous, next, button('Restart', () => { step = 0; draw(); }), button('Show whole walk', () => { step = model.length; draw(); }));
  controls.append(nav);
  const diagram = element('div', { class: 'demo-diagram' });
  const result = output('walk-output');
  const verdict = paragraph('demo-note', '');
  verdict.id = 'walk-verdict';
  container.append(controls, diagram, result, verdict,
    paragraph('demo-note', 'Use the buttons to advance the walk. A solid outer ring marks the current vertex. A dashed ring marks an interior revisit. This example has a degree-4 center and differs from the retained cubic graph J in the proof. A trace counts closed nonbacktracking walks. Further analysis must identify the simple cycles.'));
  let example = examples[0], model = analyzeWalk(5, BOW_TIE, example.vertices);
  function draw() {
    const prefix = example.vertices.slice(0, step + 1);
    const visitedEdges = prefix.slice(1).map((v, i) => [prefix[i], v]);
    const points = [[270, 145], [90, 55], [90, 235], [450, 55], [450, 235]];
    const current = prefix[prefix.length - 1];
    const svg = svgFrame(540, 290, `Walk step ${step} of ${model.length}: ${prefix.join(' to ')}. Current vertex ${current}. The complete walk is ${model.cyclicallyNonbacktracking ? '' : 'not '}cyclically nonbacktracking. It is ${model.simpleCycle ? '' : 'not '}a simple cycle.`);
    drawGraph(svg, points, BOW_TIE, { active: visitedEdges });
    const interiorPrefix = step === model.length ? prefix.slice(0, -1) : prefix;
    const repeated = [...new Set(interiorPrefix)].filter((v) => interiorPrefix.filter((candidate) => candidate === v).length > 1);
    repeated.forEach((v) => svg.append(svgElement('circle', { cx: points[v][0], cy: points[v][1], r: 28, fill: 'none', class: 'graph-node-repeated', 'stroke-dasharray': '5 4' })));
    svg.append(svgElement('circle', { cx: points[current][0], cy: points[current][1], r: 21, fill: 'none', class: 'walk-current' }));
    if (step > 0) {
      const defs = svgElement('defs');
      const marker = svgElement('marker', { id: 'walk-arrowhead', viewBox: '0 0 8 8', refX: '7', refY: '4', markerWidth: '7', markerHeight: '7', orient: 'auto' });
      marker.append(svgElement('path', { d: 'M0 0 L8 4 L0 8 Z', class: 'walk-arrow' }));
      defs.append(marker); svg.append(defs);
      const [sx, sy] = points[prefix[prefix.length - 2]], [ex, ey] = points[current];
      const distance = Math.hypot(ex - sx, ey - sy), dx = (ex - sx) / distance, dy = (ey - sy) / distance;
      svg.append(svgElement('line', { x1: sx + 32 * dx, y1: sy + 32 * dy, x2: ex - 34 * dx, y2: ey - 34 * dy, class: 'graph-edge graph-edge-active', 'marker-end': 'url(#walk-arrowhead)' }));
    }
    diagram.replaceChildren(svg);
    previous.disabled = step === 0;
    next.disabled = step === model.length;
    const reversal = step >= 2 && prefix[step] === prefix[step - 2];
    const arrival = step === model.length ? 'The walk has returned to its initial vertex.'
      : step && prefix.slice(0, -1).includes(current) ? `The walk has visited vertex ${current} before.` : `Current vertex: ${current}.`;
    result.textContent = `Step ${step}/${model.length}: ${prefix.join(' → ')}. ${arrival}${reversal ? ' This step immediately reverses the previous edge.' : ''}${step === model.length && model.closureBacktracks ? ' At closure, the final edge and the first edge reverse one another.' : ''}`;
    verdict.textContent = `Complete walk: closed = ${model.closed ? 'yes' : 'no'}. No immediate reversal inside the written sequence = ${model.nonbacktracking ? 'yes' : 'no'}. No reversal at closure = ${model.closureBacktracks ? 'no' : 'yes'}. Cyclically nonbacktracking = ${model.cyclicallyNonbacktracking ? 'yes' : 'no'}. Simple cycle = ${model.simpleCycle ? 'yes' : 'no'}.${model.repeatedVertices.length ? ` Interior repeated vertices: ${model.repeatedVertices.join(', ')}.` : ' No interior vertex repeats.'}`;
  }
  select.addEventListener('change', () => {
    example = examples.find(({ id }) => id === select.value);
    model = analyzeWalk(5, BOW_TIE, example.vertices);
    step = 0;
    draw();
  });
  draw();
}

function mountRestriction(container) {
  const first = [[0, 1], [1, 2], [2, 0]];
  const second = [[0, 2], [2, 3], [3, 0]];
  const ambient = [[0, 1], [1, 2], [2, 3], [3, 0], [0, 2]];
  const witnessKeys = new Set(first.map(edgeKey));
  const controls = element('fieldset', { class: 'demo-controls' });
  controls.append(element('legend', {}, 'Combine two cycles. Then restrict the edge set.'));
  const firstControl = checkControl('restriction-first', 'Triangle 0–1–2', refresh);
  const secondControl = checkControl('restriction-second', 'Triangle 0–2–3', refresh);
  const removeControl = checkControl('restriction-remove', 'Remove witness W = triangle 0–1–2', refresh);
  const inputs = [firstControl.input, secondControl.input, removeControl.input];
  inputs.forEach((input) => { input.checked = true; });
  controls.append(firstControl.label, secondControl.label, removeControl.label);
  const diagram = element('div', { class: 'demo-diagram demo-diagram-pair' });
  const result = output('restriction-output');
  const details = paragraph('demo-note', '');
  container.append(controls, diagram, result, details);
  function refresh() {
    const word = xorEdgeSets(...[firstControl.input.checked ? first : [], secondControl.input.checked ? second : []]);
    const restricted = removeControl.input.checked ? word.filter((edge) => !witnessKeys.has(edgeKey(edge))) : word;
    const points = [[90, 70], [270, 70], [270, 250], [90, 250]];
    const leftSvg = svgFrame(360, 315, `Ambient XOR. Selected edges: ${edgeList(word)}. Every vertex has even degree.`);
    leftSvg.append(svgElement('text', { x: 180, y: 25, 'text-anchor': 'middle', class: 'graph-label' }, 'Ambient XOR (always even)'));
    drawGraph(leftSvg, points, ambient, { active: word, witness: first });
    leftSvg.append(svgElement('text', { x: 180, y: 301, 'text-anchor': 'middle', class: 'graph-label' }, firstControl.input.checked && secondControl.input.checked ? 'Shared edge 0–2 cancels' : 'Dashed outline = witness W'));
    const rightSvg = svgFrame(360, 315, `${removeControl.input.checked ? 'Outside witness W' : 'No edges removed'}. Selected edges: ${edgeList(restricted)}. Even: ${isEvenEdgeSet(4, restricted)}. Forest: ${isForest(4, restricted)}.`);
    rightSvg.append(svgElement('text', { x: 180, y: 25, 'text-anchor': 'middle', class: 'graph-label' }, removeControl.input.checked ? 'Restriction outside W' : 'Same set (no restriction)'));
    drawGraph(rightSvg, points, restricted, { active: restricted, outside: restricted, mutedNodes: true });
    rightSvg.append(svgElement('text', { x: 180, y: 301, 'text-anchor': 'middle', class: 'graph-label' }, isForest(4, restricted) ? 'A forest' : 'Contains a cycle'));
    diagram.replaceChildren(leftSvg, rightSvg);
    const even = isEvenEdgeSet(4, restricted), forest = isForest(4, restricted);
    result.textContent = `Ambient selected edges: ${edgeList(word)}. ${removeControl.input.checked ? 'Outside W' : 'Unrestricted selected edges'}: ${edgeList(restricted)}. Right-hand edge set: even = ${even ? 'yes' : 'no'}; forest = ${forest ? 'yes' : 'no'}.`;
    details.textContent = `Right-hand degrees at vertices 0–3: ${edgeDegrees(4, restricted).join(', ')}. ${removeControl.input.checked && restricted.length === 2 ? 'The nonempty path 2–3–0 is a forest. Its endpoints have odd degree. Restriction of an ambient even edge set can give an edge set that is not even.' : !restricted.length ? 'The empty edge set is even and is a forest.' : 'Before restriction, XOR preserves even degree at every vertex.'}`;
  }
  refresh();
}
