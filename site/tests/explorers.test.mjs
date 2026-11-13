import assert from 'node:assert/strict';
import test from 'node:test';
import { mountExplorers } from '../assets/explorers.mjs';
import { horakKim } from '../assets/math-core.mjs';

// A small DOM fixture exercises the real input handler without a browser dependency.
// It does not emulate layout, focus, or native number-input validation.
class Node {
  constructor(tag) {
    this.tag = tag;
    this.attributes = new Map();
    this.children = [];
    this.dataset = {};
    this.listeners = new Map();
    this.text = '';
    this.value = '';
  }
  // Like the DOM: text is the concatenation of child text; setting it removes children.
  get textContent() {
    return this.children.length ? this.children.map((child) => typeof child === 'string' ? child : child.textContent).join('') : this.text;
  }
  set textContent(value) { this.text = String(value); this.children = []; }
  setAttribute(name, value) {
    this.attributes.set(name, String(value));
    if (name === 'value') this.value = String(value);
  }
  getAttribute(name) { return this.attributes.get(name) ?? null; }
  removeAttribute(name) { this.attributes.delete(name); }
  get id() { return this.getAttribute('id'); }
  set id(value) { this.setAttribute('id', value); }
  get valueAsNumber() { return this.value.trim() === '' ? NaN : Number(this.value); }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = nodes; }
  addEventListener(type, callback) { this.listeners.set(type, callback); }
  find(predicate) {
    if (predicate(this)) return this;
    for (const child of this.children) {
      if (typeof child === 'string') continue;
      const found = child.find(predicate);
      if (found) return found;
    }
  }
}

// Mount the examples on a page that has the given containers, and return the root.
function fixture(...ids) {
  const root = new Node('div');
  for (const id of ids) { const container = new Node('div'); container.id = id; root.append(container); }
  const previous = globalThis.document;
  globalThis.document = {
    createElement: (tag) => new Node(tag),
    createElementNS: (_, tag) => new Node(tag),
    createTextNode: (text) => String(text),
    getElementById: (id) => root.find((node) => node.id === id),
  };
  mountExplorers();
  return {
    root,
    byId: (id) => root.find((node) => node.id === id),
    button: (text) => root.find((node) => node.tag === 'button' && node.textContent === text),
    restore() {
      if (previous === undefined) delete globalThis.document;
      else globalThis.document = previous;
    },
  };
}

test('the ring example counts the cycles for every rank and shows the formula of Horak and Kim', () => {
  const page = fixture('ring-demo');
  try {
    const input = page.byId('ring-rank');
    const output = page.byId('ring-output');
    assert.equal(input.getAttribute('min'), '5');
    assert.equal(input.getAttribute('max'), '14');
    for (let r = 5; r <= 14; r++) {
      input.value = String(r);
      input.listeners.get('input')();
      const squares = Math.floor((r - 1) / 2);
      const tiles = `${squares} squares${r % 2 ? '' : ' and one single rung'}`;
      const count = horakKim(r).toLocaleString('en-US');
      assert.equal(output.textContent, `r = ${r}: ${tiles}. Counted one by one, the ring has ${count} cycles, and H(${r}) = ${count}. The first term is 2${r - 1} = ${(2 ** (r - 1)).toLocaleString('en-US')}.`);
      const svg = page.root.find((node) => node.tag === 'svg');
      assert.ok(svg.getAttribute('aria-label').includes(`rank ${r} and ${horakKim(r)} cycles`));
      // A square has four edges, and the single rung is one edge.
      const edges = svg.children.filter((child) => child.tag === 'line').map((line) => line.getAttribute('class'));
      assert.equal(edges.filter((name) => name.includes('ring-square')).length, 4 * squares);
      assert.equal(edges.filter((name) => name.includes('ring-rung')).length, r % 2 ? 0 : 1);
      assert.equal(edges.length, 3 * (r - 1), 'a cubic graph of rank r has 3(r - 1) edges');
    }
  } finally { page.restore(); }
});

test('the graph on six vertices reports its cycle lengths and when it is pancyclic', () => {
  const page = fixture('graph-demo');
  try {
    const stats = page.byId('graph-stats');
    assert.equal(stats.textContent, '8 edges. Cycle lengths: 3, 4, 5, 6. The graph is pancyclic.');
    page.button('The cycle only').listeners.get('click')();
    assert.equal(stats.textContent, '6 edges. Cycle lengths: 6. No cycle of length 3 or 4 or 5.');
    // One more edge is never enough: this is the lower limit h(6) = 2 of the page.
    for (const label of ['0–2', '0–3', '0–4', '1–3', '1–4', '1–5', '2–4', '2–5', '3–5']) {
      page.button('The cycle only').listeners.get('click')();
      page.button(label).listeners.get('click')();
      assert.match(stats.textContent, /^7 edges\. .* No cycle of length /, `one more edge ${label}`);
    }
    page.button('All nine edges').listeners.get('click')();
    assert.equal(stats.textContent, '15 edges. Cycle lengths: 3, 4, 5, 6. The graph is pancyclic.');
  } finally { page.restore(); }
});

test('the shortcut example makes each cycle length from 5 to 20 in exactly one way', () => {
  const page = fixture('binary-demo');
  try {
    const output = page.byId('binary-output');
    assert.equal(output.textContent, 'Cycle length 20.');
    const seen = new Set();
    for (let length = 5; length <= 20; length++) {
      page.button(String(length)).listeners.get('click')();
      assert.match(output.textContent, new RegExp(`^Cycle length (20|20 − \\([0-9 +]+\\) = ${length})\\.$`));
      const boxes = [0, 1, 2, 3].map((i) => page.byId(`binary-bit-${i}`).checked ? 1 : 0).join('');
      assert.ok(!seen.has(boxes), `the choice ${boxes} is used twice`);
      seen.add(boxes);
    }
    assert.equal(seen.size, 16);
  } finally { page.restore(); }
});
