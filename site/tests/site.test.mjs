import assert from 'node:assert/strict';
import test from 'node:test';
import { readFile, access } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { ringGraph, forestDistribution, horakKim, logStar, secondMomentBound, enumerateEvenSets, edgeKey } from '../assets/math-core.mjs';

const site = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const repo = resolve(site, '..');
const read = (path) => readFile(resolve(site, path), 'utf8');

// The three tours, by their folder below the site root. The Erdős 1016 tour is the root page,
// because other sites link the address jehlp.net/erdos1016. `paper` is the file in site/papers,
// `source` is its place in the repository, and `sections` is the number of numbered sections.
const TOURS = {
  '': {
    title: 'Erdős 1016', sections: 6, demos: ['graph', 'binary'],
    paper: 'pancyclic.pdf', pages: 7, source: 'paper/minimal/pancyclic/pancyclic.pdf',
  },
  forest: {
    title: 'Forest Estimate', sections: 8, demos: [],
    paper: 'forest.pdf', pages: 12, source: 'paper/minimal/forest/forest.pdf',
  },
  'exact-maximums': {
    title: 'Exact Maximums', sections: 7, demos: ['ring'],
    paper: 'exact-maximum.pdf', pages: 36, source: 'paper/minimal/exact-maximum/exact-maximum.pdf',
  },
};
const PAGE_COUNT = Object.fromEntries(Object.values(TOURS).map(({ paper, pages }) => [paper, pages]));
const slugs = Object.keys(TOURS);
const prefix = (slug) => (slug ? '../' : '');
const name = (slug) => slug || 'root page';
const html = Object.fromEntries(await Promise.all(slugs.map(async (slug) => [slug, await read(slug ? `${slug}/index.html` : 'index.html')])));
// The list page. The homepage of jehlp.net opens it, and each tour links it as "All Tours".
const LIST = { slug: 'graph-theory', title: 'Erdős 1016 & Graph Theory' };
const list = await read(`${LIST.slug}/index.html`);
const everyPage = [...slugs.map((slug) => [slug, html[slug]]), [LIST.slug, list]];
const sections = (page) => [...page.matchAll(/<section id="([\w-]+)"[^>]*>([\s\S]*?)<\/section>/g)].map(([, id, body]) => ({ id, body }));
const numbered = (page) => sections(page).filter(({ body }) => body.includes('class="chapter-number"'));
const text = (fragment) => fragment.replace(/<[^>]+>/g, '');
const number = (value) => value.toLocaleString('en-US');

test('each tour has its numbered sections, unique IDs and a list of the sections in the margin', () => {
  for (const slug of slugs) {
    const page = html[slug];
    const ids = [...page.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]);
    assert.equal(ids.length, new Set(ids).size, `${name(slug)}: repeated id`);
    const numbers = [...page.matchAll(/<h2><span class="chapter-number">(\d+)<\/span>/g)].map((m) => Number(m[1]));
    assert.deepEqual(numbers, Array.from({ length: TOURS[slug].sections }, (_, i) => i + 1), name(slug));
    // The list is the first item of the first section, so it is at the top of the margin.
    const first = sections(page)[0];
    assert.equal(first.id, 'start', name(slug));
    assert.match(first.body, /^\s*<nav class="contents side" aria-label="Contents">/, `${name(slug)}: the list of sections is in the first section`);
    const listed = [...first.body.match(/<nav class="contents side"[\s\S]*?<\/nav>/)[0].matchAll(/href="#([\w-]+)"/g)].map((m) => m[1]);
    assert.deepEqual(listed, numbered(page).map(({ id }) => id), `${name(slug)}: the list names every numbered section in order`);
    for (const [, id] of page.matchAll(/href="#([^"]+)"/g)) assert.ok(ids.includes(id), `${name(slug)}: unknown anchor ${id}`);
    assert.doesNotMatch(page, /<aside id="contents"|class="reading-layout"|class="stop-sentence"/, `${name(slug)}: no left column and no summary line`);
  }
});

test('each numbered section has its reference to the paper after the heading, and one margin item at most', () => {
  for (const slug of slugs) {
    for (const { id, body } of numbered(html[slug])) {
      assert.match(body, /<\/h2>\s*<p class="in-paper"><span class="in-paper-group"><span class="in-paper-label">Paper<\/span> /, `${name(slug)}#${id}: the reference follows the heading`);
      assert.equal((body.match(/class="in-paper"/g) || []).length, 1, `${name(slug)}#${id}: one reference line`);
      assert.ok(body.includes(`href="${prefix(slug)}papers/${TOURS[slug].paper}#page=`), `${name(slug)}#${id}: link to its own paper`);
      assert.ok((body.match(/class="side"/g) || []).length <= 1, `${name(slug)}#${id}: one margin item at most`);
    }
    // A margin item is a figure with a caption, or the example of the rings.
    for (const [, tag, inner] of html[slug].matchAll(/<(figure|aside) class="side">([\s\S]*?)<\/\1>/g)) {
      if (tag === 'figure') assert.match(inner, /^(?:<svg viewBox="0 0 \d+ \d+" role="img" aria-label="[^"]{40,}">|<table class="values">)[\s\S]*<figcaption>[^]+<\/figcaption>$/, `${name(slug)}: a margin figure has an accessible name and a caption`);
      else assert.match(inner, /<div id="ring-demo"><\/div>/, `${name(slug)}: the margin example`);
    }
  }
});

test('every link to a paper names a file and a page that exist', async () => {
  let links = 0;
  for (const [slug, page] of everyPage) {
    for (const [, file, pageNumber] of page.matchAll(/href="(?:\.\.\/)?papers\/([\w.-]+)(?:#page=(\d+))?"/g)) {
      links += 1;
      assert.ok(Object.hasOwn(PAGE_COUNT, file), `${name(slug)}: unknown paper ${file}`);
      if (pageNumber !== undefined) assert.ok(Number(pageNumber) >= 1 && Number(pageNumber) <= PAGE_COUNT[file], `${file} has no page ${pageNumber}`);
    }
  }
  assert.ok(links >= 50, `only ${links} links to the papers`);
  for (const slug of slugs) {
    const header = html[slug].match(/<header\b[\s\S]*?<\/header>/)[0];
    assert.ok(header.includes(`href="${prefix(slug)}papers/${TOURS[slug].paper}">Paper</a>`), `${name(slug)}: the header links the paper`);
    // The paper is linked on the words that state the result, in the first section.
    const first = sections(html[slug])[0].body.replace(/<nav[\s\S]*?<\/nav>/, '');
    assert.ok(first.includes(`<a href="${prefix(slug)}papers/${TOURS[slug].paper}">`), `${name(slug)}: the first section links the paper`);
  }
});

test('the published papers are the papers of the repository', async () => {
  for (const { paper, source } of Object.values(TOURS)) {
    const pdf = await readFile(resolve(site, 'papers', paper));
    assert.equal(pdf.subarray(0, 5).toString(), '%PDF-');
    assert.deepEqual(pdf, await readFile(resolve(repo, source)), `${paper} differs from ${source}`);
  }
  // The first paper of September 2026 stays at its address.
  assert.ok(html[''].includes('href="paper.pdf"'));
  assert.deepEqual(await readFile(resolve(site, 'paper.pdf')), await readFile(resolve(repo, 'paper/erdos1016.pdf')));
});

test('local linked resources exist; no external runtime dependencies', async () => {
  for (const [slug, page] of everyPage) {
    for (const [, url] of page.matchAll(/(?:src|href)="([^"]+)"/g)) {
      if (url.startsWith('#') || url.startsWith('https://')) continue;
      const target = url.split(/[?#]/)[0];
      await access(resolve(site, slug, target.endsWith('/') ? `${target}index.html` : target));
    }
    // Scripts, style sheets and the icon are local files. The canonical address is not a resource.
    for (const [tag] of page.matchAll(/<script[^>]*src="[^"]+"[^>]*>|<link[^>]*rel="(?:stylesheet|icon)"[^>]*>|<img[^>]*>/g)) {
      assert.doesNotMatch(tag, /(?:src|href)="(?:https?:)?\/\//, `${name(slug)}: external resource in ${tag}`);
    }
  }
});

test('every page has the identity header, a canonical address under /erdos1016/ and no footer', () => {
  for (const [slug, page] of everyPage) {
    const label = name(slug);
    assert.match(page, /^<!doctype html>\n<html lang="en">/, label);
    assert.match(page, /name="viewport"/, label);
    assert.match(page, /<a class="skip-link" href="#main">/, label);
    assert.match(page, /<main id="main" class="tour(?: tour--plain)?">/, label);
    assert.ok(page.includes(`<link rel="canonical" href="https://jehlp.net/erdos1016/${slug ? `${slug}/` : ''}">`), `${label}: canonical`);
    const header = page.match(/<header class="site-header site-header--identity">[\s\S]*?<\/header>/)[0];
    assert.match(header, /<img class="site-mark" src="[^"]*assets\/mark\.png" alt="" width="32" height="32">/, label);
    assert.match(header, /<a class="site-home" aria-label="Home — jehlp.net" href="https:\/\/jehlp\.net\/">/, label);
    assert.match(header, /<button type="button" data-theme-toggle="" class="theme-toggle"/, label);
    assert.doesNotMatch(header, /github\.com|href="#contents"/, label);
    assert.doesNotMatch(page, /<footer|class="eyebrow"|class="introduction"/, label);
    assert.equal((page.match(/<h1\b/g) || []).length, 1, `${label}: one h1`);
    const title = slug === LIST.slug ? LIST.title : TOURS[slug].title;
    const escaped = title.replaceAll('&', '&amp;');
    assert.ok(header.includes(`<h1 class="site-title">${escaped}</h1>`), label);
    assert.ok(page.includes(`<title>${escaped} · jehlp.net</title>`), label);
    // A tour links the list page and its paper. The list page has its links in the text.
    const links = [...header.matchAll(/<a href="([^"]*)">([^<]*)<\/a>/g)].map((m) => `${m[2]}: ${m[1]}`);
    const expected = slug === LIST.slug ? [] : [`All Tours: ${prefix(slug)}${LIST.slug}/`, `Paper: ${prefix(slug)}papers/${TOURS[slug].paper}`];
    assert.deepEqual(links, expected, `${label}: header links`);
  }
  // Names on jehlp.net have a capital letter on each word, as the homepage list has them.
  for (const title of [LIST.title, ...Object.values(TOURS).map((tour) => tour.title)]) assert.match(title, /^(?:\p{Lu}[\p{L}]*|\d+|&)(?: (?:\p{Lu}[\p{L}]*|\d+|&))*$/u, title);
  // Other sites link the address jehlp.net/erdos1016. It stays the page on Erdős problem 1016.
  assert.equal(TOURS[''].title, 'Erdős 1016');
  assert.ok(html[''].includes('Erdős problem 1016 asks for the least number of edges'));
});

test('mathematics is native MathML from the build, with the local math font', async () => {
  for (const [slug, page] of everyPage) {
    const label = name(slug);
    assert.doesNotMatch(page, /\\\(|\\\)|\\\[|\\\]|\$\$|\{\{|href="~/, `${label}: TeX or a directive remains`);
    // Formulas are MathML, not hand-built spans or Unicode subscripts.
    assert.doesNotMatch(page, /class="math-inline"|<var>|log₂|[₀-₉]/, label);
    assert.doesNotMatch(page, /<script[^>]*(?:temml|katex|mathjax)/i, `${label}: no typesetter in the browser`);
  }
  for (const slug of slugs) {
    assert.ok((html[slug].match(/<math[\s>]/g) || []).length >= 50, `${name(slug)}: inline formulas`);
    const displays = (html[slug].match(/<div class="equation" role="group" aria-label="Formula" tabindex="0"><math display="block"/g) || []).length;
    assert.ok(displays >= 3, `${name(slug)}: ${displays} display formulas`);
    assert.equal(displays, (html[slug].match(/class="equation"/g) || []).length, `${name(slug)}: every display has the keyboard scroll region`);
  }
  assert.ok(html.forest.includes('<mfrac>') && html.forest.includes('<msup>') && html[''].includes('<msub>'));
  const css = await read('assets/guide.css');
  assert.match(css, /font-family: "Guide Math"/);
  await access(resolve(site, 'assets/fonts/latinmodern-math.otf'));
  await access(resolve(site, 'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('every interactive example has its code and a text for readers without scripts', async () => {
  const explorers = await read('assets/explorers.mjs');
  const mounted = new Set([...explorers.matchAll(/'([\w-]+-demo)': mount\w+,/g)].map((m) => m[1]));
  const used = new Set();
  for (const slug of slugs) {
    const ids = [...html[slug].matchAll(/<div id="([\w-]+)-demo"><\/div>/g)].map((m) => m[1]);
    assert.deepEqual(ids.sort(), [...TOURS[slug].demos].sort(), name(slug));
    for (const id of ids) {
      used.add(`${id}-demo`);
      assert.ok(mounted.has(`${id}-demo`), `${name(slug)}: no code for ${id}-demo`);
      assert.match(html[slug], new RegExp(`<div id="${id}-demo"></div>\\s*<noscript><p>[^<]{40,}</p></noscript>`), `${name(slug)}: ${id}-demo`);
    }
    const script = new RegExp(`<script type="module" src="${prefix(slug).replace(/\./g, '\\.')}assets/explorers\\.mjs\\?v=[\\w-]+"></script>`);
    assert.equal(script.test(html[slug]), ids.length > 0, `${name(slug)}: the script is on the page only if the page has an example`);
  }
  assert.deepEqual([...mounted].sort(), [...used].sort(), 'each example of the code is on one page');
  assert.doesNotMatch(list, /<script type="module"|-demo"/, 'the list page has no example');
});

test('the list page names the three tours in order, each with its address, its text and its paper', () => {
  const items = [...list.matchAll(/<li>\s*<h2><a href="([^"]*)">([^<]*)<\/a><\/h2>\s*<p>([\s\S]*?)<\/p>\s*<p class="paper-line"><a href="([^"]*)">[^<]+<\/a> <span class="paper-meta">PDF, (\d+) pages<\/span><\/p>\s*<\/li>/g)];
  assert.equal(items.length, slugs.length);
  slugs.forEach((slug, i) => {
    const [, href, title, body, paper, pages] = items[i];
    assert.equal(href, `../${slug ? `${slug}/` : ''}`, `address of ${title}`);
    assert.equal(title, TOURS[slug].title);
    assert.ok(body.length > 120, `${title}: a text of one or more sentences`);
    assert.equal(paper, `../papers/${TOURS[slug].paper}`);
    assert.equal(Number(pages), TOURS[slug].pages);
  });
  assert.equal((list.match(/<li>/g) || []).length, slugs.length, 'no other item');
  assert.doesNotMatch(list, /class="contents|class="chapter-number"|class="side"/, 'the list page is not a tour');
});

test('the numbers in the text and in the margin tables are the numbers that the code computes', () => {
  const row = (cells) => `<tr>${cells.map((cell) => `<td>${cell}</td>`).join('')}</tr>`;
  // Forest tour: the rings with one marked square.
  for (const squares of [2, 3, 4, 5, 6]) {
    const ring = ringGraph(squares);
    const marked = new Set([...ring.tiles[0].left, ...ring.tiles[0].right]);
    const { favorable, total } = forestDistribution(ring.n, ring.edges, ring.edges.filter(([u, v]) => marked.has(u) || marked.has(v)));
    assert.equal(total, 2 ** ring.rank);
    assert.ok(2 * favorable > total, 'more than half, as the lower limit says');
    assert.ok(html.forest.includes(row([squares, number(total), number(favorable), (favorable / total).toFixed(3)])), `row for ${squares} squares`);
  }
  // Forest tour: two triangles joined by one edge, with P the left triangle. Two of the four outside parts are forests.
  const bridge = [[0, 1], [1, 2], [2, 0], [3, 4], [4, 5], [5, 3], [2, 3]];
  const atLeft = bridge.filter(([u, v]) => u < 3 || v < 3);
  assert.deepEqual((({ favorable, total }) => [favorable, total])(forestDistribution(6, bridge, atLeft)), [2, 4]);
  // Forest tour: two triangles joined by two edges. Each triangle is a component of two of the eight
  // even subgraphs, and both are components of one.
  const left = [[0, 1], [1, 2], [2, 0]], right = [[3, 4], [4, 5], [5, 3]];
  const even = enumerateEvenSets(6, [...left, ...right, [1, 3], [2, 4]]).map((set) => new Set(set.map(edgeKey)));
  const component = (triangle, set) => triangle.every((edge) => set.has(edgeKey(edge))) && !set.has('1-3') && !set.has('2-4');
  assert.equal(even.length, 8);
  assert.equal(even.filter((set) => component(left, set)).length, 2);
  assert.equal(even.filter((set) => component(right, set)).length, 2);
  assert.equal(even.filter((set) => component(left, set) && component(right, set)).length, 1);
  assert.ok(text(html.forest).includes('The graph has rank 3 and eight even subgraphs.'));
  // Forest tour: the two sides of the second-moment inequality, and the rank from which the error term is below one half.
  for (const mu of [1, 10, 100]) assert.ok(html.forest.includes(row([mu, secondMomentBound(mu, 2).toFixed(3), (0.5 + 1 / (2 * mu)).toFixed(3)])), `row for the mean ${mu}`);
  assert.equal(20 / 40, 0.5);
  assert.match(html.forest, /<msup><mn>2<\/mn><msup><mn>2<\/mn><msup><mn>2<\/mn><mn[^>]*>40<\/mn><\/msup><\/msup><\/msup>/, 'the tower 2^(2^(2^40))');
  // Erdős 1016: the iterated logarithm, the closing edges for 16 segments, and one million vertices.
  for (const n of [2, 4, 16, 65536]) {
    assert.equal(logStar(n + 1), logStar(n) + 1, `${n} is the largest number with its value`);
    assert.ok(html[''].includes(row([number(n), logStar(n)])), `row for n = ${n}`);
  }
  for (const [segments, low, high] of [[16, 17, 2 ** 16 + 16], [4, 5, 20], [2, 3, 6]]) assert.ok(html[''].includes(row([segments, `${number(low)} to ${number(high)}`])), `row for ${segments} segments`);
  assert.equal(Math.ceil(Math.log2(16)), 4);
  assert.equal(Math.ceil(Math.log2(4)), 2);
  assert.equal(logStar(16), 3);
  assert.equal(logStar(1e6), 5);
  assert.equal(Math.floor(Math.log2(1e6)) + logStar(1e6) + 1, 25);
  assert.equal((Math.log2(1e6) + logStar(1e6)).toFixed(1), '24.9');
  assert.ok(text(html['']).includes('So 25 edges above the million are enough'));
  // Exact maximums: the values of the formula.
  for (const r of [9, 10, 20, 27]) assert.ok(html['exact-maximums'].includes(row([r, number(2 ** (r - 1)), number(horakKim(r))])), `row for r = ${r}`);
  const exact = text(html['exact-maximums']);
  assert.equal(256 + 136 - 12, horakKim(9));
  assert.ok(exact.includes(`The ring of rank 9 has four squares and ${horakKim(9)} cycles.`));
  assert.ok(exact.includes(`one single rung and ${horakKim(10)} cycles`));
  assert.ok(exact.includes(`is ${number(horakKim(27))}.`));
  assert.ok(exact.includes(`that is ${number(horakKim(27) - 2 ** 26)} cycles out of 67 million`));
  assert.ok(exact.includes('67,959,973 cycles') && 67959973 > horakKim(27));
  assert.ok(9 / 25 < 2 / 5 && 2 / 5 * 2 ** 10 + 2 ** 5 < 2 ** 9, 'the two inequalities of the third case, for r = 10');
});

// A screening aid for the writing rules, not a full check: a formula counts as one word.
test('the text is short: at most 25 words in a sentence, six sentences in a paragraph, 1,400 words on a page', () => {
  for (const slug of slugs) {
    const main = html[slug].match(/<main[\s\S]*<\/main>/)[0].replace(/<noscript>[\s\S]*?<\/noscript>/g, '').replace(/<nav[\s\S]*?<\/nav>/g, '').replace(/<svg[\s\S]*?<\/svg>/g, '').replace(/<table[\s\S]*?<\/table>/g, '');
    const blocks = [...main.matchAll(/<(p|li|figcaption)\b[^>]*>([\s\S]*?)<\/\1>/g)].filter(([whole]) => !whole.includes('class="in-paper"')).map(([, , inner]) => text(inner.replace(/<div class="equation"[\s\S]*?<\/div>/g, ' ').replace(/<math[\s\S]*?<\/math>/g, 'X')).replace(/&amp;/g, '&').replace(/\s+/g, ' ').trim());
    let words = 0;
    for (const block of blocks) {
      assert.doesNotMatch(block, /;/, `${name(slug)}: a semicolon in "${block.slice(0, 60)}"`);
      const sentences = block.split(/(?<=[.!?])\s+/).filter(Boolean);
      assert.ok(sentences.length <= 6, `${name(slug)}: ${sentences.length} sentences in "${block.slice(0, 60)}"`);
      for (const sentence of sentences) {
        const count = sentence.split(' ').length;
        words += count;
        assert.ok(count <= 25, `${name(slug)}: ${count} words in "${sentence}"`);
      }
    }
    assert.ok(words <= 1400, `${name(slug)}: ${words} words`);
    assert.doesNotMatch(main, /The tour has|Each stop gives/, `${name(slug)}: no line about the page itself`);
  }
});

test('the margin layout keeps the theme: thin rules, no shadow, no rounded corner', async () => {
  const css = await read('assets/guide.css');
  assert.doesNotMatch(css, /box-shadow|border-radius:(?!0)|linear-gradient|radial-gradient/);
  // A margin item floats into the space on the right of the text column, on a wide screen only.
  assert.match(css, /@media \(min-width:62rem\) \{\s*main > section \{ display:flow-root; padding-right:max\(calc\(var\(--side\) \+ var\(--side-gap\)\), calc\(100% - var\(--text\)\)\); \}\s*main > section > :is\(\.in-paper, \.side\) \{ float:right; clear:right; width:var\(--side\);/);
  assert.match(css, /\.statement \{[^}]*border-left:3px solid var\(--blue\); background:var\(--surface-blue\)/);
  // Figure colours come from theme tokens, so both colour modes have them.
  for (const rule of css.match(/\.fig-[\w-]+ \{[^}]*\}/g)) assert.doesNotMatch(rule, /#[0-9a-f]{3,8}\b|rgb\(/i, rule);
});

test('selected demo controls retain contrast on hover and 44-pixel minimum width', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /\.demo-button\[aria-pressed=true\]:hover:not\(:disabled\)\{background:var\(--ink\);color:var\(--paper\)\}/);
  assert.match(css, /\.demo-controls button,\.demo-button\{min-width:44px/);
});

test('disabled demo buttons are distinct and all control rows are hidden in print', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /\.demo-button:disabled\s*\{[^}]*color:var\(--muted\);[^}]*border-color:var\(--line\);[^}]*cursor:default;/);
  assert.match(css, /@media print\s*\{\s*\.contents,\.demo-controls,\.demo-button-row,\.site-header nav\s*\{\s*display:none;/);
});

test('mathematics uses prose ink with neutral display shading', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /--math-ink: var\(--ink\)/);
  assert.match(css, /background:var\(--surface\); color:var\(--ink\)/);
  assert.doesNotMatch(css, /#315f68|#aacdd1/);
});

test('vendored theme includes the exact Home door and Wrenfold assets with math kept separate', async () => {
  const hash = async (path) => createHash('sha256').update(await readFile(resolve(site, path))).digest('hex');
  assert.equal(await hash('assets/theme/fonts/WrenfoldText-Regular.woff2'), '826f6c238521bfbf98d897a8f81810a78ed2d6571fec0ef86d0d51edba0212be');
  for (const icon of ['home-doorway.svg', 'home-folio-scroll.svg', 'home-compass.svg', 'home-emblem.svg', 'home.svg']) {
    assert.equal(await hash(`assets/theme/icons/${icon}`), '2baa87caf29834e155af108d7743c410e2a3b1775edf6c7671ec24918a7810db');
  }
  const css = await read('assets/theme/base.css');
  assert.match(css, /--serif: Georgia, "Times New Roman", serif/);
  assert.match(css, /--reading: "Wrenfold Text"/);
  assert.match(css, /--display: "Palatino Linotype"/);
  assert.match(css, /icons\/home-doorway\.svg/);
  for (const file of ['OFL-1.1.txt', 'Noto-Debian-copyright.txt', 'Wrenfold-README.txt']) await access(resolve(site, `assets/theme/fonts/${file}`));
  const guide = await read('assets/guide.css');
  assert.match(guide, /math \{ font-family:var\(--math-face\)/);
  assert.match(guide, /\.graph-label \{[^}]*font-family:var\(--sans\)/);
  assert.match(guide, /main \{ font-family:var\(--reading, var\(--serif\)\)/);
  assert.match(guide, /main :is\(h2, h3\) \{ font-family:var\(--reading, var\(--serif\)\)/);
  assert.match(guide, /main :is\(button, input, select, textarea, summary, legend\), \.demo-controls, \.demo-output \{ font-family:var\(--ui, var\(--serif\)\)/);
});

// The pages are built from site-src/pages with Temml. The check runs where Temml is present:
// after npm install in site-src/, or with the path of dist/temml.mjs in the variable TEMML.
test('the written pages are the build of their sources', async (t) => {
  const { buildPages } = await import(pathToFileURL(resolve(repo, 'site-src/build.mjs')).href);
  let pages;
  try {
    pages = await buildPages();
  } catch (error) {
    if (/Temml is not available/.test(error.message)) return t.skip('Temml is not installed here');
    throw error;
  }
  assert.equal(pages.length, 4);
  for (const { file, html: built } of pages) assert.equal(await readFile(file, 'utf8'), built, `${file} is not the build of its source`);
});
