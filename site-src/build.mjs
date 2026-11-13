// Builds the pages of site/ from the sources in site-src/pages/.
//
//   node site-src/build.mjs           write the pages
//   node site-src/build.mjs --check   fail if a written page differs from the build
//
// A source is HTML with a small header and a few directives.
//   <!--page { ...JSON... } -->                 title, description, address, paper
//   <section id="x" data-title="Title">         a numbered section of the tour
//   {{in-paper: Lemma 2.2 | 5 ; Figure 2 | 4}}  links to pages of the paper, directly after the
//                                               section tag. An item "forest: Theorem 1.1 | 2"
//                                               is a page of the paper `otherPapers.forest`.
//   class="side"                                one figure, table or example of a section for
//                                               the margin column
//   href="~/forest/"                            a link from the root of the site
//   {{fig:name}} and {{table:name}}             a figure or a table of figures.mjs
//   \( ... \) and \[ ... \]                     TeX, which Temml changes to MathML
//
// Temml 0.14.0 is the only dependency. Install it in site-src/ (npm install), or put the
// path of its file dist/temml.mjs in the environment variable TEMML.
import { readFile, writeFile, mkdir, readdir } from 'node:fs/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';
import path from 'node:path';
import { figures, tables } from './figures.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const siteDir = path.resolve(here, '..', 'site');
const ROOT = 'https://jehlp.net/erdos1016/';
const VERSION = {
  base: '20261108-justify',
  components: 'components-20261003-controls',
  guide: '20261113-margin',
  explorers: '20261113-margin',
};

async function loadTemml() {
  const tried = [];
  for (const source of [process.env.TEMML, 'temml']) {
    if (!source) continue;
    try {
      const module = await import(source === 'temml' ? source : pathToFileURL(path.resolve(source)).href);
      const temml = module.default ?? module;
      if (typeof temml.renderToString === 'function') return temml;
      tried.push(`${source}: no renderToString`);
    } catch (error) {
      tried.push(`${source}: ${error.code ?? error.message}`);
    }
  }
  throw new Error(`Temml is not available (${tried.join('; ') || 'no source'}). Run npm install in site-src/, or set TEMML.`);
}

const escapeHtml = (value) => String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;');
// The sources are HTML, so TeX in them escapes <, > and &. Temml needs the plain characters.
const plainTex = (tex) => tex.trim().replaceAll('&lt;', '<').replaceAll('&gt;', '>').replaceAll('&amp;', '&');

function typesetMath(temml, html) {
  const render = (tex, displayMode) => temml.renderToString(plainTex(tex), { displayMode, throwOnError: true, annotate: false });
  return html
    .replace(/\\\[([\s\S]+?)\\\]/g, (_, tex) => `<div class="equation" role="group" aria-label="Formula" tabindex="0">${render(tex, true)}</div>`)
    .replace(/\\\(([\s\S]+?)\\\)/g, (_, tex) => render(tex, false))
    // A browser can break a line between a formula and the punctuation after it. Hold them together.
    .replace(/(<math>(?:(?!<\/math>)[\s\S])*<\/math>)([,.:;)]+)/g, '<span class="math-nobreak">$1$2</span>');
}

function parseSource(name, source) {
  const header = source.match(/^<!--page\s*([\s\S]*?)-->\s*/);
  if (!header) throw new Error(`${name}: the source needs a <!--page {...} --> header`);
  const meta = JSON.parse(header[1]);
  for (const key of ['slug', 'title', 'description']) {
    if (typeof meta[key] !== 'string') throw new Error(`${name}: the header needs "${key}"`);
  }
  return { meta, body: source.slice(header[0].length) };
}

function expandDirectives(name, meta, body, prefix) {
  const stops = [];
  let html = body.replace(/<section id="([\w-]+)" data-title="([^"]+)">/g, (_, id, title) => {
    stops.push({ id, title });
    return `<section id="${id}">\n<h2><span class="chapter-number">${stops.length}</span> ${title}</h2>`;
  });
  // The list of the numbered sections is the first item of the first section, so that it is at
  // the top of the margin. On a narrow screen the style sheet puts it after the first paragraphs.
  if (stops.length) {
    const contents = `<nav class="contents side" aria-label="Contents"><p class="contents-title">Contents</p><ol>${stops.map(({ id, title }) => `<li><a href="#${id}">${title}</a></li>`).join('')}</ol></nav>\n`;
    if (!/^\s*<section id="start"/.test(html)) throw new Error(`${name}: the first section must have id="start"`);
    html = html.replace(/(<section id="start"[^>]*>\n?)/, `$1${contents}`);
  }
  html = html.replace(/\{\{in-paper:([^}]+)\}\}/g, (_, list) => {
    const groups = [];
    for (const item of list.split(';')) {
      const [, key, text, page] = item.match(/^\s*(?:([\w-]+):)?\s*([^|]+?)\s*\|\s*(\d+)\s*$/) ?? [];
      const paper = key ? meta.otherPapers?.[key] : meta.paper;
      if (!paper || !text || Number(page) < 1 || Number(page) > paper.pages) throw new Error(`${name}: bad reference "${item.trim()}"`);
      const group = groups.find((entry) => entry.paper === paper) ?? groups[groups.push({ paper, label: key ? paper.label : 'Paper', links: [] }) - 1];
      group.links.push(`<a href="${prefix}${paper.file}#page=${page}">${text}, page ${page}</a>`);
    }
    // A separator stays on the line of the link before it.
    const items = (links) => links.map((link, i) => `<span class="in-paper-item">${link}${i < links.length - 1 ? '<span aria-hidden="true"> ·</span>' : ''}</span>`).join(' ');
    return `<p class="in-paper">${groups.map(({ label, links }) => `<span class="in-paper-group"><span class="in-paper-label">${label}</span> ${items(links)}</span>`).join(' ')}</p>`;
  });
  html = html.replace(/\{\{fig:([\w-]+)\}\}/g, (_, figure) => {
    if (!Object.hasOwn(figures, figure)) throw new Error(`${name}: unknown figure ${figure}`);
    return figures[figure]();
  });
  html = html.replace(/\{\{table:([\w-]+)\}\}/g, (_, table) => {
    if (!Object.hasOwn(tables, table)) throw new Error(`${name}: unknown table ${table}`);
    return tables[table]();
  });
  // A link that starts with ~/ is relative to the root of the site.
  html = html.replace(/href="~\/([^"]*)"/g, (_, target) => {
    if (!prefix && !target) throw new Error(`${name}: the page at the root links to itself`);
    return `href="${prefix}${target}"`;
  });
  const leftover = html.match(/\{\{[^}]*\}\}/);
  if (leftover) throw new Error(`${name}: unknown directive ${leftover[0]}`);
  return { html, stops };
}

function frame({ meta, main, stops, prefix, usesDemos }) {
  const canonical = `${ROOT}${meta.slug ? `${meta.slug}/` : ''}`;
  const nav = (meta.nav ?? []).map(({ label, href }) => `<a href="${prefix}${href}">${escapeHtml(label)}</a>`).join('');
  const layout = stops.length ? 'tour' : 'tour tour--plain';
  const script = usesDemos ? `<script type="module" src="${prefix}assets/explorers.mjs?v=${VERSION.explorers}"></script>\n` : '';
  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="theme-color" content="#fbfaf7"><title>${escapeHtml(meta.title)} · jehlp.net</title><meta name="description" content="${escapeHtml(meta.description)}"><meta property="og:type" content="article"><meta property="og:title" content="${escapeHtml(meta.title)}"><meta property="og:description" content="${escapeHtml(meta.description)}"><meta property="og:url" content="${canonical}"><meta property="og:site_name" content="jehlp.net"><link rel="canonical" href="${canonical}"><link rel="icon" href="${prefix}assets/favicon.png"><script src="${prefix}assets/theme/theme.js"></script><link rel="stylesheet" href="${prefix}assets/theme/base.css?v=${VERSION.base}"><link rel="stylesheet" href="${prefix}assets/theme/components.css?v=${VERSION.components}"><script src="${prefix}assets/theme/components.js?v=${VERSION.components}" defer></script><link rel="stylesheet" href="${prefix}assets/guide.css?v=${VERSION.guide}"></head>
<body><a class="skip-link" href="#main">${escapeHtml(meta.skip ?? 'Skip to the text')}</a><header class="site-header site-header--identity"><div class="site-identity site-brand"><img class="site-mark" src="${prefix}assets/mark.png" alt="" width="32" height="32"><h1 class="site-title">${escapeHtml(meta.title)}</h1></div><nav aria-label="Main">${nav}<span class="site-utility-pair"><a class="site-home" aria-label="Home — jehlp.net" href="https://jehlp.net/"><span aria-hidden="true">Home</span></a><button type="button" data-theme-toggle="" class="theme-toggle" aria-label="Use dark theme"></button></span></nav></header>
<main id="main" class="${layout}">
${main.trim()}
</main>
${script}</body></html>
`;
}

export async function buildPages() {
  const temml = await loadTemml();
  const names = (await readdir(path.join(here, 'pages'))).filter((name) => name.endsWith('.html')).sort();
  const pages = [];
  for (const name of names) {
    const { meta, body } = parseSource(name, await readFile(path.join(here, 'pages', name), 'utf8'));
    const prefix = meta.slug ? '../' : '';
    const { html, stops } = expandDirectives(name, meta, body, prefix);
    const main = typesetMath(temml, html);
    if (/\\[([]|\\[)\]]/.test(main)) throw new Error(`${name}: TeX remains after the build`);
    const usesDemos = /id="[\w-]+-demo"/.test(main);
    pages.push({ file: path.join(siteDir, meta.slug, 'index.html'), html: frame({ meta, main, stops, prefix, usesDemos }) });
  }
  return pages;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const check = process.argv.includes('--check');
  const pages = await buildPages();
  let stale = 0;
  for (const { file, html } of pages) {
    const shown = path.relative(path.resolve(here, '..'), file);
    if (check) {
      const present = await readFile(file, 'utf8').catch(() => null);
      if (present !== html) { stale += 1; console.error(`stale: ${shown}`); }
    } else {
      await mkdir(path.dirname(file), { recursive: true });
      await writeFile(file, html);
      console.log(`wrote ${shown} (${html.length} characters)`);
    }
  }
  if (check) {
    if (stale) process.exit(1);
    console.log(`${pages.length} pages are up to date`);
  }
}
