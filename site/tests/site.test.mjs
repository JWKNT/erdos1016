import assert from 'node:assert/strict';
import test from 'node:test';
import {readFile,access} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
const site=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const html=await readFile(resolve(site,'index.html'),'utf8');
test('twelve chapters, unique IDs and working internal navigation',()=>{
 const ids=[...html.matchAll(/\bid="([^"]+)"/g)].map(m=>m[1]);
 assert.equal(ids.length,new Set(ids).size);assert.equal((html.match(/<section id=/g)||[]).length,12);
 for(const [,id] of html.matchAll(/href="#([^"]+)"/g))assert.ok(ids.includes(id),`Unknown anchor: ${id}`);
});
test('ten progressive experiments and source evidence remain present',()=>{
 for(const id of ['graph','space','forest','binary','logstar','moment','recurrence','cut','walk','restriction'])assert.ok(html.includes(`id="${id}-demo"`),id);
 for(const phrase of ['36203783167','d1bf348','not substitutes for the proof','sufficiently large','supremum','nonbacktracking','Cauchy'])assert.ok(html.includes(phrase),phrase);
 assert.match(html,/lang="en"/);assert.match(html,/name="viewport"/);assert.match(html,/class="skip-link"/);
});
test('local linked resources exist; no external runtime dependencies',async()=>{
 for(const [,url] of html.matchAll(/(?:src|href)="([^"]+)"/g)){
  if(url.startsWith('#')||url.startsWith('https://'))continue;
  await access(resolve(site,url));
 }
 for(const [,src] of html.matchAll(/<script[^>]*src="([^"]+)"/g))assert.ok(!src.startsWith('http'));
});
