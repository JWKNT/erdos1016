"""Independent DFS validation of a high-girth mean-length obstruction."""
import itertools
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def decode(s):
 n=ord(s[0])-63
 bits=[(ord(ch)-63)>>b&1 for ch in s[1:] for b in range(5,-1,-1)]
 es=[(u,v) for bit,(u,v) in zip(bits,((u,v) for v in range(1,n) for u in range(v))) if bit]
 return n,es

def check(row):
 n,es=decode(row['g6']); adj=[[] for _ in range(n)]
 for i,(u,v) in enumerate(es): adj[u].append((v,i));adj[v].append((u,i))
 cycles=[]
 for start in range(n):
  def walk(v,used,mask,first):
   for u,e in adj[v]:
    if u==start and used.bit_count()>=3 and first<v:
     cycles.append((mask|(1<<e),used))
    elif u>start and not(used>>u&1):
     walk(u,used|(1<<u),mask|(1<<e),u if v==start else first)
  walk(start,1<<start,0,-1)
 assert len({mask for mask,_ in cycles})==len(cycles)
 count=len(cycles); length=sum(mask.bit_count() for mask,_ in cycles)
 cols=[sum((1<<j) for j,(mask,_) in enumerate(cycles) if mask>>i&1) for i in range(len(es))]
 freqs=[c.bit_count() for c in cols]
 assert (count,length,min(freqs))==(row['cycles'],row['length_sum'],row['min_edge'])
 assert 4*length>3*n*count
 assert 2*min(freqs)<=count
 cuts=[]
 for removed in itertools.combinations(range(len(es)),3):
  rem=set(removed); reached={0}; pending=[0]
  while pending:
   for u,e in adj[pending.pop()]:
    if e not in rem and u not in reached: reached.add(u);pending.append(u)
  if len(reached)==n:continue
  other=set(range(n))-reached
  ra=sum(u in reached and v in reached for u,v in es)-len(reached)+1
  rb=sum(u in other and v in other for u,v in es)-len(other)+1
  if min(ra,rb)>0: cuts.append({'removed':removed,'shore':sorted(reached),'ranks':[ra,rb]})
 return {'g6':row['g6'],'vertices':n,'edges':es,'rank':len(es)-n+1,'girth':min(mask.bit_count() for mask,_ in cycles),'cycles':count,'length_sum':length,'mean_minus_three_n_over_four_fraction':[4*length-3*n*count,4*count], 'edge_frequencies':freqs,'minimum_frequency':min(freqs),'edge_connectivity_at_least_three':0 not in cols and len(set(cols))==len(cols),'cyclic_three_cuts':cuts,'validation':'Independent simple-cycle DFS; full edge frequencies; direct three-edge-cut enumeration.'}

rows=[json.loads(line) for line in (HERE/'root-edge-half-mean-order22.jsonl').read_text().splitlines()]
out=[check(row) for row in rows if row['kind']=='mean_violation']
(HERE/'root-edge-half-mean-witness-checks.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out:
 print(json.dumps({k:v for k,v in r.items() if k not in ['edges','edge_frequencies','cyclic_three_cuts']}|{'cyclic_three_cut_count':len(r['cyclic_three_cuts'])}))
