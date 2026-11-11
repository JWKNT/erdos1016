"""Reproducible asymmetric cubic graph fixtures, independent of any weights."""
import json
from pathlib import Path
import random
import networkx as nx

BASE=Path(__file__).resolve().parent
rng=random.Random(10161111)
rows=[];meta=[]
for n in range(22,34,2):
    for i in range(80):
        while True:
            seed=rng.randrange(2**32)
            g=nx.random_regular_graph(3,n,seed=seed)
            if nx.is_connected(g):break
        rows.append(nx.to_graph6_bytes(g,header=False).decode().strip())
        meta.append(dict(order=n,seed=seed))
(BASE/"random-edge-half-asymmetric.g6").write_text("\n".join(rows)+"\n")
(BASE/"random-edge-half-asymmetric-fixtures.json").write_text(json.dumps(meta,indent=2)+"\n")
print("saved",len(rows),"connected simple cubic fixtures")
