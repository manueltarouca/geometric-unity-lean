# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
import json
from fractions import Fraction
from itertools import product
d=json.load(open("/tmp/gu-f2/data.json"))
piv=[tuple(p) for p in d["piv"]]; E=d["E"]; CE=d["CE"]
R4=range(4); idx=list(product(R4,R4,R4,R4)); pos={t:i for i,t in enumerate(idx)}
sym=[(a,b) for a in R4 for b in R4 if a<=b]
pairs=[(p,q) for ip,p in enumerate(sym) for iq,q in enumerate(sym) if ip<=iq]
kp=[]; sg=[]
for r in CE:
    k=[i for i,x in enumerate(r) if x][0]; kp.append(pairs[k]); sg.append(r[k])
# relations: (name, args, vector)
rels=[]
for (a,b,c,e) in idx:
    v=[0]*256; v[pos[(a,b,c,e)]]+=1; v[pos[(b,a,c,e)]]+=1; rels.append(("h1",(a,b,c,e),v))
    v=[0]*256; v[pos[(a,b,c,e)]]+=1; v[pos[(a,b,e,c)]]+=1; rels.append(("h2",(a,b,c,e),v))
    v=[0]*256; v[pos[(a,b,c,e)]]+=1; v[pos[(a,c,e,b)]]+=1; v[pos[(a,e,b,c)]]+=1; rels.append(("h3",(a,b,c,e),v))
# row-reduce relations with combination tracking (sparse dicts)
basis=[]  # list of (pivot col, vec dict, combo dict)
def reduce(vec,combo):
    vec=dict(vec); combo=dict(combo)
    for (pc,bv,bc) in basis:
        if pc in vec and vec[pc]!=0:
            f=vec[pc]/bv[pc]
            for k,x in bv.items(): vec[k]=vec.get(k,0)-f*x
            for k,x in bc.items(): combo[k]=combo.get(k,0)-f*x
            vec={k:x for k,x in vec.items() if x!=0}
    return vec,combo
for j,(nm,ar,v) in enumerate(rels):
    vec={i:Fraction(x) for i,x in enumerate(v) if x}
    vec,combo=reduce(vec,{j:Fraction(1)})
    if vec:
        pc=min(vec); basis.append((pc,vec,combo))
out=[]
for t in idx:
    target={pos[t]:Fraction(1)}
    for mi,p in enumerate(piv):
        c=E[mi][pos[t]]
        if c: target[pos[p]]=target.get(pos[p],0)-c
    target={k:x for k,x in target.items() if x!=0}
    vec,combo=reduce(target,{})
    assert not vec, ("not in span", t)
    # target = - (sum combo_j rel_j)?  reduce subtracts: vec_final = target - sum f*rel = 0 => target = sum(-combo)*rel
    terms=[]
    for j,x in combo.items():
        if x!=0:
            nm,ar,_=rels[j]; coef=-x
            terms.append(f"({coef}) * {nm} {' '.join(map(str,ar))}")
    out.append(" + ".join(terms) if terms else "0")
json.dump({"kp":kp,"sg":sg,"piv":piv,"cert":out},open("/tmp/gu-f2/cert.json","w"))
print("ok", sum(1 for c in out if c!="0"), "nontrivial certs; max terms", max(c.count("*") for c in out))
