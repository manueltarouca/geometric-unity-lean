# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
import os
os.makedirs('/tmp/gu-f2', exist_ok=True)
from fractions import Fraction
from itertools import product
R4=range(4)
def esym(i,j): return lambda a,b: 1 if (a==i and b==j) or (a==j and b==i) else 0
def kn(h,k): return lambda a,b,c,d: h(a,c)*k(b,d)+h(b,d)*k(a,c)-h(a,d)*k(b,c)-h(b,c)*k(a,d)
sym=[(a,b) for a in R4 for b in R4 if a<=b]
pairs=[(p,q) for ip,p in enumerate(sym) for iq,q in enumerate(sym) if ip<=iq]
idx=list(product(R4,R4,R4,R4))
V=[[kn(esym(*p),esym(*q))(*t) for t in idx] for p,q in pairs]  # 55 x 256
# independent coordinates: R_abcd with a<b, c<d, (a,b)<=(c,d) minus Bianchi -> choose 20 via row-reduction of the span
n=len(V); m=256
# find 20 KN rows forming a basis and coordinates pivots via Gaussian elimination over Q
rows=[ [Fraction(x) for x in r] for r in V]
basis=[]; piv=[]; mat=[]
for i,r in enumerate(rows):
    v=r[:]
    for (pc,b) in zip(piv,mat):
        if v[pc]!=0:
            f=v[pc]/b[pc]; v=[x-f*y for x,y in zip(v,b)]
    nz=[j for j,x in enumerate(v) if x!=0]
    if nz:
        piv.append(nz[0]); mat.append(v); basis.append(i)
print("rank",len(basis))
print("basis KN indices",basis)

# --- integer row reduction (Hermite-like) of the 55 x 256 KN matrix, tracking combinations ---
import copy
M=[r[:] for r in V]                          # integer rows
C=[[1 if i==j else 0 for j in range(n)] for i in range(n)]  # row i of M = sum C[i][k] * V[k]
pivrows=[]; pivcols=[]
r0=0
for col in range(m):
    # gcd elimination on column col among rows r0..
    while True:
        nz=[i for i in range(r0,n) if M[i][col]!=0]
        if not nz: break
        i0=min(nz,key=lambda i:abs(M[i][col]))
        M[r0],M[i0]=M[i0],M[r0]; C[r0],C[i0]=C[i0],C[r0]
        done=True
        for i in range(r0+1,n):
            if M[i][col]!=0:
                q=M[i][col]//M[r0][col]
                M[i]=[a-q*b for a,b in zip(M[i],M[r0])]; C[i]=[a-q*b for a,b in zip(C[i],C[r0])]
                if M[i][col]!=0: done=False
        if done: break
    if any(M[i][col]!=0 for i in range(r0,n)):
        if M[r0][col]<0: M[r0]=[-a for a in M[r0]]; C[r0]=[-a for a in C[r0]]
        pivrows.append(r0); pivcols.append(col); r0+=1
print("rank", r0, "pivot values", [M[i][c] for i,c in zip(pivrows,pivcols)])

# full reduction: make E_m(pivcol_n) = delta
E=[M[i][:] for i in pivrows]; CE=[C[i][:] for i in pivrows]
for a in range(len(E)-1,-1,-1):
    for b in range(len(E)):
        if b!=a and E[b][pivcols[a]]!=0:
            q=E[b][pivcols[a]]
            E[b]=[x-q*y for x,y in zip(E[b],E[a])]; CE[b]=[x-q*y for x,y in zip(CE[b],CE[a])]
assert all(E[a][pivcols[b]]==(1 if a==b else 0) for a in range(20) for b in range(20))
# check E = sum CE * V
for a in range(20):
    s=[sum(CE[a][k]*V[k][t] for k in range(n)) for t in range(m)]
    assert s==E[a]
piv_idx=[idx[c] for c in pivcols]
print("pivots", piv_idx)
print("max |coef|", max(abs(x) for r in CE for x in r), "nonzeros", sum(1 for r in CE for x in r if x))
import json
json.dump({"piv":piv_idx,"E":E,"CE":CE},open("/tmp/gu-f2/data.json","w"))
