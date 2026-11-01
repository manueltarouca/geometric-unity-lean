# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
"""Is the Shiab-based first-order operator (anti)self-adjoint at symbol level, as (9.7) needs?
S(α, β) = Tr( α ∧ ⧉(ξ ∧ β) )|_top for ad-valued 1-forms α, β (ad = full Clifford algebra).
Report the symmetric and antisymmetric parts' norms for the Einstein-type bracket choice and
for the alternatives."""
import itertools, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S

rng = np.random.default_rng(2)
plain = lambda a, b: a @ b if not (np.isscalar(a) or np.isscalar(b)) else a * b

def run(eta, brackets, label):
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    E = []
    for a in range(n):
        for i in range(d * d):
            M = np.zeros((d, d), complex); M.flat[i] = 1
            E.append({(a,): M})
    xi = rng.normal(size=n)
    Xi = {(a,): xi[a] * np.eye(d) for a in range(n)}
    top = tuple(range(n))
    imgs = []
    for b in E:
        t1, t2 = S.shiab(S.wedge(Xi, b, plain), gam, eta, *brackets)
        imgs.append(S.add(t1, t2, -0.5))
    N = len(E); Sm = np.zeros((N, N), complex)
    for i, a in enumerate(E):
        for j, sh in enumerate(imgs):
            w = S.wedge(a, sh, plain)
            Sm[i, j] = np.trace(w.get(top, np.zeros((d, d))))
    sym, asym = np.linalg.norm(Sm + Sm.T), np.linalg.norm(Sm - Sm.T)
    print(f"  {label} η={eta}: |S|={np.linalg.norm(Sm):.3e}  |S+Sᵀ|={sym:.3e}  |S−Sᵀ|={asym:.3e}")

for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
    run(eta, (S.comm, S.acomm, S.acomm), "Einstein ([,],{,},{,})")
    run(eta, (S.comm, S.comm, S.comm), "uniform [,]")
    run(eta, (S.acomm, S.acomm, S.acomm), "uniform {,}")
