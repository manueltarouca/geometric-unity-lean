# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
"""Principal-symbol test of the bosonic deformation complex (10.1)/(10.3)/(10.9):
    Ω0(ad) --δ1--> Ω1(ad) ⊕ Ω0(ad) --δ2--> Ω^{n-1}(ad)
with δ1 = (d_A, DL_ε)          symbol σ1(φ) = (ξ⊗φ, 0)          (DL_ε is zeroth order)
     δ2 = (⧉∘d_A + κ*, F∧⧉ − κ ⋆ d_B)  symbol σ2(α, φ) = ⧉(ξ∧α) − κ ⋆(ξ⊗φ)
⧉ is the Einstein-type Shiab (commutator, anticommutator, anticommutator), Φ_r = Σ e^I⊗γ_I.
ad is modelled by all of gl(2^{n/2}, C) (Clifford algebra as matrices).
Ellipticity <=> the symbol sequence is exact for every ξ ≠ 0."""
import itertools, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S

rng = np.random.default_rng(1)

def basis_forms(n, k):
    return list(itertools.combinations(range(n), k))

def run(eta, kappa):
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    E = [np.zeros((d, d), complex) for _ in range(d * d)]
    for i in range(d * d): E[i].flat[i] = 1
    B0, B1, Bn1 = basis_forms(n, 0), basis_forms(n, 1), basis_forms(n, n - 1)
    def vec(F, Bk):
        return np.concatenate([np.asarray(F.get(I, np.zeros((d, d)))).ravel() for I in Bk])
    xi = rng.normal(size=n)
    Xi = {(a,): xi[a] * np.eye(d) for a in range(n)}   # ξ as an ad-scalar 1-form
    plain = lambda a, b: a @ b if not (np.isscalar(a) or np.isscalar(b)) else a * b
    # σ1 : Λ0⊗ad → (Λ1⊗ad) ⊕ (Λ0⊗ad)
    cols = []
    for M in E:
        img1 = S.wedge(Xi, {(): M}, plain)
        cols.append(np.concatenate([vec(img1, B1), np.zeros(d * d)]))
    s1 = np.stack(cols, 1)
    # σ2 : (Λ1⊗ad) ⊕ (Λ0⊗ad) → Λ^{n-1}⊗ad
    cols = []
    for I in B1:
        for M in E:
            two = S.wedge(Xi, {I: M}, plain)
            t1, t2 = S.shiab(two, gam, eta, S.comm, S.acomm, S.acomm)
            sh = S.add(t1, t2, -0.5)
            cols.append(vec(sh, Bn1))
    for M in E:
        one = S.wedge(Xi, {(): M}, plain)
        cols.append(-kappa * vec(S.star(one, eta), Bn1))
    s2 = np.stack(cols, 1)
    r1, r2 = np.linalg.matrix_rank(s1, 1e-8), np.linalg.matrix_rank(s2, 1e-8)
    comp = np.linalg.norm(s2 @ s1)
    mid = s1.shape[0]
    print(f"  η={eta} κ={kappa}: dims {d*d} → {mid} → {s2.shape[0]}; rank σ1={r1}, rank σ2={r2}, "
          f"|σ2σ1|={comp:.1e}, exact at middle: {r1 + r2 == mid}, σ2 onto: {r2 == s2.shape[0]}")

for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
    for kappa in (0.0, 1.0):
        run(eta, kappa)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'more':
    print("dimension 6 (Euclidean, (3,3)):")
    for eta in ([1] * 6, [1, 1, 1, -1, -1, -1]):
        run(eta, 1.0)
