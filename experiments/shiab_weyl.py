# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
"""Numerical test of the draft's claim (§9.1): the Shiab operator (9.3)
    S(xi) = B1[Phi1 ^ *xi] - (1/2) * B2[Phi1 ^ * B3[Phi2 ^ *xi]]
annihilates the Weyl part of a Riemann-type curvature and returns an Einstein-like tensor.
Brackets B_i are either the commutator or the anticommutator (draft §8.1 / appendix).
Curvature: xi = sum R_abcd e^a^e^b (x) gamma^c gamma^d over a<b, c<d, for random algebraic
curvature tensors R (sums of Kulkarni-Nomizu products of symmetric matrices)."""
import itertools, sys
import numpy as np

rng = np.random.default_rng(0)

def clifford(eta):
    n = len(eta); m = (n + 1) // 2
    X = np.array([[0, 1], [1, 0]], complex); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1]).astype(complex); I = np.eye(2)
    gs = []
    for k in range(m):
        for P in (X, Y):
            mats = [Z] * k + [P] + [I] * (m - k - 1)
            g = mats[0]
            for M in mats[1:]:
                g = np.kron(g, M)
            gs.append(g)
    gs = gs[:n]
    return [g if eta[a] > 0 else 1j * g for a, g in enumerate(gs)]  # gamma_a^2 = eta_aa

def perm_sign(seq):
    seq = list(seq); s = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]: s = -s
            elif seq[i] == seq[j]: return 0
    return s

def wedge(A, B, br):
    out = {}
    for I, a in A.items():
        for J, b in B.items():
            s = perm_sign(I + J)
            if s == 0: continue
            K = tuple(sorted(I + J))
            out[K] = out.get(K, 0) + s * br(a, b)
    return out

def star(A, eta):
    n = len(eta); out = {}
    for I, a in A.items():
        Ic = tuple(i for i in range(n) if i not in I)
        # e^I ^ *e^I = <e^I,e^I> vol, <e^I,e^I> = prod eta_ii
        s = perm_sign(I + Ic) * np.prod([eta[i] for i in I])
        out[Ic] = out.get(Ic, 0) + s * a
    return out

def add(A, B, c=1.0):
    out = dict(A)
    for K, b in B.items(): out[K] = out.get(K, 0) + c * b
    return out

comm = lambda a, b: a @ b - b @ a
acomm = lambda a, b: a @ b + b @ a
mul = lambda a, b: a * b if np.isscalar(a) or np.isscalar(b) else a @ b

def algebraic_curvature(n, eta, k=6):
    R = np.zeros((n,) * 4)
    for _ in range(k):
        h = rng.normal(size=(n, n)); h = h + h.T
        q = rng.normal(size=(n, n)); q = q + q.T
        R += (np.einsum('ac,bd->abcd', h, q) + np.einsum('bd,ac->abcd', h, q)
              - np.einsum('ad,bc->abcd', h, q) - np.einsum('bc,ad->abcd', h, q))
    return R

def weyl_part(R, eta):
    n = len(eta); g = np.diag(eta); gi = np.diag(1 / np.array(eta, float))
    Ric = np.einsum('acbd,cd->ab', R, gi); s = np.einsum('ab,ab->', Ric, gi)
    P = (Ric - s / (2 * (n - 1)) * g) / (n - 2)  # Schouten
    KN = lambda h, q: (np.einsum('ac,bd->abcd', h, q) + np.einsum('bd,ac->abcd', h, q)
                       - np.einsum('ad,bc->abcd', h, q) - np.einsum('bc,ad->abcd', h, q))
    return R - KN(P, g), Ric, s

def curv_form(R, gam, eta):
    n = len(eta); F = {}
    gup = [gam[a] / eta[a] for a in range(n)]  # gamma^a
    for a, b in itertools.combinations(range(n), 2):
        M = sum(R[a, b, c, d] * gup[c] @ gup[d] for c, d in itertools.combinations(range(n), 2))
        F[(a, b)] = M
    return F

def shiab(xi, gam, eta, B1, B2, B3):
    n = len(eta)
    # Canonical invariant elements: Phi_r = sum_I e^I (x) gamma(e_I), with LOWER-index gammas.
    Phi1 = {(a,): gam[a] for a in range(n)}
    Phi2 = {(a, b): gam[a] @ gam[b] for a, b in itertools.combinations(range(n), 2)}
    sxi = star(xi, eta)
    t1 = wedge(Phi1, sxi, B1)
    inner = star(wedge(Phi2, sxi, B3), eta)        # 0-form
    t2 = star(wedge(Phi1, inner, B2), eta)          # (n-1)-form
    return t1, t2

def norm(A):
    return np.sqrt(sum(np.linalg.norm(v) ** 2 for v in A.values())) if A else 0.0

def einstein_form(Ric, s, eta, gam, coef):
    # *( sum_a e^a (x) (Ric_a^b - coef*s*delta_a^b) gamma_b )
    n = len(eta); gi = 1 / np.array(eta, float)
    G = Ric * gi[None, :] - coef * s * np.eye(n)
    one = {(a,): sum(G[a, b] * gam[b] for b in range(n)) for a in range(n)}
    return star(one, eta)

def fit(target, basis):
    keys = sorted(set().union(*[set(b) for b in basis], set(target)))
    shape = next(iter(target.values())).shape
    vec = lambda A: np.concatenate([np.asarray(A.get(k, np.zeros(shape))).ravel() for k in keys])
    M = np.stack([vec(b) for b in basis], 1); t = vec(target)
    c, *_ = np.linalg.lstsq(M, t, rcond=None)
    return c, np.linalg.norm(M @ c - t) / max(np.linalg.norm(t), 1e-30)

def run(eta):
    n = len(eta); gam = clifford(eta)
    names = {id(comm): '[,]', id(acomm): '{,}'}
    print(f"signature {eta}")
    for B1, B2, B3 in itertools.product([comm, acomm], repeat=3):
        R = algebraic_curvature(n, eta)
        W, Ric, s = weyl_part(R, eta)
        t1W, t2W = shiab(curv_form(W, gam, eta), gam, eta, B1, B2, B3)
        t1, t2 = shiab(curv_form(R, gam, eta), gam, eta, B1, B2, B3)
        scale = norm(curv_form(R, gam, eta))
        # Is t1 Ricci-like, t2 scalar-like?  Fit t1 ~ x*E(Ric), t2 ~ y*E(s g)
        ric = einstein_form(Ric, 0 * s, eta, gam, 0)
        sca = einstein_form(0 * Ric, s, eta, gam, -1)   # *(s * e^a gamma_a)
        c1, r1 = fit(t1, [ric]) if norm(t1) > 1e-9 * scale else ((0,), 0.0)
        c2, r2 = fit(t2, [sca]) if norm(t2) > 1e-9 * scale else ((0,), 0.0)
        print(f"  B1={names[id(B1)]} B2={names[id(B2)]} B3={names[id(B3)]}: "
              f"|t1(Weyl)|={norm(t1W)/scale:.1e} |t2(Weyl)|={norm(t2W)/scale:.1e} "
              f"|t1|={norm(t1)/scale:.2e} ricci-fit coef={np.real_if_close(c1[0]):.4g} resid={r1:.1e} "
              f"|t2|={norm(t2)/scale:.2e} scalar-fit coef={np.real_if_close(c2[0]):.4g} resid={r2:.1e}")

if __name__ == '__main__':
    for eta in ([1, -1, -1, -1], [1, 1, -1, -1], [1, -1, -1, -1, 1, 1]):
        run(eta)
