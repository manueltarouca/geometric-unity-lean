"""Re-run the (10.1) symbol-exactness test with the synthetic Shiab ⧉_GU
(= -1/2 A[] ± 1/4 (C1[][] + C1{}{}), see shiab_search.py)."""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S
import shiab_search as SS

rng = np.random.default_rng(5)
plain = lambda a, b: a @ b if not (np.isscalar(a) or np.isscalar(b)) else a * b

def run(eta, kappa):
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    ops = dict(SS.candidates(eta, gam))
    sg = 1.0 if np.prod(eta) > 0 else -1.0
    def shGU(x):
        a, c1, c2 = ops['A[]'](x), ops['C1[][]'](x), ops['C1{}{}'](x)
        keys = set(a) | set(c1) | set(c2)
        return {k: -0.5 * a.get(k, 0) + 0.25 * sg * (c1.get(k, 0) + c2.get(k, 0)) for k in keys}
    E = [np.zeros((d, d), complex) for _ in range(d * d)]
    for i in range(d * d): E[i].flat[i] = 1
    B1 = [(a,) for a in range(n)]
    xi = rng.normal(size=n); Xi = {(a,): xi[a] * np.eye(d) for a in range(n)}
    cols = [np.concatenate([SS.flat(S.wedge(Xi, {(): M}, plain), n, d, 1), np.zeros(d * d)]) for M in E]
    s1 = np.stack(cols, 1)
    cols = []
    for I in B1:
        for M in E:
            cols.append(SS.flat(shGU(S.wedge(Xi, {I: M}, plain)), n, d, n - 1))
    for M in E:
        cols.append(-kappa * SS.flat(S.star(S.wedge(Xi, {(): M}, plain), eta), n, d, n - 1))
    s2 = np.stack(cols, 1)
    r1, r2 = np.linalg.matrix_rank(s1, 1e-8), np.linalg.matrix_rank(s2, 1e-8)
    print(f"  η={eta} κ={kappa}: rank σ1={r1}, rank σ2={r2} of {s2.shape[0]}, middle dim {s1.shape[0]}, "
          f"exact={r1 + r2 == s1.shape[0]}, |σ2σ1|={np.linalg.norm(s2 @ s1):.1e}")

for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
    for kappa in (0.0, 1.0):
        run(eta, kappa)

def max_rank(eta, trials=3):
    """Max rank of σ2 over random combinations of ALL 34 family members (plus κ term)."""
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    ops = SS.candidates(eta, gam)
    E = [np.zeros((d, d), complex) for _ in range(d * d)]
    for i in range(d * d): E[i].flat[i] = 1
    xi = rng.normal(size=n); Xi = {(a,): xi[a] * np.eye(d) for a in range(n)}
    per = []
    for _, op in ops:
        per.append(np.stack([SS.flat(op(S.wedge(Xi, {(a,): M}, plain)), n, d, n - 1)
                             for a in range(n) for M in E], 1))
    kap = np.stack([SS.flat(S.star(S.wedge(Xi, {(): M}, plain), eta), n, d, n - 1) for M in E], 1)
    best = 0
    for _ in range(trials):
        c = rng.normal(size=len(per))
        s2 = np.concatenate([sum(ci * P for ci, P in zip(c, per)), rng.normal() * kap], 1)
        best = max(best, np.linalg.matrix_rank(s2, 1e-8))
    print(f"  η={eta}: max rank σ2 over the whole family = {best} of {kap.shape[0]} (need {kap.shape[0]} for ellipticity)")

if len(sys.argv) > 1 and sys.argv[1] == 'family':
    for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
        max_rank(eta)

def constrained_max_rank(eta, trials=6):
    """Max rank of σ2 over the affine space of operators satisfying (W), (E) and antisymmetry."""
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    SS.search(eta, MODE)
    A, b, ops = SS.LAST
    c0, *_ = np.linalg.lstsq(A, b, rcond=None)
    _, sv, Vt = np.linalg.svd(A)
    null = Vt[(sv > 1e-9 * sv[0]).sum():].T
    print(f"  η={eta}: solution space dimension = {null.shape[1]}")
    E = [np.zeros((d, d), complex) for _ in range(d * d)]
    for i in range(d * d): E[i].flat[i] = 1
    best = 0
    for _ in range(trials):
        xi = rng.normal(size=n); Xi = {(a,): xi[a] * np.eye(d) for a in range(n)}
        per = [np.stack([SS.flat(op(S.wedge(Xi, {(a,): M}, plain)), n, d, n - 1)
                         for a in range(n) for M in E], 1) for _, op in ops]
        kap = np.stack([SS.flat(S.star(S.wedge(Xi, {(): M}, plain), eta), n, d, n - 1) for M in E], 1)
        c = c0 + null @ rng.normal(size=null.shape[1]) if null.shape[1] else c0
        s2 = np.concatenate([sum(ci * P for ci, P in zip(c, per)), kap], 1)
        best = max(best, np.linalg.matrix_rank(s2, 1e-8))
    print(f"  η={eta}: max rank σ2 on the constrained space (κ=1) = {best} of {kap.shape[0]}")

MODE = 'antisym'
if len(sys.argv) > 1 and sys.argv[1] == 'constrained':
    for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
        constrained_max_rank(eta)

if len(sys.argv) > 2 and sys.argv[1] == 'constrained_mode':
    MODE = sys.argv[2]
    for eta in ([1, 1, 1, 1],):
        constrained_max_rank(eta)
