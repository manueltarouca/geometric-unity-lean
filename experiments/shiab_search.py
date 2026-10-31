"""Search the draft's Shiab family for an operator Ω²→Ω^{n-1} (n=4) that
 (W) annihilates Weyl curvature, (E) maps a Riemann curvature to the Einstein form, and
 (S) has a symmetric or antisymmetric symbol pairing (needed for (9.7)).
Basis of candidates: all degree-compatible contractions built from Φ_r = Σ_{|I|=r} e^I⊗γ_I
with commutator / anticommutator brackets:
   A[b]       = b(Φ1 ∧ ⋆ξ)
   B[i,b,c]   = b(Φ_i ∧ ⋆ c(Φ_{i-1} ∧ ⋆ξ))          i=1..n
   C[i,b,c]   = ⋆ b(Φ_i ∧ ⋆ c(Φ_{i+1} ∧ ⋆ξ))        i=0..n-1
Linear constraints in the coefficients; solved by least squares (real and imaginary parts)."""
import itertools, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S

rng = np.random.default_rng(3)
plain = lambda a, b: a @ b if not (np.isscalar(a) or np.isscalar(b)) else a * b

def Phi(gam, r):
    n = len(gam); d = gam[0].shape[0]
    out = {}
    for I in itertools.combinations(range(n), r):
        M = np.eye(d, dtype=complex)
        for i in I: M = M @ gam[i]
        out[I] = M
    return out

def candidates(eta, gam):
    n = len(eta); P = [Phi(gam, r) for r in range(n + 1)]
    brs = [('[]', S.comm), ('{}', S.acomm)]
    ops = []
    for bn, b in brs:
        ops.append((f"A{bn}", lambda xi, b=b: S.wedge(P[1], S.star(xi, eta), b)))
    for i in range(1, n + 1):
        for (bn, b), (cn, c) in itertools.product(brs, brs):
            ops.append((f"B{i}{bn}{cn}", lambda xi, i=i, b=b, c=c:
                        S.wedge(P[i], S.star(S.wedge(P[i - 1], S.star(xi, eta), c), eta), b)))
    for i in range(0, n):
        for (bn, b), (cn, c) in itertools.product(brs, brs):
            ops.append((f"C{i}{bn}{cn}", lambda xi, i=i, b=b, c=c:
                        S.star(S.wedge(P[i], S.star(S.wedge(P[i + 1], S.star(xi, eta), c), eta), b), eta)))
    return ops

def flat(F, n, d, deg):
    keys = list(itertools.combinations(range(n), deg))
    return np.concatenate([np.asarray(F.get(k, np.zeros((d, d)))).ravel() for k in keys])

def search(eta, mode):
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    ops = candidates(eta, gam); K = len(ops)
    rows, rhs = [], []
    def add(cols, target):
        M = np.stack(cols, 1)
        rows.extend([M.real, M.imag]); rhs.extend([target.real, target.imag])
    for _ in range(3):  # Weyl annihilation
        R = S.algebraic_curvature(n, eta); W, _, _ = S.weyl_part(R, eta)
        xi = S.curv_form(W, gam, eta)
        add([flat(op(xi), n, d, n - 1) for _, op in ops], np.zeros(len(flat({}, n, d, n - 1)) or 1) if False else np.zeros_like(flat(ops[0][1](xi), n, d, n - 1)))
    for _ in range(3):  # Einstein output
        R = S.algebraic_curvature(n, eta); _, Ric, s = S.weyl_part(R, eta)
        xi = S.curv_form(R, gam, eta)
        target = flat(S.einstein_form(Ric, s, eta, gam, 0.5), n, d, n - 1)
        add([flat(op(xi), n, d, n - 1) for _, op in ops], target)
    if mode != 'none':  # symbol (anti)symmetry
        E = []
        for a in range(n):
            for i in range(d * d):
                M = np.zeros((d, d), complex); M.flat[i] = 1; E.append({(a,): M})
        top = tuple(range(n))
        for _ in range(1):
            xv = rng.normal(size=n); Xi = {(a,): xv[a] * np.eye(d) for a in range(n)}
            cols = []
            for _, op in ops:
                imgs = [op(S.wedge(Xi, b, plain)) for b in E]
                Sm = np.array([[np.trace(S.wedge(a, im, plain).get(top, np.zeros((d, d)))) for im in imgs] for a in E])
                cols.append((Sm - Sm.T if mode == 'sym' else Sm + Sm.T).ravel())
            add(cols, np.zeros(len(cols[0])))
    A = np.concatenate(rows, 0); bvec = np.concatenate(rhs, 0)
    c, *_ = np.linalg.lstsq(A, bvec, rcond=None)
    resid = np.linalg.norm(A @ c - bvec) / np.linalg.norm(bvec)
    nz = [(ops[k][0], round(c[k], 4)) for k in range(K) if abs(c[k]) > 1e-8]
    print(f"  η={eta} constraint={mode}: K={K} relative residual={resid:.2e}; nonzero coeffs: {nz[:12]}{' …' if len(nz) > 12 else ''}")

for eta in ([1, 1, 1, 1], [1, -1, -1, -1]):
    for mode in ('none', 'sym', 'antisym'):
        search(eta, mode)

def nullity_and_check(eta):
    """Dimension of the solution set (W, E, antisym) and an independent check of the
    explicit candidate  L = A[] + κ·(C1[][] + C1{}{}) with C0 terms eliminated."""
    n = len(eta); gam = S.clifford(eta); d = gam[0].shape[0]
    ops = dict(candidates(eta, gam))
    # explicit candidate: fit a, k on fresh samples using only A[] and C1[][]+C1{}{}
    R = S.algebraic_curvature(n, eta); _, Ric, s = S.weyl_part(R, eta)
    xi = S.curv_form(R, gam, eta)
    tgt = flat(S.einstein_form(Ric, s, eta, gam, 0.5), n, d, n - 1)
    cA = flat(ops['A[]'](xi), n, d, n - 1)
    cC = flat(ops['C1[][]'](xi), n, d, n - 1) + flat(ops['C1{}{}'](xi), n, d, n - 1)
    M = np.stack([cA, cC], 1); sol, *_ = np.linalg.lstsq(np.concatenate([M.real, M.imag]), np.concatenate([tgt.real, tgt.imag]), rcond=None)
    a, k = sol
    L = lambda x: S.add(ops['A[]'](x), S.add(ops['C1[][]'](x), ops['C1{}{}'](x)), 1.0) if False else \
        {key: a * ops['A[]'](x).get(key, 0) + k * (ops['C1[][]'](x).get(key, 0) + ops['C1{}{}'](x).get(key, 0))
         for key in set(ops['A[]'](x)) | set(ops['C1[][]'](x)) | set(ops['C1{}{}'](x))}
    # fresh checks
    R2 = S.algebraic_curvature(n, eta); W2, Ric2, s2 = S.weyl_part(R2, eta)
    eW = S.norm(L(S.curv_form(W2, gam, eta))) / S.norm(S.curv_form(W2, gam, eta))
    out = L(S.curv_form(R2, gam, eta)); E2 = S.einstein_form(Ric2, s2, eta, gam, 0.5)
    eE = np.linalg.norm(flat(out, n, d, n - 1) - flat(E2, n, d, n - 1)) / np.linalg.norm(flat(E2, n, d, n - 1))
    E = []
    for aa in range(n):
        for i in range(d * d):
            Mx = np.zeros((d, d), complex); Mx.flat[i] = 1; E.append({(aa,): Mx})
    xv = rng.normal(size=n); Xi = {(aa,): xv[aa] * np.eye(d) for aa in range(n)}; top = tuple(range(n))
    imgs = [L(S.wedge(Xi, b, plain)) for b in E]
    Sm = np.array([[np.trace(S.wedge(x, im, plain).get(top, np.zeros((d, d)))) for im in imgs] for x in E])
    print(f"  η={eta}: L = {a.real:.4f}·A[] + {k.real:.4f}·(C1[][] + C1{{}}{{}}); fresh: |L(Weyl)|={eW:.1e}, "
          f"|L(R)−Einstein|={eE:.1e}, |S+Sᵀ|/|S|={np.linalg.norm(Sm + Sm.T)/np.linalg.norm(Sm):.1e}")

if len(sys.argv) > 1 and sys.argv[1] == 'check':
    for eta in ([1, 1, 1, 1], [1, -1, -1, -1], [1, 1, 1, 1, 1, 1], [1, -1, -1, -1, 1, 1]):
        nullity_and_check(eta)
