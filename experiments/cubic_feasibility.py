"""Careful cubic-feasibility test: solution space of {W, E, antisym} (basis N, particular c0), then
cubic rows C_k = L - kR from many samples (more equations than the solution-space dimension).
Reports rank(C N), sample count, and the best relative residual |C(c0+Nz)| / |C c0| over k."""
import sys, io, contextlib
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S
import shiab_search as SS

def run(twist, nsamp):
    SS.TWIST = twist; SS.CUBIC = False
    eta = [1, 1, 1, 1]; n = 4; gam = S.clifford(eta); d = 4
    with contextlib.redirect_stdout(io.StringIO()):
        SS.search(eta, 'antisym')
    A, b, ops = SS.LAST
    c0, *_ = np.linalg.lstsq(A, b, rcond=None)
    _, s, vh = np.linalg.svd(A); N = vh[(s > 1e-9 * s[0]).sum():].T
    rng = np.random.default_rng(99); top = (0, 1, 2, 3); plain = lambda x, y: x @ y
    L, R = [], []
    for _ in range(nsamp):
        T = {(i,): rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for i in range(n)}
        al = {(i,): rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for i in range(n)}
        X1 = S.add(S.wedge(al, T, S.comm), S.wedge(T, al, S.comm)); X2 = S.wedge(T, T, S.comm)
        L.append([np.trace(S.wedge(T, op(X1), plain).get(top, np.zeros((d, d)))) for _, op in ops])
        R.append([np.trace(S.wedge(al, op(X2), plain).get(top, np.zeros((d, d)))) for _, op in ops])
    L, R = np.array(L), np.array(R)
    best = (1e9, None)
    for k in np.round(np.arange(-4, 6.01, 0.1), 2):
        C = L - k * R; M = C @ N
        z, *_ = np.linalg.lstsq(np.concatenate([M.real, M.imag]), np.concatenate([(-C @ c0).real, (-C @ c0).imag]), rcond=None)
        r = np.linalg.norm(C @ (c0 + N @ z)) / max(np.linalg.norm(C @ c0), 1e-30)
        if r < best[0]: best = (r, k, np.linalg.matrix_rank(np.concatenate([M.real, M.imag]), 1e-8))
    print(f"  twist={twist}: K={len(ops)}, solution-space dim={N.shape[1]}, cubic real equations={2*nsamp}, "
          f"best relative residual={best[0]:.2e} at k={best[1]}, rank(C·N)={best[2]}")

for twist in (False, True):
    run(twist, 150)
