"""Does the non-identity component of Spin(n,n) preserve the invariant spinor forms?

Superseded by lean/GU/Bundle/TwoComponent.lean (`flip_hyp`, `flip_omega`, `flip_nonidentity`): proved
for every Spin+-invariant form, with no irreducibility assumption. Kept as a numerical cross-check.

Real Clifford module of Cl(n,n) on R^(2^n). g = e0 f0 (one spacelike, one timelike unit vector) lies in
the two-component Spin(n,n), outside its identity component. For n <= 5 the script computes all bilinear
forms invariant under the bivectors (the Lie algebra) and checks g^T C g = -C. For n = 7 the null space is
too large for a dense SVD, so it checks the two explicit forms prod(E) and prod(F), which are invariant
and independent, and which span the invariant forms if S+ and S- are irreducible,
inequivalent and of real type (true in split signature: Cl0(7,7) = R(64) + R(64)).
Numerical check, not a proof. The hand argument: for C with C v C^-1 = +-v^T, C(v x, v y) = +-v^2 C(x, y),
so an even product scales C by (-1)^(number of timelike vectors).
Run: uv run --no-project --with numpy python -I experiments/spin_form_sign.py
"""
import numpy as np

sx = np.array([[0, 1], [1, 0.0]])
sz = np.array([[1, 0], [0, -1.0]])
e = np.array([[0, 1], [-1, 0.0]])
I2 = np.eye(2)


def kron(*a):
    r = np.eye(1)
    for m in a:
        r = np.kron(r, m)
    return r


def gens(n):
    E, F = [], []
    for k in range(n):
        pre, post = [sz] * k, [I2] * (n - k - 1)
        E.append(kron(*pre, sx, *post))
        F.append(kron(*pre, e, *post))
    return E, F


def prod(ms):
    r = np.eye(ms[0].shape[0])
    for m in ms:
        r = r @ m
    return r


for n in [1, 2, 3, 4, 5, 7]:
    E, F = gens(n)
    G, N = E + F, 2**n
    for i, a in enumerate(G):
        for j, b in enumerate(G):
            want = (1 if i < n else -1) * 2 * np.eye(N) if i == j else 0 * np.eye(N)
            assert np.allclose(a @ b + b @ a, want)
    bivs = [G[i] @ G[j] for i in range(2 * n) for j in range(i + 1, 2 * n)]
    g = E[0] @ F[0]
    if n <= 5:
        M = np.vstack([np.kron(np.eye(N), A.T) + np.kron(A.T, np.eye(N)) for A in bivs])
        _, s, vt = np.linalg.svd(M, full_matrices=True)
        forms = [v.reshape(N, N, order="F") for v in vt[(s > 1e-9).sum():]]
    else:
        forms = [prod(E), prod(F)]
    for C in forms:
        assert all(np.allclose(A.T @ C + C @ A, 0) for A in bivs)
    flips = all(np.allclose(g.T @ C @ g, -C) for C in forms)
    Gam = prod(G)
    print(f"Cl({n},{n}): {len(forms)} invariant forms; g = e0 f0 scales each by -1: {flips}; "
          f"g commutes with chirality: {np.allclose(g @ Gam, Gam @ g)}")
