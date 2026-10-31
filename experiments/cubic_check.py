"""Cubic-term test for (9.4)→(9.7): the variation of ⅓Tr(T∧⧉[T,T]) is ⟨α, ⧉[T,T]⟩ only if
Tr(T∧⧉(α∧T + T∧α)) = k·Tr(α∧⧉(T∧T)) with a universal k (k = 2 for Chern–Simons).
Brackets inside [T,T]: commutator-wedge. Reports the ratio over random samples."""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S
import shiab_search as SS
rng = np.random.default_rng(7)
eta = [1, 1, 1, 1]; n = 4; gam = S.clifford(eta); d = 4
ops = dict(SS.candidates(eta, gam))
def shGU(x):
    a, c1, c2 = ops['A[]'](x), ops['C1[][]'](x), ops['C1{}{}'](x)
    return {k: -0.5 * a.get(k, 0) + 0.25 * (c1.get(k, 0) + c2.get(k, 0)) for k in set(a) | set(c1) | set(c2)}
plain = lambda a, b: a @ b if not (np.isscalar(a) or np.isscalar(b)) else a * b
rnd1 = lambda: {(i,): rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for i in range(n)}
top = (0, 1, 2, 3)
tr = lambda F: np.trace(F.get(top, np.zeros((d, d))))
for _ in range(4):
    T, al = rnd1(), rnd1()
    lhs = tr(S.wedge(T, shGU(S.add(S.wedge(al, T, S.comm), S.wedge(T, al, S.comm))), plain))
    rhs = tr(S.wedge(al, shGU(S.wedge(T, T, S.comm)), plain))
    print(f"  ratio = {lhs / rhs:.4f}")
