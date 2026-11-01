# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
"""Run the Shiab (9.3) test at the draft's actual signature (7,7) with the Einstein-type bracket
choice (B1, B2, B3) = (commutator, anticommutator, anticommutator), using 128x128 gammas."""
import sys, time
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import shiab_weyl as S

eta = [1] * 7 + [-1] * 7
n = 14; gam = S.clifford(eta)
t0 = time.time()
R = S.algebraic_curvature(n, eta, k=3)
W, Ric, s = S.weyl_part(R, eta)
F, FW = S.curv_form(R, gam, eta), S.curv_form(W, gam, eta)
scale = S.norm(F)
t1W, t2W = S.shiab(FW, gam, eta, S.comm, S.acomm, S.acomm)
t1, t2 = S.shiab(F, gam, eta, S.comm, S.acomm, S.acomm)
ric = S.einstein_form(Ric, 0 * s, eta, gam, 0)
sca = S.einstein_form(0 * Ric, s, eta, gam, -1)
c1, r1 = S.fit(t1, [ric]); c2, r2 = S.fit(t2, [sca])
print(f"(7,7): |t1(W)|/|F|={S.norm(t1W)/scale:.1e} |t2(W)|/|F|={S.norm(t2W)/scale:.1e}")
print(f"  t1 = {np.real_if_close(c1[0]):.6g} * *(Ric gamma)  resid {r1:.1e}")
print(f"  t2 = {np.real_if_close(c2[0]):.6g} * *(R e^a gamma_a)  resid {r2:.1e}")
print(f"  ({time.time()-t0:.0f}s)")
