# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
import json
from itertools import product
c=json.load(open("/tmp/gu-f2/cert.json")); d=json.load(open("/tmp/gu-f2/data.json"))
E=d["E"]; piv=[tuple(p) for p in c["piv"]]; kp=c["kp"]; sg=c["sg"]; cert=c["cert"]
R4=range(4); idx=list(product(R4,R4,R4,R4))
def mat4(f):  # nested ![...] for Fin4^4 -> Z
    return "!["+", ".join("!["+", ".join("!["+", ".join("!["+", ".join(str(f(a,b,cc,dd)) for dd in R4)+"]" for cc in R4)+"]" for b in R4)+"]" for a in R4)+"]"
L=[]
L.append("import GU.Shiab.FormsSpan\n")
L.append("""/-!
# Track 2, F2–F3: every integer algebraic curvature tensor, n = 4

`IsCurv R`: antisymmetry in each index pair, plus the first Bianchi identity (pair symmetry follows).
**`curv_span`**: every integer algebraic curvature tensor is `Σ_m R(p_m) • E_m` over 20 pivot
components `p_m`, where each `E_m` is a single Kulkarni–Nomizu tensor (`Etab_eq`, by `decide`; the
signs `sgT` are all `+1`). The 256 component identities are proved by `linarith`, with hints (the
needed symmetry instances) generated offline. Reproduce from `lean/` with
`python3 -I scripts/f2/kn.py && python3 -I scripts/f2/gen.py && python3 -I scripts/f2/emit.py`.
`isCurv_knT`: the KN tensors are algebraic curvature tensors (non-vacuity).
**`einstein_all_curv`**: for every integer algebraic curvature tensor, the doubled printed Shiab
of its curvature form equals `−4 ⋆(Einstein form)` on every index set. This supersedes the
"55 spanning tensors / linearity not formalised" caveat in `FormsEinstein.lean`. The integer
restriction is because `curvForm` takes `ℤ` coefficients; a real-linear version is open.
-/
""")
L.append("namespace GU.FormsW\n\nopen GU.Spinor\n")
L.append("""/-- Algebraic curvature tensors (pair antisymmetries and first Bianchi). -/
structure IsCurv (R : Tens) : Prop where
  h1 : ∀ a b c d, R a b c d = -R b a c d
  h2 : ∀ a b c d, R a b c d = -R a b d c
  h3 : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0
""")
def fin(x): return f"({x} : Fin 4)"
L.append("def pivT : Fin 20 → Fin 4 × Fin 4 × Fin 4 × Fin 4 := !["+", ".join(f"({a}, {b}, {cc}, {dd})" for (a,b,cc,dd) in piv)+"]\n")
L.append("def kpT : Fin 20 → (Fin 4 × Fin 4) × (Fin 4 × Fin 4) := !["+", ".join(f"(({p[0][0]}, {p[0][1]}), ({p[1][0]}, {p[1][1]}))" for p in kp)+"]\n")
L.append("def sgT : Fin 20 → ℤ := !["+", ".join(str(s) for s in sg)+"]\n")
L.append("/-- Basis tensors `E_m = sgT m • KN(kpT m)`. -/\ndef Eb (m : Fin 20) : Tens := sgT m • knT (kpT m)\n")
L.append("/-- Explicit table of the basis tensors. -/\ndef Etab : Fin 20 → Tens := !["+",\n  ".join(mat4(lambda a,b,cc,dd,mi=mi: E[mi][((a*4+b)*4+cc)*4+dd]) for mi in range(20))+"]\n")
L.append("set_option maxRecDepth 100000 in\ntheorem Etab_eq : ∀ m, Etab m = Eb m := by decide +kernel\n")
L.append("set_option maxRecDepth 100000 in\nlemma kpT_mem : ∀ m, kpT m ∈ knPairs := by decide +kernel\n")
L.append("set_option maxRecDepth 100000 in\n/-- Non-vacuity: the KN tensors are algebraic curvature tensors. -/\ntheorem isCurv_knT : ∀ p ∈ knPairs, (∀ a b c d, knT p a b c d = -knT p b a c d) ∧\n    (∀ a b c d, knT p a b c d = -knT p a b d c) ∧\n    (∀ a b c d, knT p a b c d + knT p a c d b + knT p a d b c = 0) := by decide +kernel\n")
L.append("set_option maxHeartbeats 8000000 in")
L.append("""/-- **Coordinates**: an algebraic curvature tensor is determined by its 20 pivot components. -/
theorem curv_coords (R : Tens) (hR : IsCurv R) (a b c d : Fin 4) :
    R a b c d = ∑ m : Fin 20, R (pivT m).1 (pivT m).2.1 (pivT m).2.2.1 (pivT m).2.2.2 * Etab m a b c d := by
  have h1 := hR.h1; have h2 := hR.h2; have h3 := hR.h3
  have q : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases q a with rfl | rfl | rfl | rfl <;> rcases q b with rfl | rfl | rfl | rfl <;>
    rcases q c with rfl | rfl | rfl | rfl <;> rcases q d with rfl | rfl | rfl | rfl""")
for t,ce in zip(idx,cert):
    import re
    insts=re.findall(r"(h[123] \d \d \d \d)", ce)
    hint=", ".join(insts)
    L.append(f"  · (simp [Fin.sum_univ_succ, pivT, Etab]) <;> linarith [{hint}]")
L.append("""
/-- **Spanning**: `R = Σ_m R(p_m) • E_m` with `E_m = ± KN`. -/
theorem curv_span (R : Tens) (hR : IsCurv R) :
    R = ∑ m : Fin 20, R (pivT m).1 (pivT m).2.1 (pivT m).2.2.1 (pivT m).2.2.2 • Eb m := by
  funext a b c d
  rw [curv_coords R hR a b c d]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Etab_eq]

/-- **Einstein output for every integer algebraic curvature tensor** (n = 4, Euclidean, printed
(9.3) with Hodge stars). -/
theorem einstein_all_curv (R : Tens) (hR : IsCurv R) (I : Idx4) :
    semF (twoShiab (curvForm R)) I = semF (einsteinForm R) I := by
  have hL : ∀ T : Tens, semF (twoShiab (curvForm T)) = twoShiabH (curvH T) := fun T =>
    funext (semF_twoShiab (canon_curvForm T))
  let D : Tens →+ (Idx4 → M128) := twoShiabH.comp curvH - einH
  have hD : ∀ m, D (Eb m) = 0 := fun m => by
    simp only [D, Eb, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, map_zsmul]
    rw [← hL]
    have := basis_eq (kpT m) (kpT_mem m)
    rw [show einH (knT (kpT m)) = semF (einsteinForm (knT (kpT m))) from rfl, ← this, sub_self, smul_zero]
  have hDR : D R = 0 := by
    rw [curv_span R hR, map_sum]
    exact Finset.sum_eq_zero fun m _ => by rw [map_zsmul, hD, smul_zero]
  have := congrFun hDR I
  simp only [D, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, Pi.sub_apply, Pi.zero_apply,
    sub_eq_zero] at this
  rw [hL]; exact this

end GU.FormsW
""")
open("GU/Shiab/FormsCurvSpan.lean","w").write("\n".join(L))
print("written", sum(len(x) for x in L), "chars")
