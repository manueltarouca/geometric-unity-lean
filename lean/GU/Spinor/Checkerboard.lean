import GU.Spinor.Pauli
import GU.Spinor.Dirac

/-!
# The Clifford checkerboard (3.26)–(3.27), verified exhaustively (draft footnote 3)

For every subset `I ⊆ {0,…,13}` let `γ_I` be the ordered product of the generators. Then
`γ_Iᵀ C = ε_{|I|} C γ_I` with `ε_k = −1` for `k ≡ 1,2 (mod 4)` and `+1` for `k ≡ 0,3 (mod 4)`
(`checkerboard`, all 16384 monomials checked by `decide`). Consequently:
* `so(C) = so(64,64)` is spanned by grades `1,2,5,6,9,10,13,14`, as in (3.26);
* `u(C) = u(64,64)` adds `i·`(grades `0,3,4,7,8,11,12`), as in (3.27).
The draft's footnote 3 says this decomposition "should be checked": it is correct.
-/

namespace GU.Spinor

open Matrix

namespace PString

/-- Transpose of a string: `tprod(f)ᵀ = ∏ tr(f j) · tprod(f)`. -/
def transposeP (p : PString) : PString := ⟨p.s * ∏ j, F2.tr (p.f j), p.f⟩

theorem toMat_transposeP (p : PString) : (p.toMat)ᵀ = (transposeP p).toMat := by
  simp only [toMat, transposeP, transpose_smul, tprod_transpose]
  simp_rw [F2.transpose]
  rw [tprod_smul, smul_smul, Int.cast_mul, Int.cast_prod]

/-- Integer scaling. -/
def zsmul (c : ℤ) (p : PString) : PString := ⟨c * p.s, p.f⟩

theorem toMat_zsmul (c : ℤ) (p : PString) : (zsmul c p).toMat = (c : ℝ) • p.toMat := by
  simp [toMat, zsmul, smul_smul]

end PString

/-- The spinor form as a string. -/
def CP : PString := ⟨1, csym⟩

theorem toMat_CP : CP.toMat = C := by simp [PString.toMat, CP, C]

/-- Generators of a subset encoded as a 14-bit mask. -/
def maskGens (m : ℕ) : List Gen := ((List.finRange 14).filter fun i => m.testBit i.val).map gen

def eps (k : ℕ) : ℤ := if k % 4 = 1 ∨ k % 4 = 2 then -1 else 1

def checkMask (m : ℕ) : Bool :=
  let G := gprod (maskGens m)
  PString.beq (PString.transposeP G * CP) (PString.zsmul (eps (maskGens m).length) (CP * G))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkerboard_all : (List.range 16384).all checkMask = true := by decide +kernel

/-- **Checkerboard**: `γ_Iᵀ C = ε_{|I|} C γ_I` for every monomial. -/
theorem checkerboard (m : ℕ) (hm : m < 16384) :
    ((maskGens m).map gamma).prod.transpose * C =
      (eps (maskGens m).length : ℝ) • (C * ((maskGens m).map gamma).prod) := by
  have h := PString.eq_of_beq (List.all_eq_true.mp checkerboard_all m (List.mem_range.mpr hm))
  have := congrArg PString.toMat h
  rw [PString.toMat_mul, PString.toMat_zsmul, PString.toMat_mul, ← PString.toMat_transposeP,
    toMat_CP, toMat_gprod] at this
  exact this

end GU.Spinor
