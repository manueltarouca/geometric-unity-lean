/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import Mathlib

/-!
# Fiber metric on `Y = Met(X)` and the (7,7) model (GU draft §3.1–3.5)

Gap M1. The draft says the traceless part has signature (3,6) and claims "a freedom to assign
(0,1) or (1,0)" to the trace direction (3.9). The form it writes down, `Tr_y(A·B)` (3.8), does
not realise that freedom: it fixes the trace direction's sign, giving (7,3) up to an overall
sign. Flipping the trace direction requires the DeWitt supermetric
`tr(g⁻¹Ag⁻¹B) - λ tr(g⁻¹A) tr(g⁻¹B)` with `λ > 1/4`. Getting (7,7) then needs one more sign:
only (6,4), not (4,6), combines with the base (1,3) to give (7,7); (4,6) gives (5,9).

Formalised here:
* `deWitt_traceless`: `λ` changes the metric only on the trace direction.
* `deWitt_trace_direction`: on that direction the norm is `4 - 16λ`; it is positive for the
  paper's `λ = 0` and negative exactly when `λ > 1/4`.
  (The (6,3) signature of the traceless block was checked numerically in Phase 1, not here.)
* The synthetic choice `Q77` (signature (7,7) on ℝ¹⁴), `Spin77`, and the vector-space
  isomorphism `ϑ : Cl(7,7) ≃ Λ*(ℝ¹⁴)` of (8.3) (typo `T*X` corrected to `T*Y`).
* The Clifford dimension counts (3.22), (3.26), (3.27), (8.6).
-/

namespace GU

open Matrix

section DeWitt

/-- DeWitt supermetric on symmetric 2-tensors at a metric with inverse `gi`.
`λ = 0` is the draft's Frobenius form (3.8). -/
def deWitt (lam : ℚ) (gi A B : Matrix (Fin 4) (Fin 4) ℚ) : ℚ :=
  trace (gi * A * gi * B) - lam * trace (gi * A) * trace (gi * B)

/-- Minkowski metric `η = diag(1,-1,-1,-1)`; it is its own inverse. -/
def η : Matrix (Fin 4) (Fin 4) ℚ := diagonal ![1, -1, -1, -1]

lemma η_mul_η : η * η = 1 := by
  rw [η, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i; fin_cases i <;> simp

/-- `λ` only affects the trace direction. -/
theorem deWitt_traceless (lam : ℚ) (gi A B : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : trace (gi * A) = 0) : deWitt lam gi A B = deWitt 0 gi A B := by
  simp [deWitt, hA]

/-- Norm of the trace direction `A = g` at `g = η`. -/
theorem deWitt_trace_direction (lam : ℚ) : deWitt lam η η η = 4 - 16 * lam := by
  simp only [deWitt, η_mul_η, one_mul, trace_one, Fintype.card_fin]
  norm_num; ring

/-- With the draft's literal form (`λ = 0`) the trace direction is positive. -/
theorem frobenius_trace_direction_pos : 0 < deWitt 0 η η η := by
  rw [deWitt_trace_direction]; norm_num

/-- The trace direction flips sign exactly when `λ > 1/4`, the condition behind (6,4). -/
theorem trace_direction_neg_iff (lam : ℚ) : deWitt lam η η η < 0 ↔ 1 / 4 < lam := by
  rw [deWitt_trace_direction]; constructor <;> intro h <;> linarith

end DeWitt

noncomputable section Model77

/-- Synthetic choice closing gap M1: the split form of signature (7,7) on `ℝ¹⁴`
(base (1,3) ⊕ DeWitt fiber (6,4) with `λ > 1/4`). -/
def Q77 : QuadraticForm ℝ (Fin 14 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1)

/-- `Cl(7,7)`. -/
abbrev Cl77 := CliffordAlgebra Q77

/-- `Spin(7,7)` as Mathlib's algebraic spin group (no topology: roadblock R4). Mathlib's
`spinGroup` requires spinor norm `x* x = 1`; its image in `SO(7,7)` is the spinor-norm kernel
`SO⁺(7,7)` (`range_vecRep`). This is the identity component `SO₀(7,7)` of the matrix group `O(7,7)` (`cc_iff_spin`). -/
abbrev Spin77 := spinGroup Q77


/-- (8.3), corrected to `T*Y`: `ϑ : Cl(T*Y) ≃ Λ*(T*Y)` as vector spaces. -/
def ϑ : Cl77 ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin 14 → ℝ) :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  CliffordAlgebra.equivExterior Q77

end Model77

section CliffordCounts

/-- (3.22): `gl(64,ℝ) "=" Λ² ⊕ Λ⁶ ⊕ Λ¹⁰ ⊕ Λ¹⁴`. -/
theorem dim_gl64 : Nat.choose 14 2 + Nat.choose 14 6 + Nat.choose 14 10 + Nat.choose 14 14
    = 64 ^ 2 := by decide

/-- (3.26): `so(64,64)` adds `Λ¹ ⊕ Λ⁵ ⊕ Λ⁹ ⊕ Λ¹³`. -/
theorem dim_so6464 : (Nat.choose 14 2 + Nat.choose 14 6 + Nat.choose 14 10 + Nat.choose 14 14) +
    (Nat.choose 14 1 + Nat.choose 14 5 + Nat.choose 14 9 + Nat.choose 14 13) = 128 * 127 / 2 := by
  decide

/-- (3.27): `u(64,64)` is all of `Cl_ℂ(7,7)` as a real vector space of dimension `128²`. -/
theorem dim_u6464 : (List.range 15).foldr (fun k s => Nat.choose 14 k + s) 0 = 128 ^ 2 := by
  decide

/-- (8.6): `u(64,64)/so(64,64) "=" Λ⁰ ⊕ Λ³ ⊕ Λ⁴ ⊕ Λ⁷ ⊕ Λ⁸ ⊕ Λ¹¹ ⊕ Λ¹²`. -/
theorem dim_u_mod_so : Nat.choose 14 0 + Nat.choose 14 3 + Nat.choose 14 4 + Nat.choose 14 7 +
    Nat.choose 14 8 + Nat.choose 14 11 + Nat.choose 14 12 = 128 ^ 2 - 128 * 127 / 2 := by
  decide

/-- (4.2)/(4.3): Weyl "internal" dimension for signature (1,3) is `2^4 = 16`. -/
theorem internal_weyl_dim :
    2 ^ ((1 ^ 2 + 3 ^ 2 + 2 * 1 * 3 + 1 + 3 - 4) / 4) = 16 := by decide

end CliffordCounts

end GU
