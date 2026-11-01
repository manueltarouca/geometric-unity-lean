/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TwoComponent
import GU.Spinor.SpinComponent

/-!
# Phase 7, item 1: the components of `O(7,7)`

**`mem_SO0_iff`**: `g ∈ O(7,7)` lies in the identity component `SO₀` iff `tdet g > 0` and `det g > 0`.

Proof: if `det g = 1`, then by the reflection decomposition (`mem_or_g0_mul_mem`, `SpinImage.lean`) either
`g` or `g₀ g` is in the image of `Spin(7,7)`, which is `SO₀` (`spinToO77_mem`, `range_ρ`); here `g₀ = r_{e₀} r_{e₇}`. On
`SO₀` the sign of `tdet (g₀ h)` is constant (`tdet` never vanishes on `O(7,7)`, `SO₀` is connected) and
equal to `tdet g₀ = −1`, so the second case forces `tdet g < 0`.

Consequences: **`SO77_eq`** (`SO(7,7) := {det = 1} = SO₀ ∪ (−1)·SO₀`) and **`range_toO_eq`**: the map `toO`
of the two-component group (Phase 6 item 6) is onto `SO(7,7)`.
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- An element of `O(7,7)` is an isometry of `Q77`. -/
lemma isIsom77_of_mem (g : O77) : IsIsom77 (Matrix.toLin' (Matrix.of (g : Mat 14))) :=
  (mem_O77_iff_IsoSet _).mp g.2

/-- `g₀` as an element of `O(7,7)`. -/
def g0O : O77 := ⟨Matrix.of.symm (Matrix.diagonal dg0), by
  rw [mem_Orth_iff_mat]
  show (Matrix.diagonal dg0)ᵀ * Matrix.diagonal (fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1) *
    Matrix.diagonal dg0 = Matrix.diagonal (fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1)
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; unfold dg0; split_ifs <;> ring⟩

lemma g0O_sq : g0O * g0O = 1 := by
  apply Subtype.ext
  show mulM _ _ = Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)
  unfold mulM
  show Matrix.of.symm (Matrix.diagonal dg0 * Matrix.diagonal dg0) = _
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 2; funext i; unfold dg0; split_ifs <;> norm_num

lemma tdet_g0O : tdet (g0O : Mat 14) = -1 := by
  have : posBlock (g0O : Mat 14) = Matrix.diagonal fun a : Fin 7 => dg0 (Fin.castAdd 7 a) := by
    ext a b
    show (Matrix.diagonal dg0) (Fin.castAdd 7 a) (Fin.castAdd 7 b) = _
    by_cases h : a = b
    · subst h; simp
    · have h' : (Fin.castAdd 7 a : Fin (7 + 7)) ≠ Fin.castAdd 7 b := fun e => h (Fin.castAdd_injective _ _ e)
      rw [Matrix.diagonal_apply_ne _ h', Matrix.diagonal_apply_ne _ h]
  unfold tdet
  rw [this, Matrix.det_diagonal, Fin.prod_univ_seven]
  norm_num [dg0, Fin.ext_iff]

/-- **On `SO₀`, `tdet (g₀ h) < 0`.** -/
lemma tdet_g0O_mul_neg {h : O77} (hh : h ∈ SO0) : tdet ((g0O * h : O77) : Mat 14) < 0 := by
  set S : Set O77 := {k | tdet ((g0O * k : O77) : Mat 14) < 0}
  have hcont : Continuous fun k : O77 => tdet ((g0O * k : O77) : Mat 14) :=
    continuous_tdet.comp (continuous_const.mul continuous_id)
  have hS : S = {k | ¬ 0 < tdet ((g0O * k : O77) : Mat 14)} := by
    ext k
    simp only [S, Set.mem_ofPred_eq, not_lt]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (tdet_ne_zero _)⟩
  have hc : IsClopen S := by
    refine ⟨?_, isOpen_lt hcont continuous_const⟩
    rw [hS]
    exact (isOpen_lt continuous_const hcont).isClosed_compl
  have h1 : (1 : O77) ∈ S := by
    show tdet ((g0O * 1 : O77) : Mat 14) < 0
    rw [mul_one, tdet_g0O]; norm_num
  exact hc.connectedComponent_subset h1 hh

lemma spinToO77_eq_of_vecRep {x : Spin77} {g : O77}
    (h : ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) =
      Matrix.toLin' (Matrix.of (g : Mat 14))) : spinToO77 x = g := by
  apply Subtype.ext
  show Matrix.of.symm (LinearMap.toMatrix' (vecRep x : Module.End ℝ (Fin 14 → ℝ))) = (g : Mat 14)
  rw [h, LinearMap.toMatrix'_toLin']
  rfl

lemma toLin'_g0O_mul (g : O77) :
    g0 * Matrix.toLin' (Matrix.of (g : Mat 14)) = Matrix.toLin' (Matrix.of ((g0O * g : O77) : Mat 14)) := by
  show g0 * _ = Matrix.toLin' (Matrix.of (mulM _ _))
  unfold mulM
  rw [Equiv.apply_symm_apply, Matrix.toLin'_mul]
  congr 1
  show g0 = Matrix.toLin' (Matrix.diagonal dg0)
  rw [← toMatrix_g0, Matrix.toLin'_toMatrix']

/-- **The identity component of `O(7,7)`**: `g ∈ SO₀` iff `tdet g > 0` and `det g > 0`. -/
theorem mem_SO0_iff (g : O77) :
    g ∈ SO0 ↔ 0 < tdet (g : Mat 14) ∧ 0 < (Matrix.of (g : Mat 14)).det := by
  constructor
  · intro hg
    exact ⟨tdet_pos_of_mem_SO0 hg, by rw [det_SO0 hg]; exact one_pos⟩
  · rintro ⟨ht, hd⟩
    have hdet : (Matrix.of (g : Mat 14)).det = 1 := by
      have := det_sq_O77 g
      nlinarith [this, hd]
    rcases mem_or_g0_mul_mem _ (isIsom77_of_mem g) (by rw [LinearMap.det_toLin']; exact hdet) with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · rw [← spinToO77_eq_of_vecRep hx]; exact spinToO77_mem x
    · exfalso
      rw [toLin'_g0O_mul] at hx
      have e := spinToO77_eq_of_vecRep hx
      have hg : g = g0O * spinToO77 x := by rw [e, ← mul_assoc, g0O_sq, one_mul]
      have := tdet_g0O_mul_neg (spinToO77_mem x)
      rw [← hg] at this
      linarith

/-- **`SO(7,7) = SO₀ ∪ (−1)·SO₀`.** -/
theorem SO77_eq (g : O77) :
    (Matrix.of (g : Mat 14)).det = 1 ↔ g ∈ SO0 ∨ negO * g ∈ SO0 := by
  constructor
  · intro hd
    rcases lt_or_gt_of_ne (tdet_ne_zero g) with ht | ht
    · right
      rw [mem_SO0_iff]
      have e : ((negO * g : O77) : Mat 14) = Matrix.of.symm (-(Matrix.of (g : Mat 14))) := by
        show mulM _ _ = _
        unfold mulM
        show Matrix.of.symm ((-1 : Matrix (Fin 14) (Fin 14) ℝ) * Matrix.of (g : Mat 14)) = _
        rw [neg_one_mul]
      rw [e]
      constructor
      · have hp : posBlock (Matrix.of.symm (-(Matrix.of (g : Mat 14)))) = -posBlock (g : Mat 14) := by
          ext a b; rfl
        unfold tdet at ht ⊢
        rw [hp, Matrix.det_neg]
        simp
        linarith
      · show 0 < (-(Matrix.of (g : Mat 14))).det
        rw [Matrix.det_neg, hd]; norm_num
    · left
      exact (mem_SO0_iff g).mpr ⟨ht, by rw [hd]; exact one_pos⟩
  · rintro (h | h)
    · exact det_SO0 h
    · have := det_SO0 h
      have e : (Matrix.of ((negO * g : O77) : Mat 14)).det = (Matrix.of (g : Mat 14)).det := by
        show (Matrix.of (mulM _ _)).det = _
        unfold mulM
        rw [Equiv.apply_symm_apply, det_mul]
        show (Matrix.of (Matrix.of.symm (-1 : Matrix (Fin 14) (Fin 14) ℝ))).det * _ = _
        simp [Matrix.det_neg]; norm_num
      rw [← e]; exact this

/-- **The two-component group maps onto `SO(7,7)`** (closes the open clause of Phase 6 item 6). -/
theorem range_toO_eq : Set.range toO = {g : O77 | (Matrix.of (g : Mat 14)).det = 1} := by
  rw [range_toO]
  ext g
  exact (SO77_eq g).symm

end

end GU.Library
