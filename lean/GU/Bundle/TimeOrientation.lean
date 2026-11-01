/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SpinTwist

/-!
# Phase 4, item 4: the time-orientation invariant of `O(7,7)`

`tdet M` is the determinant of the positive `7 × 7` block of `M`. On `O(7,7)` it never vanishes
(`tdet_ne_zero`), and it is positive on the identity component `SO₀` (`tdet_pos_of_mem_SO0`).
`gHol` is the diagonal element of `O(7,7)` that is the holonomy of the metric loop of
`MetricLoop.lean`; `tdet gHol = −1`, so `gHol ∉ SO₀` (`gHol_not_mem_SO0`), although `det gHol = 1` (`det_gHol`, `SO0Reduction.lean`).
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The positive block. -/
def posBlock (M : Mat 14) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of fun a b => M (Fin.castAdd 7 a) (Fin.castAdd 7 b)

/-- The time-orientation invariant. -/
def tdet (M : Mat 14) : ℝ := (posBlock M).det

lemma Bm_self (w : Fin 14 → ℝ) :
    Bm w w = ∑ a : Fin 7, w (Fin.castAdd 7 a) ^ 2 - ∑ b : Fin 7, w (Fin.natAdd 7 b) ^ 2 := by
  rw [← Q77_eq_Bm, Q77, QuadraticMap.weightedSumSquares_apply]
  rw [show (∑ i : Fin 14, _) = _ from Fin.sum_univ_add (a := 7) (b := 7) _]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have : ((Fin.castAdd 7 a : Fin (7 + 7)) : ℕ) < 7 := a.2
    simp [this, pow_two]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have : ¬ ((Fin.natAdd 7 b : Fin (7 + 7)) : ℕ) < 7 := by simp
    simp [this, pow_two]

/-- **`tdet` does not vanish on `O(7,7)`.** -/
theorem tdet_ne_zero (g : O77) : tdet (g : Mat 14) ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  set v : Fin 14 → ℝ := Fin.append x (0 : Fin 7 → ℝ)
  have hvl : ∀ a : Fin 7, v (Fin.castAdd 7 a) = x a := fun a => Fin.append_left _ _ a
  have hvr : ∀ b : Fin 7, v (Fin.natAdd 7 b) = 0 := fun b => by
    show Fin.append x (0 : Fin 7 → ℝ) (Fin.natAdd 7 b) = 0
    rw [Fin.append_right]; rfl
  have hM := (mem_Orth_iff_Bm (g : Mat 14)).mp g.2 v v
  have hw : ∀ a : Fin 7, (Matrix.of (g : Mat 14) *ᵥ v) (Fin.castAdd 7 a) = 0 := by
    intro a
    have := congrFun hAx a
    simp only [mulVec, dotProduct, posBlock, Matrix.of_apply, Pi.zero_apply] at this ⊢
    rw [show (∑ j : Fin 14, _) = _ from Fin.sum_univ_add (a := 7) (b := 7) _]
    simp only [hvl, hvr, mul_zero, Finset.sum_const_zero, add_zero]
    exact this
  rw [Bm_self, Bm_self] at hM
  simp only [hw, hvl, hvr] at hM
  have hpos : 0 < ∑ a : Fin 7, x a ^ 2 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, by have : x k ≠ 0 := hk; positivity⟩
  have hneg : 0 ≤ ∑ b : Fin 7, (Matrix.of (g : Mat 14) *ᵥ v) (Fin.natAdd 7 b) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have z : ∑ _a : Fin 7, (0 : ℝ) ^ 2 = 0 := by simp
  rw [z] at hM
  linarith

lemma continuous_tdet : Continuous fun g : O77 => tdet (g : Mat 14) := by
  have hb : Continuous fun g : O77 => posBlock (g : Mat 14) :=
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply_apply (Fin.castAdd 7 a) (Fin.castAdd 7 b)).comp continuous_subtype_val
  exact hb.matrix_det

lemma tdet_one : tdet ((1 : O77) : Mat 14) = 1 := by
  have : posBlock ((1 : O77) : Mat 14) = 1 := by
    ext a b
    show (1 : Matrix (Fin 14) (Fin 14) ℝ) (Fin.castAdd 7 a) (Fin.castAdd 7 b) = _
    by_cases h : a = b
    · subst h; simp
    · have h' : (Fin.castAdd 7 a : Fin (7 + 7)) ≠ Fin.castAdd 7 b := fun e => h (Fin.castAdd_injective _ _ e)
      rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h]
  unfold tdet; rw [this, Matrix.det_one]

/-- **`tdet` is positive on `SO₀`.** -/
theorem tdet_pos_of_mem_SO0 {g : O77} (hg : g ∈ SO0) : 0 < tdet (g : Mat 14) := by
  have hcl : IsClopen {g : O77 | 0 < tdet (g : Mat 14)} := by
    refine ⟨?_, isOpen_lt continuous_const continuous_tdet⟩
    have : {g : O77 | 0 < tdet (g : Mat 14)} = {g : O77 | 0 ≤ tdet (g : Mat 14)} := by
      ext g
      exact ⟨fun h => le_of_lt (show 0 < tdet (g : Mat 14) from h),
        fun h => lt_of_le_of_ne (show 0 ≤ tdet (g : Mat 14) from h) (tdet_ne_zero g).symm⟩
    rw [this]
    exact isClosed_le continuous_const continuous_tdet
  have hone : (1 : O77) ∈ {g : O77 | 0 < tdet (g : Mat 14)} := by
    show 0 < tdet ((1 : O77) : Mat 14); rw [tdet_one]; norm_num
  exact hcl.connectedComponent_subset hone hg

/-- `SO₀` is stable under conjugation. -/
lemma conj_mem_SO0 {g : O77} (h : O77) (hg : h⁻¹ * g * h ∈ SO0) : g ∈ SO0 := by
  have hc : Continuous fun x : O77 => h * x * h⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsub := hc.image_connectedComponent_subset (1 : O77)
  simp only [mul_one, mul_inv_cancel] at hsub
  have this : h * (h⁻¹ * g * h) * h⁻¹ ∈ connectedComponent (1 : O77) := hsub ⟨_, hg, rfl⟩
  have e : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
  rw [e] at this
  exact this

/-- The signs of the holonomy. -/
def dHol : Fin 14 → ℝ := ![-1, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1]

lemma dHol_sq (i : Fin 14) : dHol i * dHol i = 1 := by
  fin_cases i <;> simp [dHol]

/-- The matrix of the holonomy. -/
def gHolM : Mat 14 := Matrix.of.symm (Matrix.diagonal dHol)

lemma gHolM_mem : gHolM ∈ O77 := by
  rw [mem_Orth_iff_mat]
  show (Matrix.diagonal dHol)ᵀ * Matrix.of η77 * Matrix.diagonal dHol = Matrix.of η77
  have : Matrix.of η77 = Matrix.diagonal fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1 := rfl
  rw [this, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  have := dHol_sq i
  calc dHol i * _ * dHol i = (dHol i * dHol i) * (if (i : ℕ) < 7 then (1 : ℝ) else -1) := by ring
    _ = _ := by rw [this, one_mul]

/-- **The holonomy element.** -/
def gHol : O77 := ⟨gHolM, gHolM_mem⟩

lemma tdet_gHol : tdet (gHol : Mat 14) = -1 := by
  have : posBlock (gHol : Mat 14) = Matrix.diagonal fun a : Fin 7 => dHol (Fin.castAdd 7 a) := by
    ext a b
    show (Matrix.diagonal dHol) (Fin.castAdd 7 a) (Fin.castAdd 7 b) = _
    by_cases h : a = b
    · subst h; simp
    · have h' : (Fin.castAdd 7 a : Fin (7 + 7)) ≠ Fin.castAdd 7 b := fun e => h (Fin.castAdd_injective _ _ e)
      rw [Matrix.diagonal_apply_ne _ h', Matrix.diagonal_apply_ne _ h]
  unfold tdet
  rw [this, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, dHol, Fin.castAdd]

/-- **The holonomy is not in the identity component.** -/
theorem gHol_not_mem_SO0 : gHol ∉ SO0 := fun h => by
  have := tdet_pos_of_mem_SO0 h
  rw [tdet_gHol] at this
  norm_num at this

end

end GU.Library
