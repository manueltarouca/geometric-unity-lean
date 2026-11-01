/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Observerse.ChimericFiber
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Every Lorentzian `4×4` symmetric matrix is congruent to `η` or `−η`

**`lorentz_dichotomy`**: if `G` is symmetric with `det G < 0` then `G = P η Pᵀ` or `G = P (−η) Pᵀ` for an
invertible `P`. Proof: spectral theorem (`Matrix.IsHermitian.spectral_theorem`), rescaling eigenvalues
to `±1` by `√|λ|`; `det < 0` forces an odd number of `−1`s; the 8 resulting sign patterns are
permutations of `η` or `−η` (`sign_patterns`, by `decide`).
-/

namespace GU.Chimeric
open Matrix

def sgnZ (p : Fin 4 → Bool) : Fin 4 → ℤ := fun i => if p i then 1 else -1

def swapM (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j => if j = Equiv.swap 0 k i then 1 else 0

theorem sign_patterns : ∀ p : Fin 4 → Bool, (∏ i, sgnZ p i) = -1 →
    ∃ k : Fin 4, diagonal (sgnZ p) = swapM k * ηZ * (swapM k)ᵀ ∨
      diagonal (sgnZ p) = swapM k * (-ηZ) * (swapM k)ᵀ := by
  decide

lemma swapM_cast (k : Fin 4) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    ((swapM k * A * (swapM k)ᵀ).map (Int.castRingHom ℝ)) =
      (swapM k).map (Int.castRingHom ℝ) * A.map (Int.castRingHom ℝ) * ((swapM k).map (Int.castRingHom ℝ))ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

lemma swapM_isUnit (k : Fin 4) : IsUnit ((swapM k).map (Int.castRingHom ℝ)) := by
  have h : swapM k * swapM k = 1 := by revert k; decide
  have h' : (swapM k).map (Int.castRingHom ℝ) * (swapM k).map (Int.castRingHom ℝ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h')

/-- **Every Lorentzian symmetric matrix is congruent to `η` or `−η`.** -/
theorem lorentz_dichotomy (G : Matrix (Fin 4) (Fin 4) ℝ) (hs : G.IsSymm) (hd : G.det < 0) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ (G = P * ηR * Pᵀ ∨ G = P * (-ηR) * Pᵀ) := by
  have hH : G.IsHermitian := by
    unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hs.eq
  set U : Matrix (Fin 4) (Fin 4) ℝ := (hH.eigenvectorUnitary : Matrix (Fin 4) (Fin 4) ℝ)
  set ev := hH.eigenvalues
  have hspec : G = U * diagonal ev * Uᵀ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have hdet : ∏ i, ev i < 0 := by
    have := hH.det_eq_prod_eigenvalues; simp only [RCLike.ofReal_real_eq_id, id] at this
    rw [← this]; exact hd
  have hne : ∀ i, ev i ≠ 0 := fun i h => by
    have : ∏ i, ev i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h
    linarith
  set p : Fin 4 → Bool := fun i => decide (0 < ev i)
  set r : Fin 4 → ℝ := fun i => Real.sqrt |ev i|
  have hev : diagonal ev = diagonal r * (diagonal (sgnZ p)).map (Int.castRingHom ℝ) * diagonal r := by
    rw [diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    simp only [r, p, sgnZ]
    have hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    by_cases h : 0 < ev i
    · simp [h, abs_of_pos h]; rw [Real.mul_self_sqrt h.le]
    · have hn : ev i < 0 := lt_of_le_of_ne (not_lt.mp h) (hne i)
      simp [h, abs_of_neg hn]; rw [Real.mul_self_sqrt (by linarith)]; ring
  have hsgn : ∏ i, sgnZ p i = -1 := by
    have h1 : ∀ i, ev i = (sgnZ p i : ℝ) * |ev i| := fun i => by
      simp only [sgnZ, p]
      by_cases h : 0 < ev i
      · simp [h, abs_of_pos h]
      · have hn : ev i < 0 := lt_of_le_of_ne (not_lt.mp h) (hne i)
        simp [h, abs_of_neg hn]
    have h2 : ∏ i, ev i = (∏ i, (sgnZ p i : ℝ)) * ∏ i, |ev i| := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => h1 i
    have hpos : 0 < ∏ i, |ev i| := Finset.prod_pos fun i _ => abs_pos.mpr (hne i)
    have hneg : (∏ i, (sgnZ p i : ℝ)) < 0 := by
      rw [h2] at hdet; exact neg_of_mul_neg_left hdet hpos.le
    have hpm : ∀ q : Fin 4 → Bool, ∏ i, sgnZ q i = 1 ∨ ∏ i, sgnZ q i = -1 := by decide
    rcases hpm p with h | h
    · exfalso; have : (∏ i, (sgnZ p i : ℝ)) = 1 := by exact_mod_cast h
      linarith
    · exact h
  obtain ⟨k, hk⟩ := sign_patterns p hsgn
  have hrU : IsUnit (U * diagonal r) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [det_mul, det_diagonal]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Real.sqrt_pos.mpr (abs_pos.mpr (hne i))).ne'))
    have hu := hH.eigenvectorUnitary.2
    exact Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hu)
  set S := (swapM k).map (Int.castRingHom ℝ)
  refine ⟨U * diagonal r * S, hrU.mul (swapM_isUnit k), ?_⟩
  have hG : G = (U * diagonal r) * (diagonal (sgnZ p)).map (Int.castRingHom ℝ) * (U * diagonal r)ᵀ := by
    rw [hspec, hev, transpose_mul, diagonal_transpose]; simp only [Matrix.mul_assoc]
  rcases hk with h | h
  · left
    rw [hG, h, swapM_cast]
    have : ηZ.map (Int.castRingHom ℝ) = ηR := rfl
    rw [this]; simp only [S, transpose_mul, Matrix.mul_assoc]
  · right
    rw [hG, h, swapM_cast]
    have : (-ηZ).map (Int.castRingHom ℝ) = -ηR := by rw [Matrix.map_neg _ (fun a => map_neg _ a)]; rfl
    rw [this]; simp only [S, transpose_mul, Matrix.mul_assoc]

end GU.Chimeric
