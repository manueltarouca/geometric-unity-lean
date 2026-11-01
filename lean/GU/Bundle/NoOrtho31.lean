/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.OrthoGlue
import GU.Observerse.Signature95
import GU.Observerse.LorentzDichotomy

/-!
# No orthonormal frames over the (3,1) points of `Y`

**`no_ortho_31`**: if `Gpt y = P (−η) Pᵀ` (a (3,1) point), then no element of the frame bundle over
`y` is orthonormal. So the fibres of `orthoSet` over the (3,1) points are empty, and the O(7,7)
reduction can only live over the (1,3) part `Y13` (where fibres are nonempty, `ortho_exists_Y13`).
Proof: an orthonormal frame would give a linear `B` with `chimB (B x) (B x) = chimBm x x`, which
`no_isometry_95` rules out.

Conventions: `η = diag(1,−1,−1,−1)` and "(p,q)" counts (positive, negative) directions of the
contravariant `Gpt` (inversion-invariant). Convention dependence: this uses the relative sign `+DeWitt ⊕ +g⁻¹` fixed in `Chimeric.lean` (the
draft leaves (7,7) vs (9,5) open); with the opposite sign the roles of (1,3) and (3,1) swap. "(3,1)
points" means the points `Gpt = P(−η)Pᵀ`; these and `Y13` exhaust `Yobs` (`yobs_dichotomy`), and
**`ortho_iff_13`**: orthonormal frames exist over `y` iff `y` is a (1,3) point.
-/

namespace GU.Observerse

open Bundle Manifold Matrix GU.Chimeric GU.Iso77
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

lemma negηR_inv : (-ηR)⁻¹ = -ηR := by
  have h : (-ηR) * (-ηR) = 1 := by
    rw [neg_mul_neg]; ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, mul_apply, diagonal]
  exact inv_eq_left_inv h

lemma negηr_inv : (-ηr)⁻¹ = -ηr := by rw [← ηR_eq]; exact negηR_inv

lemma Bmod_negη_toCF (x y : E14) : Bmod (-ηR) (toCF x) (toCF y) = chimBm x y := by
  simp only [Bmod, chimY, toCF, covec_dotCLM, ηR_eq, negηr_inv, chimBm, LinearMap.mk₂_apply,
    neg_mul, mul_neg, neg_neg, trace_neg]

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **No orthonormal frames over (3,1) points.** -/
theorem no_ortho_31 (p : HomTot X) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (hy : Gpt p.proj = P * (-ηR) * Pᵀ) : p ∉ orthoSet (X := X) := by
  intro ho
  obtain ⟨u, hu⟩ := orthoSet_subset_frameSet ho
  let B : E14 →ₗ[ℝ] E14 := toCFL.symm.toLinearMap ∘ₗ ((↑u⁻¹ : EndC) : CFib →ₗ[ℝ] CFib) ∘ₗ
    (TP P hP).toLinearMap ∘ₗ toCFL.toLinearMap
  refine no_isometry_95 B fun x => ?_
  set w : CFib := TP P hP (toCFL x)
  have hA : (show EndC from p.2) ((↑u⁻¹ : EndC) w) = w := by
    rw [← hu]; show ((u : EndC) * ↑u⁻¹) w = w; rw [Units.mul_inv]; rfl
  have e1 : chimB (B x) (B x) = Bη ((↑u⁻¹ : EndC) w) ((↑u⁻¹ : EndC) w) := by
    rw [Bη_eq]; rfl
  rw [e1, ← ho, hA, hy, GU.Bmod_covariant, ← Bmod_negη_toCF]
  rfl

/-- **Every point of `Y` is a (1,3) point or a (3,1) point** (`lorentz_dichotomy`). -/
theorem yobs_dichotomy (y : Yobs X) :
    (∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ) ∨
      (∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * (-ηR) * Pᵀ) := by
  obtain ⟨P, hP, h | h⟩ := lorentz_dichotomy (Gpt y) (symMat_isSymm _) y.2
  · exact Or.inl ⟨P, hP, h⟩
  · exact Or.inr ⟨P, hP, h⟩

/-- **Orthonormal frames exist over `y` iff `y` is a (1,3) point.** So the O(7,7) reduction lives
exactly over `Y13` (under the `+DeWitt ⊕ +g⁻¹` convention). With `ortho_exists`, no point is both
(1,3) and (3,1): `not_13_and_31`. -/
theorem ortho_iff_13 (y : Yobs X) :
    (∃ p : HomTot X, p.proj = y ∧ p ∈ orthoSet (X := X)) ↔
      ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ := by
  constructor
  · rintro ⟨p, hp, ho⟩
    rcases yobs_dichotomy y with h | ⟨P, hP, h⟩
    · exact h
    · subst hp; exact absurd ho (no_ortho_31 p P hP h)
  · rintro ⟨P, hP, h⟩
    obtain ⟨p, hp, ho, -⟩ := ortho_exists y P hP h
    exact ⟨p, hp, ho⟩

/-- No point of `Y` is both a (1,3) and a (3,1) point. -/
theorem not_13_and_31 (y : Yobs X) :
    ¬ ((∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ) ∧
      (∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * (-ηR) * Pᵀ)) := by
  rintro ⟨⟨P, hP, h⟩, ⟨Q, hQ, h'⟩⟩
  obtain ⟨p, hp, ho, -⟩ := ortho_exists y P hP h
  subst hp
  exact no_ortho_31 p Q hQ h' ho

/-- Non-vacuity: over `X = ℝ⁴`, the point `(0, −η)` is a (3,1) point of `Y`. -/
example : ∃ y : Yobs (Fin 4 → ℝ), ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * (-ηR) * Pᵀ := by
  have hs : (-ηR).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, diagonal]
  have hd : (symMat (symCoords (-ηR))).det < 0 := by
    have e : -ηR = diagonal ![-1, 1, 1, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, diagonal]
    rw [symMat_symCoords _ hs, e, det_diagonal]; simp [Fin.prod_univ_four]
  refine ⟨⟨⟨0, symCoords (-ηR)⟩, hd⟩, 1, isUnit_one, ?_⟩
  simp only [Gpt, Matrix.one_mul, transpose_one, Matrix.mul_one]
  exact symMat_symCoords _ hs

end GU.Observerse
