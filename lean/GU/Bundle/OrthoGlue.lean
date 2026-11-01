/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SmoothOrtho
import GU.Bundle.Isometry77

/-!
# Orthonormal frames: invertibility and existence over the (1,3) part

* `chimB_nondeg`, `Bη_nondeg`: the model form `Bη` (≅ `Q77`) is (left-, hence by symmetry)
  nondegenerate (diagonal Gram
  matrix on `chimVec_basis` with nonzero norms).
* **`orthoSet_subset_frameSet`**: every orthonormal map `ℝ¹⁴ → C_y` is invertible, so the closed set
  `orthoSet` lies inside the frame bundle `FrY`. `ortho_transitive'`: fibre-transitivity of `O(Bη)`
  on orthonormal frames with no extra hypotheses.
* **`ortho_exists`**: over every (1,3) point `y` (`Gpt y = P η Pᵀ`) there is an orthonormal frame,
  namely the transport `TP P` (`TP_isometry`), as an element of the smooth total space.
-/

namespace GU.Observerse

open Bundle Manifold Matrix GU.Chimeric GU.Iso77
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

theorem chimB_nondeg (x : E14) (h : ∀ y, chimB x y = 0) : x = 0 := by
  rw [← chimVec_basis.sum_repr x]
  have hc : ∀ j, chimVec_basis.repr x j = 0 := by
    intro j
    have hj := h (chimVec j)
    rw [← chimVec_basis.sum_repr x] at hj
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hj
    have hb : ∀ i, chimVec_basis i = chimVec i := fun i => by
      simp [chimVec_basis]
    simp only [hb, chimB_basis, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hj
    exact (mul_eq_zero.mp hj).resolve_right (chimNorms_ne j)
  simp [hc]

theorem Bη_nondeg (u : CFib) (h : ∀ w, Bη u w = 0) : u = 0 := by
  have : toCFL.symm u = 0 := chimB_nondeg _ fun y => by
    rw [← h (toCFL y), Bη_eq, toCFL.symm_apply_apply]
  simpa using congrArg toCFL this

lemma Bmod_zero_left (G : Matrix (Fin 4) (Fin 4) ℝ) (v : CFib) : Bmod G 0 v = 0 := by
  have h1 : symMat (0 : Fin 10 → ℝ) = 0 := by ext i j; simp [symMat]
  have h2 : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext i; simp [covec]
  simp [Bmod, chimY, h1, h2]

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **Orthonormal maps are frames.** -/
theorem orthoSet_subset_frameSet : orthoSet (X := X) ⊆ frameSet (X := X) := by
  intro p hp
  set A : EndC := show EndC from p.2
  have hinj : Function.Injective (A : CFib →ₗ[ℝ] CFib) := by
    intro a b hab
    refine sub_eq_zero.mp (Bη_nondeg _ fun w => ?_)
    have h0 : A (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hab
    rw [← hp (a - b) w]
    show Bmod _ (A (a - b)) _ = 0
    rw [h0, Bmod_zero_left]
  let e := (LinearEquiv.ofInjectiveEndo (A : CFib →ₗ[ℝ] CFib) hinj).toContinuousLinearEquiv
  exact ⟨e.toUnit, ContinuousLinearMap.ext fun v => rfl⟩

/-- **Orthonormal frames exist over every (1,3) point** (in the smooth total space). -/
theorem ortho_exists (y : Yobs X) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (hy : Gpt y = P * ηR * Pᵀ) :
    ∃ p : HomTot X, p.proj = y ∧ p ∈ orthoSet (X := X) ∧ p ∈ frameSet (X := X) := by
  let A : EndC := LinearMap.toContinuousLinearMap (TP P hP : CFib →ₗ[ℝ] CFib)
  refine ⟨⟨y, A⟩, rfl, ?_, orthoSet_subset_frameSet ?_⟩ <;>
  · intro u w
    show Bmod (Gpt y) (TP P hP u) (TP P hP w) = Bη u w
    rw [hy, TP_isometry]

/-- Hence over the (1,3) part the frame bundle has orthonormal frames in every fibre. -/
theorem ortho_exists_Y13 (y : Y13 X) :
    ∃ p : HomTot X, p.proj = y.1 ∧ p ∈ orthoSet (X := X) ∧ p ∈ frameSet (X := X) := by
  obtain ⟨P, hP, hy⟩ := y.2
  exact ortho_exists y.1 P hP hy

/-- `ortho_transitive` without the (now redundant) frame hypotheses. -/
theorem ortho_transitive' {p q : HomTot X} (hpo : p ∈ orthoSet (X := X)) (hqo : q ∈ orthoSet (X := X))
    (h : p.proj = q.proj) :
    ∃ g : EndCˣ, ract p g = q ∧ ∀ u v, Bη ((g : EndC) u) ((g : EndC) v) = Bη u v :=
  ortho_transitive (orthoSet_subset_frameSet hpo) (orthoSet_subset_frameSet hqo) hpo hqo h

end GU.Observerse
