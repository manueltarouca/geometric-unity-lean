import GU.Bundle.FramesCompare
import GU.Bundle.NoOrtho31

/-!
# Orthonormal frames in Mathlib's hom bundle, with the standard form `Q77`

A frame `q : ℝ¹⁴ →L C_y` of Mathlib's hom bundle is **orthonormal** if it is an isometry from
`(ℝ¹⁴, Q77)` (the standard (7,7) form) to `(C_y, chimeric metric)`:
`Bmod (Gpt y) (q x) (q x') = polar Q77 x x' / 2` (`orthoSetM`).

* `Bη_Φ`: `Bη (Φ x) (Φ x') = polar Q77 x x' / 2` (polarisation of `Φiso_isometry`).
* **`toM_ortho_iff`**: under `homDiffeo`, orthonormal frames correspond exactly (`orthoSet` ↔ `orthoSetM`).
* **`orthoM_iff_13`**: `Q77`-orthonormal frames of `C` exist over `y` iff `y` is a (1,3) point; the
  signature-selection statement in Mathlib's bundle language.
-/

namespace GU.Observerse

open Bundle Manifold Matrix GU.Chimeric GU.Iso77
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

lemma Bη_Φ (x x' : R14) : Bη (ΦL x) (ΦL x') = QuadraticMap.polar Q77 x x' / 2 := by
  have hb : ∀ u v : CFib, Bη u v = chimB (toCFL.symm u) (toCFL.symm v) := Bη_eq
  have hsq : ∀ z : R14, Bη (ΦL z) (ΦL z) = Q77 z := Φiso_isometry
  have hlin : ΦL (x + x') = ΦL x + ΦL x' := map_add _ _ _
  have key : Bη (ΦL (x + x')) (ΦL (x + x')) =
      Bη (ΦL x) (ΦL x) + 2 * Bη (ΦL x) (ΦL x') + Bη (ΦL x') (ΦL x') := by
    rw [hlin, hb, hb, hb, hb]
    simp only [map_add, LinearMap.add_apply]
    rw [chimB_symm (toCFL.symm (ΦL x')) (toCFL.symm (ΦL x))]
    ring
  rw [hsq, hsq, hsq] at key
  simp only [QuadraticMap.polar]
  linarith

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Orthonormal frames of Mathlib's hom bundle: isometries `(ℝ¹⁴, Q77) → (C_y, Bmod)`. -/
def orthoSetM : Set (HomTotM X) :=
  {q | ∀ x x' : R14, Bmod (Gpt q.proj) ((show HomF from q.2) x) ((show HomF from q.2) x') =
    QuadraticMap.polar Q77 x x' / 2}

/-- **Orthonormal frames correspond under `homDiffeo`.** -/
theorem toM_ortho_iff (p : HomTot X) : toM p ∈ orthoSetM (X := X) ↔ p ∈ orthoSet (X := X) := by
  constructor
  · intro h u w
    have := h (ΦL.symm u) (ΦL.symm w)
    rw [← Bη_Φ, ΦL.apply_symm_apply, ΦL.apply_symm_apply] at this
    change Bmod (Gpt p.proj) ((show EndC from p.2) (ΦL (ΦL.symm u)))
      ((show EndC from p.2) (ΦL (ΦL.symm w))) = Bη u w at this
    rwa [ΦL.apply_symm_apply, ΦL.apply_symm_apply] at this
  · intro h x x'
    rw [← Bη_Φ]
    exact h (ΦL x) (ΦL x')

/-- **Signature selection in Mathlib's bundle**: `Q77`-orthonormal frames of `C` exist over `y` iff
`y` is a (1,3) point. -/
theorem orthoM_iff_13 (y : Yobs X) :
    (∃ q : HomTotM X, q.proj = y ∧ q ∈ orthoSetM (X := X)) ↔
      ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ := by
  rw [← ortho_iff_13]
  constructor
  · rintro ⟨q, hq, ho⟩
    refine ⟨ofM q, hq, ?_⟩
    rw [← toM_ortho_iff, toM_ofM]; exact ho
  · rintro ⟨p, hp, ho⟩
    exact ⟨toM p, hp, (toM_ortho_iff p).mpr ho⟩

end GU.Observerse
