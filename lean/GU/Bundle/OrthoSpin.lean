import GU.Bundle.OrthoLie
import GU.Spinor.SpinComponent

/-!
# Track 3, L4b: `O77` meets the spin results

* **`mem_O77_iff_IsoSet`**: the Lie group `O77` is the matrix set `IsoSet` of `SpinComponent.lean`.
* **`spinToO77 : Spin77 →* O77`**, `x ↦ matrix of vecRep x`, with
  **`orthToOG_comp_spinToO77`**: composed with `orthToOG` (the map behind `orthOGEquiv`) it is
  `spinToOG`; `spinToO77_neg_one`: `−1 ↦ 1`.
* **`cc_O77_iff_spin`**, **`connectedComponent_O77`**: the identity component of the Lie group
  `O77` is exactly the image of `Spin(7,7)`.
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor GU.Iso77

lemma Bm_polar (x y : Fin 14 → ℝ) :
    Bm x y = (Bm (x + y) (x + y) - Bm x x - Bm y y) / 2 := by
  have hc := Bm_comm y x
  unfold Bm at *
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hc]; ring

lemma mem_O77_iff_IsoSet (M : Mat 14) : M ∈ O77 ↔ Matrix.of M ∈ IsoSet := by
  rw [mem_Orth_iff_Bm]
  show _ ↔ ∀ v, Q77 (Matrix.toLin' (Matrix.of M) v) = Q77 v
  simp only [Matrix.toLin'_apply, Q77_eq_Bm]
  constructor
  · intro h v; exact h v v
  · intro h x y
    rw [Bm_polar, Bm_polar x y, ← mulVec_add, h, h, h]

/-- The matrix of `vecRep x`. -/
noncomputable def spinMat (x : Spin77) : Mat 14 :=
  Matrix.of.symm (LinearMap.toMatrix' (vecRep x : Module.End ℝ (Fin 14 → ℝ)))

lemma of_spinMat_mulVec (x : Spin77) (v : Fin 14 → ℝ) :
    Matrix.of (spinMat x) *ᵥ v = vecRep x v := by
  unfold spinMat
  rw [Equiv.apply_symm_apply, LinearMap.toMatrix'_mulVec]
  rfl

lemma spinMat_mem (x : Spin77) : spinMat x ∈ O77 := by
  rw [mem_O77_iff_IsoSet]
  intro v
  rw [Matrix.toLin'_apply, of_spinMat_mulVec]
  exact vecRep_isometry x v

lemma spinMat_one : spinMat 1 = Matrix.of.symm 1 := by
  apply Matrix.of.injective
  rw [Equiv.apply_symm_apply]
  ext i j
  have := congrFun (of_spinMat_mulVec 1 (Pi.single j 1)) i
  rw [map_one, mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

lemma of_mulM (A B : Mat 14) : Matrix.of (mulM A B) = Matrix.of A * Matrix.of B := rfl

lemma spinMat_mul (x y : Spin77) :
    spinMat (x * y) = mulM (spinMat x) (spinMat y) := by
  apply Matrix.of.injective
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, of_mulM, ← mulVec_mulVec, of_spinMat_mulVec,
    of_spinMat_mulVec, of_spinMat_mulVec, map_mul]
  rfl

/-- **`Spin(7,7) →* O(7,7)`**. -/
noncomputable def spinToO77 : Spin77 →* O77 where
  toFun x := ⟨spinMat x, spinMat_mem x⟩
  map_one' := Subtype.ext spinMat_one
  map_mul' x y := Subtype.ext (spinMat_mul x y)

/-- **Compatibility**: `Spin77 → O77 → OG` is `spinToOG`. -/
theorem orthToOG_comp_spinToO77 : orthToOG.comp spinToO77 = spinToOG := by
  refine MonoidHom.ext fun x => Subtype.ext (LinearEquiv.ext fun w => ?_)
  rw [MonoidHom.comp_apply, orthToOG_apply]
  show ΦL (Matrix.of (spinMat x) *ᵥ ΦL.symm w) = _
  rw [of_spinMat_mulVec]
  rfl

lemma spinToO77_neg_one : spinToO77 ⟨-1, neg_one_mem_spin⟩ = 1 :=
  orthToOG_injective (by rw [← MonoidHom.comp_apply, orthToOG_comp_spinToO77, map_one]
                         exact spinToOG_neg_one)

lemma O77_eq_IsoSet : (O77 : Set (Mat 14)) = IsoSet := Set.ext fun M => mem_O77_iff_IsoSet M

/-- **The identity component of `O(7,7)` is the image of `Spin(7,7)`**, as sets of matrices
(the topology on `Mat 14` is the `Matrix` topology). -/
theorem cc_O77_iff_spin (M : Mat 14) :
    M ∈ connectedComponentIn (O77 : Set (Mat 14)) (Matrix.of.symm 1) ↔
      ∃ x : Spin77, (spinToO77 x : Mat 14) = M := by
  show M ∈ connectedComponentIn (O77 : Set (Mat 14)) (Matrix.of.symm 1) ↔ ∃ x, spinMat x = M
  rw [O77_eq_IsoSet]
  show M ∈ connectedComponentIn IsoSet 1 ↔ _
  exact cc_iff_spin M

/-- **The same on the Lie group**: `connectedComponent 1 = range spinToO77`. -/
theorem connectedComponent_O77 : connectedComponent (1 : O77) = Set.range spinToO77 := by
  ext A
  have h := cc_O77_iff_spin (A : Mat 14)
  rw [connectedComponentIn_eq_image one_mem_Orth] at h
  constructor
  · intro hA
    obtain ⟨x, hx⟩ := h.mp ⟨A, hA, rfl⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨B, hB, e⟩ := h.mpr ⟨x, rfl⟩
    exact Subtype.ext e ▸ hB

end GU.Library
