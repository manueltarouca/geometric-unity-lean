import GU.Bundle.OrthoSpin

/-!
# `Spin(7,7)` as a topological group, and continuity of `Spin(7,7) → O(7,7)`

Mathlib gives `CliffordAlgebra` no topology. Pull one back along the faithful representation
`cliffordRep : Cl(7,7) ≃ ℝ(128)` (`cliffordRep_bijective`), which makes `cliffordRep` a
homeomorphism onto `ℝ(128)` (`clTop`, `cl77Homeomorph`), the canonical module topology. With the subspace topology:
* **`IsTopologicalGroup Spin77`**: `ρ(xy) = ρ(x)ρ(y)` and `ρ(x⁻¹) = ρ(x*) = C ρ(x)ᵀ C`;
* **`continuous_spinToO77`**: the matrix of `vecRep x` has entries
  `tr(ρ(x) γ_j C ρ(x)ᵀ C γ_i) / (128 w_i)` (`spinMat_apply_trace`), which are polynomial in `ρ(x)`.
This is the first topological input towards the spin double cover; the covering-map property and
connectedness of `Spin77` remain open.
-/

namespace GU.Spinor

open Matrix CliffordAlgebra GU.Library
open scoped Manifold ContDiff

/-- The topology on `Cl(7,7)` transported from `ℝ(128)`. It is the canonical module topology
(`IsModuleTopology ℝ Cl77` below); a future norm on `Cl77` should use `replaceTopology clTop`. -/
noncomputable instance clTop : TopologicalSpace Cl77 := TopologicalSpace.induced cliffordRep inferInstance

lemma isInducing_rep : Topology.IsInducing (cliffordRep : Cl77 → M128) := ⟨rfl⟩

lemma isInducing_spin : Topology.IsInducing (fun x : Spin77 => cliffordRep (x : Cl77)) :=
  isInducing_rep.comp Topology.IsInducing.subtypeVal

lemma continuous_rep_spin : Continuous (fun x : Spin77 => cliffordRep (x : Cl77)) :=
  isInducing_spin.continuous

/-- `cliffordRep` as a homeomorphism `Cl(7,7) ≃ₜ ℝ(128)`. -/
noncomputable def cl77Homeomorph : Cl77 ≃ₜ M128 :=
  cl77Equiv.toEquiv.toHomeomorphOfIsInducing isInducing_rep

instance : IsModuleTopology ℝ M128 := IsModuleTopology.instPi

/-- `ℝ(128) ≃L Cl(7,7)`. -/
noncomputable def cl77CLE : M128 ≃L[ℝ] Cl77 :=
  { cl77Equiv.symm.toLinearEquiv with
    continuous_toFun := cl77Homeomorph.symm.continuous
    continuous_invFun := cl77Homeomorph.continuous }

/-- **`clTop` is the canonical topology** of the finite-dimensional space `Cl(7,7)`. -/
instance : IsModuleTopology ℝ Cl77 := .iso cl77CLE

instance : IsTopologicalRing Cl77 := IsModuleTopology.isTopologicalRing ℝ Cl77
instance : T2Space Cl77 := cl77Homeomorph.symm.t2Space

/-- `ρ(x⁻¹) = C ρ(x)ᵀ C` on `Spin(7,7)`. -/
lemma cliffordRep_inv (x : Spin77) : cliffordRep ((x⁻¹ : Spin77) : Cl77) = C * (cliffordRep (x : Cl77))ᵀ * C :=
  cliffordRep_star (x : Cl77)

/-- **`Spin(7,7)` is a topological group.** -/
instance spinTopGroup : IsTopologicalGroup Spin77 where
  continuous_mul := by
    rw [isInducing_spin.continuous_iff]
    have : (fun p : Spin77 × Spin77 => cliffordRep ((p.1 * p.2 : Spin77) : Cl77)) =
        fun p => cliffordRep (p.1 : Cl77) * cliffordRep (p.2 : Cl77) := by
      funext p; exact map_mul _ _ _
    rw [Function.comp_def, this]
    exact (continuous_rep_spin.comp continuous_fst).mul (continuous_rep_spin.comp continuous_snd)
  continuous_inv := by
    rw [isInducing_spin.continuous_iff, Function.comp_def]
    simp_rw [cliffordRep_inv]
    exact (continuous_const.mul continuous_rep_spin.matrix_transpose).mul continuous_const

/-- Coordinates of a vector from its Clifford image. -/
lemma coord_trace (v : Fin 14 → ℝ) (i : Fin 14) :
    v i = trace (gammaMap v * gamma (gen i)) / (128 * w i) := by
  have hw : w i ≠ 0 := by unfold w; split_ifs <;> norm_num
  simp only [gammaMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, trace_sum, smul_mul_assoc,
    trace_smul, trace_gamma_gamma, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji]) (by simp)]
  simp only [ite_true]
  field_simp

/-- Entries of the vector representation as traces in `ℝ(128)`. -/
lemma spinMat_apply_trace (x : Spin77) (i j : Fin 14) :
    spinMat x i j = trace (cliffordRep (x : Cl77) * gammaMap (Pi.single j 1) *
      (C * (cliffordRep (x : Cl77))ᵀ * C) * gamma (gen i)) / (128 * w i) := by
  have h1 : spinMat x i j = vecRep x (Pi.single j 1) i := by
    have := congrFun (of_spinMat_mulVec x (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    exact this
  rw [h1, coord_trace (vecRep x (Pi.single j 1)) i]
  congr 2
  rw [← cliffordRep_ι, show (vecRep x (Pi.single j 1)) = vecL x (Pi.single j 1) from rfl, ι_vecL,
    map_mul, map_mul, cliffordRep_ι, cliffordRep_star]

/-- **`Spin(7,7) → O(7,7)` is continuous.** -/
theorem continuous_spinToO77 : Continuous (spinToO77 : Spin77 → O77) := by
  apply Continuous.subtype_mk
  show Continuous fun x : Spin77 => spinMat x
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp_rw [spinMat_apply_trace]
  refine Continuous.div_const ?_ _
  refine Continuous.matrix_trace ?_
  exact ((continuous_rep_spin.mul continuous_const).mul
    ((continuous_const.mul continuous_rep_spin.matrix_transpose).mul continuous_const)).mul
      continuous_const

/-- `O77` as a topological group (from its Lie group structure). -/
instance : IsTopologicalGroup O77 :=
  topologicalGroup_of_lieGroup 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞

end GU.Spinor
