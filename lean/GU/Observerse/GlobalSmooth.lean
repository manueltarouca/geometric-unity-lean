import GU.Observerse.SymSquare

/-!
# The Einsteinian observerse `Y` as a global smooth 14-manifold over any smooth 4-manifold `X`

* `symCore (tangentBundleCore)` is `Sym²(TX)`: transition maps `A ↦ T A Tᵀ` built from the
  tangent transitions `T`. With the `IsContMDiff` mixin (`symAct` is polynomial, `symAct_contDiff`),
  it is a smooth vector bundle, so its total space is a smooth manifold modelled on `ℝ⁴ × ℝ¹⁰`.
* `Yobs X`: the open subset of Lorentzian tensors (`det < 0`, chart-invariant by `det_symAct`,
  open by `isOpen_lorSet`). **`Yobs_isManifold`**: `Y` is a smooth 14-manifold.
  `contMDiff_Yobs_proj`: the projection `Y → X` is smooth.

Points of `Y` are contravariant symmetric tensors `g^{ab}` (inverse metrics) of signature (1,3) or
(3,1). They correspond to metrics `g_ab` by inversion, a fibrewise diffeomorphism (not formalised).
This closes "smooth gluing of Y over X" from the open-items list. Mathlib's `IsManifold` carries
no Hausdorff / second-countability; these are inherited from `X` but not stated here. `X` lives in
`Type` (universe 0).
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The tangent bundle core of `X`. -/
noncomputable abbrev Zt (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :=
  tangentBundleCore (modelWithCornersSelf ℝ (Fin 4 → ℝ)) X

instance symCore_isContMDiff : (symCore (Zt X)).IsContMDiff (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ where
  contMDiffOn_coordChange i j := by
    have h1 : IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) (∞ + 1) X := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ by rfl]; infer_instance
    have : (Zt X).IsContMDiff (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ :=
      tangentBundleCore.isContMDiff (I := modelWithCornersSelf ℝ (Fin 4 → ℝ)) (M := X) (n := ∞)
    exact (symAct_contDiff.of_le le_top).contMDiff.comp_contMDiffOn
      ((Zt X).contMDiffOn_coordChange _ i j)

/-- `Sym²(TX)`, a smooth manifold modelled on `ℝ⁴ × ℝ¹⁰`. -/
abbrev Sym2TX (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :=
  TotalSpace (Fin 10 → ℝ) (symCore (Zt X)).Fiber

theorem sym2_isManifold :
    IsManifold ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞
      (Sym2TX X) := inferInstance

/-- **The observerse `Y`**: Lorentzian points of `Sym²(TX)`, an open subset. -/
def Yobs (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : TopologicalSpace.Opens (Sym2TX X) :=
  ⟨lorSet (Zt X), isOpen_lorSet (Zt X)⟩

/-- **`Y` is a smooth 14-manifold** (model `ℝ⁴ × ℝ¹⁰`) over any smooth 4-manifold `X`. -/
theorem Yobs_isManifold :
    IsManifold ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞
      (Yobs X) := inferInstance

theorem finrank_model : Module.finrank ℝ ((Fin 4 → ℝ) × (Fin 10 → ℝ)) = 14 := by simp

/-- The projection `π : Y → X` is smooth. -/
theorem contMDiff_Yobs_proj :
    ContMDiff ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
      (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ (fun y : Yobs X => (y : Sym2TX X).proj) :=
  (Bundle.contMDiff_proj _).comp contMDiff_subtype_val

end GU.Observerse
