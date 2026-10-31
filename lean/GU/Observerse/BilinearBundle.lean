import Mathlib

/-!
# Stepping stone to the global smooth observerse: the bundle of bilinear forms on `TX`

For any smooth manifold `X` modelled on `ℝ⁴`, `Bil x = T_xX →L T_xX →L ℝ` is a smooth vector
bundle (Mathlib's hom-bundle machinery), so its total space is a smooth manifold of dimension
`4 + 16 = 20` (`bil_isManifold`), with smooth projection to `X` (`contMDiff_bil_proj`).

The observerse `Y = Met_Lor(X)` is the subset of *symmetric* forms of negative determinant
(10-dimensional fibers, 14-dimensional total space). It is not open here (symmetry is a closed
condition). Building it as a smooth 14-manifold needs a symmetric sub-bundle, which Mathlib does
not provide yet. Pointwise, the Lorentzian condition is basis-independent (`det_congr_sign`).
-/

namespace GU.Observerse

open Bundle Manifold

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ⊤ X]

/-- Fiber model: bilinear forms on `ℝ⁴` (dimension 16). -/
abbrev F16 := (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ

/-- Bilinear forms on the tangent space. -/
abbrev Bil (x : X) := TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ]
  TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ

noncomputable instance bil_smoothBundle : ContMDiffVectorBundle ⊤ F16 (Bil (X := X))
    (modelWithCornersSelf ℝ (Fin 4 → ℝ)) := inferInstance

theorem bil_isManifold :
    IsManifold ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ F16)) ⊤
      (TotalSpace F16 (Bil (X := X))) := inferInstance

theorem contMDiff_bil_proj :
    ContMDiff ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ F16))
      (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ⊤ (TotalSpace.proj : TotalSpace F16 (Bil (X := X)) → X) :=
  Bundle.contMDiff_proj _

end GU.Observerse
