/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Observerse.GlobalSmooth

/-!
# The chimeric bundle `C = V ⊕ H*` as a smooth rank-14 vector bundle over `Y` ((3.10))

With `π : Y → X` smooth (`piYsm`):
* `Vb = π* Sym²(TX)`: the vertical bundle (`V_y ≅ T_y(fiber) ≅ Sym²`), rank 10;
* `Hb = π* T*X`: the horizontal cotangent bundle `H* = π*(T*X)` of (3.7), rank 4;
* `Cb = Vb ×ᵇ Hb`: the chimeric bundle, a smooth vector bundle of rank 14 over the smooth
  14-manifold `Y` (`chimeric_smooth`), built entirely from Mathlib's pullback/product machinery.

Identifying `Vb` with the vertical tangent bundle of `Y` (canonical for the total space of a
vector bundle) and putting the chimeric metric on `Cb` fibrewise are not done here; the pointwise
metric and its (7,7) signature are in `Chimeric*.lean`.
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- `π : Y → X` as a smooth map. -/
noncomputable def piYsm : ContMDiffMap
    ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
    (modelWithCornersSelf ℝ (Fin 4 → ℝ)) (Yobs X) X ∞ :=
  ⟨fun y => (y : Sym2TX X).proj, contMDiff_Yobs_proj⟩

/-- Vertical part `V = π* Sym²(TX)`. -/
abbrev Vb := (piYsm (X := X) : Yobs X → X) *ᵖ (symCore (Zt X)).Fiber

/-- Horizontal cotangent part `H* = π* T*X`. -/
abbrev Hb := (piYsm (X := X) : Yobs X → X) *ᵖ
  (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ)

/-- **The chimeric bundle** `C = V ⊕ H*`. -/
abbrev Cb := Vb (X := X) ×ᵇ Hb (X := X)

/-- Fiber model of `C`: `ℝ¹⁰ × (ℝ⁴)* ≅ ℝ¹⁴`. -/
abbrev CFib := (Fin 10 → ℝ) × ((Fin 4 → ℝ) →L[ℝ] ℝ)

theorem chimeric_vectorBundle : VectorBundle ℝ CFib (Cb (X := X)) := inferInstance

theorem chimeric_smooth :
    ContMDiffVectorBundle ∞ CFib (Cb (X := X))
      ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) :=
  inferInstance

end GU.Observerse
