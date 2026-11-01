import GU.Bundle.TimeObstruction

/-!
# Phase 4, item 4: spin structures over small open sets exist

The spin-lift theorems are not vacuous: every point of `Y13` has an open neighbourhood `W` carrying
a spin structure (`exists_spinLiftData_near`, `exists_spinStructure_near`), from the local sections
of the frame bundle (`frame_locTriv`) with trivial lifts (`SpinLiftData.ofSection`). Together with
`no_spinStructure_univ`, this says a spin structure (for the connected group `Spin77`, i.e. `Spin⁺(7,7)`)
exists locally on `Y13` but not on all of it when `X` is nonempty. These instances use one chart and
trivial lifts, so the cocycle and coboundary content is not exercised by them.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **Every point of `Y13` has a neighbourhood with cocycle lifts.** -/
theorem exists_spinLiftData_near (b : Y13o X) : ∃ D : SpinLiftData X, b ∈ D.W := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨V, hV, hb, σ, -, hσ, hp, -, -⟩ := frame_locTriv (X := X) b
  exact ⟨SpinLiftData.ofSection V hV σ hσ.continuousOn hp, hb⟩

/-- **Every point of `Y13` has a neighbourhood with a spin structure.** -/
theorem exists_spinStructure_near (b : Y13o X) : ∃ S : SpinStructure X, b ∈ S.W := by
  obtain ⟨D, hD⟩ := exists_spinLiftData_near (X := X) b
  exact ⟨D.toStructure, hD⟩

end

end GU.Library
