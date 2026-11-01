import GU.Bundle.TimeCover

/-!
# Phase 6, item 2: `Y13` and its time-orientation cover are Hausdorff when `X` is

* **`t2_totalSpace`**: a fibre bundle with Hausdorff base and fibre has a Hausdorff total space (points
  over different base points are separated by the projection, points over one base point by a local
  trivialisation).
* **`t2_Y13`**: hence `Y13o X` (an open subset of `Yobs X`, itself open in `Sym²(TX)`) is Hausdorff for
  Hausdorff `X`, and **`t2_Ytilde`**: so is its time-orientation cover `Ytilde X` (`t2_tilde`).
  `t2_Ytilde_R4` is the instance for `X = ℝ⁴`.
-/

namespace GU.Library

open Bundle GU GU.Observerse TopologicalSpace Topology
open scoped ContDiff Manifold

noncomputable section

/-- **A fibre bundle with Hausdorff base and fibre has a Hausdorff total space.** -/
theorem t2_totalSpace {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [T2Space B] [T2Space F] : T2Space (TotalSpace F E) := by
  refine ⟨fun p q hpq => ?_⟩
  by_cases h : p.proj = q.proj
  · set e := trivializationAt F E p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hq : q ∈ e.source := by
      rw [e.mem_source, ← h]; exact FiberBundle.mem_baseSet_trivializationAt' p.proj
    have hne : e p ≠ e q := fun he => hpq (e.injOn hp hq he)
    obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation hne
    refine ⟨e.source ∩ e ⁻¹' U, e.source ∩ e ⁻¹' V,
      e.continuousOn.isOpen_inter_preimage e.open_source hU,
      e.continuousOn.isOpen_inter_preimage e.open_source hV, ⟨hp, hpU⟩, ⟨hq, hqV⟩, ?_⟩
    exact Set.disjoint_left.mpr fun r hr hr' => Set.disjoint_left.mp hUV hr.2 hr'.2
  · obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation h
    exact ⟨TotalSpace.proj ⁻¹' U, TotalSpace.proj ⁻¹' V, hU.preimage (FiberBundle.continuous_proj F E),
      hV.preimage (FiberBundle.continuous_proj F E), hpU, hqV, hUV.preimage _⟩

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- `Sym²(TX)` (and hence `Yobs X`) is Hausdorff when `X` is. -/
instance t2_Sym2TX [T2Space X] : T2Space (Sym2TX X) := t2_totalSpace

/-- **`Y13` is Hausdorff when `X` is.** -/
instance t2_Y13 [T2Space X] : T2Space (Y13o X) := inferInstance

/-- **The time-orientation cover is Hausdorff when `X` is.** -/
instance t2_Ytilde [T2Space X] : T2Space (Ytilde X) := inferInstance

/-- The instance over `ℝ⁴`. -/
theorem t2_Ytilde_R4 : T2Space (Ytilde (Fin 4 → ℝ)) := inferInstance

end

end GU.Library
