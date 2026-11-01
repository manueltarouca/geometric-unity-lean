/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinConnected
import GU.Library.LocalHomeoCharts

/-!
# Phase 4, item 5: `Spin(7,7)` is a Lie group

`ρ = spinToO77 : Spin(7,7) → O(7,7)` is a local homeomorphism (`isLocalHomeomorph_ρ`: the covering
`spinToSO0` onto the open `SO₀`). `Spin77` gets the manifold structure pulled back along `ρ`
(`LocalHomeoCharts.lean`): a map into `Spin77` is smooth iff it is continuous and its image in `O77`
is smooth. Hence **`lieGroup_spin`**, and `ρ` is a local diffeomorphism (`isLocalDiffeomorph_ρ`) with
image `SO₀` (`range_ρ`). This is the local-diffeomorphism statement for `spinToSO0` read in the ambient
`O77`, in which `SO₀` is open; `SO₀` is not given its own manifold structure here.
-/

namespace GU.Library

open GU GU.Spinor TopologicalSpace
open scoped ContDiff Manifold Topology

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The model of `O(7,7)` and of `Spin(7,7)`. -/
abbrev E77 := Fin (fibreDim (Mat 14) (symS 14)) → ℝ

lemma isOpen_SO0 : IsOpen ((SO0 : Subgroup O77) : Set O77) :=
  isOpen_connectedComponent

/-- **`ρ` is a local homeomorphism.** -/
theorem isLocalHomeomorph_ρ : IsLocalHomeomorph (spinToO77 : Spin77 → O77) := by
  have h1 := isCoveringMap_spinToSO0.isLocalHomeomorph
  have h2 : IsLocalHomeomorph (Subtype.val : SO0 → O77) :=
    isOpen_SO0.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact h2.comp h1

instance : ChartedSpace E77 Spin77 := pullCharted E77 isLocalHomeomorph_ρ

/-- **`Spin77` is a smooth manifold.** -/
instance isManifold_spin : IsManifold 𝓘(ℝ, E77) ∞ Spin77 := isManifold_pull isLocalHomeomorph_ρ

/-- **`ρ` is smooth.** -/
theorem contMDiff_ρ : ContMDiff 𝓘(ℝ, E77) 𝓘(ℝ, E77) ∞ (spinToO77 : Spin77 → O77) :=
  contMDiff_pull isLocalHomeomorph_ρ

/-- **`ρ` is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_ρ : IsLocalDiffeomorph 𝓘(ℝ, E77) 𝓘(ℝ, E77) ∞ (spinToO77 : Spin77 → O77) :=
  isLocalDiffeomorph_pull isLocalHomeomorph_ρ

section Universal

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace M] [ChartedSpace HM M] {I : ModelWithCorners ℝ EM HM}

theorem contMDiff_into_spin_iff {f : M → Spin77} :
    ContMDiff I 𝓘(ℝ, E77) ∞ f ↔
      Continuous f ∧ ContMDiff I 𝓘(ℝ, E77) ∞ (fun y => spinToO77 (f y)) :=
  contMDiff_into_pull_iff isLocalHomeomorph_ρ

theorem contMDiffOn_into_spin_iff {f : M → Spin77} {t : Set M} (ht : IsOpen t) :
    ContMDiffOn I 𝓘(ℝ, E77) ∞ f t ↔
      ContinuousOn f t ∧ ContMDiffOn I 𝓘(ℝ, E77) ∞ (fun y => spinToO77 (f y)) t :=
  contMDiffOn_into_pull_iff isLocalHomeomorph_ρ ht

end Universal

/-- **`Spin(7,7)` is a Lie group.** -/
instance lieGroup_spin : LieGroup 𝓘(ℝ, E77) ∞ Spin77 := by
  refine { toIsManifold := isManifold_spin, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · rw [contMDiff_into_spin_iff]
    refine ⟨continuous_mul, ?_⟩
    have h1 := contMDiff_ρ.comp (contMDiff_fst (I := 𝓘(ℝ, E77)) (J := 𝓘(ℝ, E77))
      (M := Spin77) (N := Spin77))
    have h2 := contMDiff_ρ.comp (contMDiff_snd (I := 𝓘(ℝ, E77)) (J := 𝓘(ℝ, E77))
      (M := Spin77) (N := Spin77))
    have h3 := h1.mul h2
    refine h3.congr fun p => ?_
    exact (map_mul spinToO77 p.1 p.2).symm ▸ rfl
  · rw [contMDiff_into_spin_iff]
    refine ⟨continuous_inv, ?_⟩
    refine (contMDiff_ρ.inv).congr fun s => ?_
    exact (map_inv spinToO77 s).symm ▸ rfl

/-- The image of `ρ` is exactly `SO₀`. -/
theorem range_ρ : Set.range (spinToO77 : Spin77 → O77) = ((SO0 : Subgroup O77) : Set O77) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩; exact spinToO77_mem s
  · intro hg
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
    exact ⟨t, congrArg Subtype.val ht⟩

end

end GU.Library
