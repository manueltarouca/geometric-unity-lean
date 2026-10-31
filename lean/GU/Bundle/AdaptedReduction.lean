import GU.Bundle.AdaptedSection

/-!
# Phase 3, item 3: the adapted frames are a reduction of `OFr` to the block group

**`adaptedReduction`**: a `SmoothReduction` (reduction of the structure group in the
local-section sense) of `frameBundle` (the smooth principal `O(7,7)`-bundle `OFr → Y13`) to
`Gblk` (`O(6,4) × O(1,3)` by `SH_signature`) with carrier the adapted frames `AFr`: `Gblk`-stable
(`ractM_mem_AFr_blk`), fibrewise `Gblk`-transitive (`adapted_fibre_transitive`), with smooth local
adapted sections (`adapted_locSec`, from `exists_local_section_adapted`). So
`SmoothReduction.locTriv` gives smooth local trivialisations whose division maps are
`Gblk`-valued on `AFr`. The aligned Pati–Salam groups act on the carrier
(`adaptedReduction_PS6'`, `_PS4'`, via `PS6'_le_Gblk`, `PS4'_le_Gblk`).
**Not shown**: that `AFr` is an embedded submanifold, or `Gblk` an embedded Lie subgroup (only
closed, `isClosed_Gblk`), so there is no `SmoothPrincipalBundle … Gblk AFr` object yet.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **Smooth local adapted sections over `Y13`.** -/
theorem adapted_locSec (b : Y13o X) :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ∃ V : Set (Y13o X), IsOpen V ∧ b ∈ V ∧ ∃ σ : Y13o X → OFr X,
      ContMDiffOn ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
        𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ σ V ∧
      ∀ y ∈ V, projOFr (σ y) = y ∧ (σ y : HomTotM X) ∈ AFr X := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨q0, hq0p, hq0⟩ := exists_adapted_frame (b : Yobs X) b.2
  obtain ⟨U, hU, σ, hσ, hσp⟩ := exists_local_section_adapted q0 hq0
  set cY := chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj
  have he0 : (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 q0).1) = cY q0.proj :=
    chart_fst q0 q0 (mem_chart_source _ q0)
  rw [he0] at hU
  let Vy : Set (Yobs X) := cY.source ∩ cY ⁻¹' interior U
  have hVy : IsOpen Vy := cY.isOpen_inter_preimage isOpen_interior
  let V : Set (Y13o X) := Subtype.val ⁻¹' Vy
  have hmem : ∀ y : Y13o X, y ∈ V → σ (cY y) ∈ AFr X := fun y hy =>
    (hσp _ (interior_subset hy.2)).1
  classical
  let σY : Y13o X → OFr X := fun y =>
    if hy : y ∈ V then ⟨σ (cY y), (hmem y hy).1⟩ else ⟨q0, hq0.1⟩
  have hσY : ∀ y ∈ V, (σY y : HomTotM X) = σ (cY y) := fun y hy => by
    simp [σY, hy]
  refine ⟨V, hVy.preimage continuous_subtype_val, ?_, σY, ?_, fun y hy => ⟨?_, ?_⟩⟩
  · show (b : Yobs X) ∈ Vy
    rw [← hq0p]
    exact ⟨mem_chart_source _ _, mem_interior_iff_mem_nhds.mpr hU⟩
  · rw [contMDiffOn_regularLevel_iff]
    have hcY : ContMDiffOn ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
        (modelWithCornersSelf ℝ (Fin 10 → ℝ))) 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) ∞
        (fun y : Y13o X => (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY y)) V := by
      rw [← contMDiffOn_modelProd_target_iff]
      exact (contMDiffOn_chart (x := q0.proj)).comp contMDiff_subtype_val.contMDiffOn
        fun y hy => hy.1
    exact (hσ.comp hcY fun y (hy : y ∈ V) => (interior_subset hy.2 : _)).congr
      fun y hy => hσY y hy
  · obtain ⟨-, hfst, hsrc⟩ := hσp (cY y) (interior_subset hy.2)
    apply Subtype.ext
    show ((σY y : OFr X) : HomTotM X).proj = y
    rw [hσY y hy]
    have h1 := chart_fst q0 _ hsrc
    rw [hfst] at h1
    exact cY.injOn (proj_mem_chart_source q0 _ hsrc) hy.1 h1.symm
  · rw [hσY y hy]; exact hmem y hy

/-- **Phase 3, item 3: the adapted frames `AFr` are a reduction of the chimeric orthonormal frame
bundle `OFr → Y13` to the block group `Gblk ≅ O(6,4) × O(1,3)`.** -/
noncomputable def adaptedReduction :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    SmoothReduction (frameBundle (X := X)) Gblk := by
  letI := regCharted (Fframe_regular (X := X))
  haveI := isManifold_regularLevel (Fframe_regular (X := X))
  exact
  { carrier := {p : OFr X | (p : HomTotM X) ∈ AFr X}
    act_mem := fun p hp g hg => ractM_mem_AFr_blk hp hg
    transitive := fun p hp q hq hpq => by
      obtain ⟨g, hg, he⟩ := adapted_fibre_transitive hp hq (congrArg Subtype.val hpq)
      exact ⟨g, hg, Subtype.ext he⟩
    locSec := adapted_locSec }

/-- **The aligned Pati–Salam groups act on the reduced (adapted) bundle.** -/
theorem adaptedReduction_PS6' :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ∀ p ∈ (adaptedReduction (X := X)).carrier, ∀ g ∈ PS6',
      (frameBundle (X := X)).act p g ∈ (adaptedReduction (X := X)).carrier := by
  letI := regCharted (Fframe_regular (X := X))
  haveI := isManifold_regularLevel (Fframe_regular (X := X))
  exact fun p hp g hg => (adaptedReduction (X := X)).act_mem p hp g (PS6'_le_Gblk hg)

theorem adaptedReduction_PS4' :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ∀ p ∈ (adaptedReduction (X := X)).carrier, ∀ g ∈ PS4',
      (frameBundle (X := X)).act p g ∈ (adaptedReduction (X := X)).carrier := by
  letI := regCharted (Fframe_regular (X := X))
  haveI := isManifold_regularLevel (Fframe_regular (X := X))
  exact fun p hp g hg => (adaptedReduction (X := X)).act_mem p hp g (PS4'_le_Gblk hg)

end GU.Library
