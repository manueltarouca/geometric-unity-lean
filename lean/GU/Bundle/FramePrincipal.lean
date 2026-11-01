/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.LocalTrivInverse
import GU.Library.SmoothPrincipal
import GU.Observerse.Y13Open

/-!
# Phase 3, item 2: the chimeric orthonormal frame bundle is a smooth principal `O(7,7)`-bundle

Base: `Y13o`, the (1,3) part of `Y` as an open submanifold (`isOpen_Y13`). Total space: `OFr X`
(regular-level-set manifold). Group: `O77` (Lie group). **`frameBundle`**: a
`SmoothPrincipalBundle`; local triviality from `localTriv_diffeo`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

section Conv

variable {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
  [NormedSpace ℝ E2] {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I' ∞ M']

/-- Target-side `ModelProd` conversion. -/
theorem contMDiffOn_modelProd_target_iff {f : M' → ModelProd E1 E2} {s : Set M'} :
    ContMDiffOn I' ((modelWithCornersSelf ℝ E1).prod (modelWithCornersSelf ℝ E2)) ∞ f s ↔
      ContMDiffOn I' 𝓘(ℝ, E1 × E2) ∞ (fun x => (show E1 × E2 from f x)) s := by
  rw [contMDiffOn_iff, contMDiffOn_iff]
  constructor <;> rintro ⟨hc, hd⟩ <;> refine ⟨hc, fun x y => ?_⟩ <;>
    · convert hd x y using 2 <;>
        first | rfl | simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def, Set.ext_iff]

end Conv

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The total-space chart domain depends only on the base point. -/
lemma mem_chart_source_iff (a q : HomTotM X) :
    q ∈ (chartAt HomModel a).source ↔
      q.proj ∈ (trivializationAt HomF (HomCb (X := X)) a.proj).baseSet ∧
      q.proj ∈ (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).source := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a]
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    OpenPartialHomeomorph.prod_source, Set.mem_prod, OpenPartialHomeomorph.refl_source,
    Set.mem_univ, and_true, Trivialization.mem_source]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Trivialization.coe_coe, Trivialization.coe_fst' _ h1] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Trivialization.coe_coe, Trivialization.coe_fst' _ h1]

/-- The (1,3) locus as an open subset of `Y`. -/
def Y13o (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Opens (Yobs X) :=
  ⟨{y | ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * GU.Chimeric.ηR * Pᵀ}, GU.Observerse.isOpen_Y13⟩

lemma proj_mem_Y13o {q : HomTotM X} (hq : q ∈ OFr X) : q.proj ∈ Y13o X := by
  have : q ∈ orthoSetM := by rw [← levelSet_Fframe]; exact hq
  exact (orthoM_iff_13 q.proj).mp ⟨q, rfl, this⟩

/-- The bundle projection `OFr → Y13`. -/
noncomputable def projOFr (q : OFr X) : Y13o X := ⟨(q : HomTotM X).proj, proj_mem_Y13o q.2⟩

/-- The right `O77`-action on `OFr`. -/
noncomputable def actOFr' (q : OFr X) (g : O77) : OFr X := ⟨ractM q g, ractM_mem_OFr q.2 g⟩

/-- **Local triviality** of the frame bundle over `Y13`. -/
theorem frame_locTriv (b : Y13o X) :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ∃ V : Set (Y13o X), IsOpen V ∧ b ∈ V ∧ ∃ (σ : Y13o X → OFr X) (τ : OFr X → O77),
      ContMDiffOn ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
        𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ σ V ∧
      (∀ y ∈ V, projOFr (σ y) = y) ∧
      ContMDiffOn 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ)
        𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ τ (projOFr ⁻¹' V) ∧
      (∀ p ∈ projOFr ⁻¹' V, actOFr' (σ (projOFr p)) (τ p) = p) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨q0, hq0p, ho⟩ := (orthoM_iff_13 (b : Yobs X)).mpr b.2
  have hq0 : q0 ∈ OFr X := by rw [OFr, levelSet_Fframe]; exact ho
  obtain ⟨U, hU, Ψ, Ψinv, W, hΨ, hΨinv, h3, h4, hUo, hWo, hq0W, hbase, hequiv, hW⟩ :=
    localTriv_diffeo q0 hq0
  set c := chartAt HomModel q0
  set cY := chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj
  set tb := (trivializationAt HomF (HomCb (X := X)) q0.proj).baseSet
  let Vy : Set (Yobs X) := {y | y ∈ tb ∧ y ∈ cY.source ∧ (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY y) ∈ U}
  have hVy : IsOpen Vy := by
    have h1 := cY.isOpen_inter_preimage (s := U) hUo
    have h2 := (trivializationAt HomF (HomCb (X := X)) q0.proj).open_baseSet
    have : Vy = tb ∩ (cY.source ∩ cY ⁻¹' U) := by
      ext y; exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
    rw [this]; exact h2.inter h1
  let V : Set (Y13o X) := Subtype.val ⁻¹' Vy
  have hV : IsOpen V := hVy.preimage continuous_subtype_val
  have hbV : b ∈ V := by
    show (b : Yobs X) ∈ Vy
    rw [← hq0p]
    refine ⟨FiberBundle.mem_baseSet_trivializationAt HomF (HomCb (X := X)) q0.proj,
      mem_chart_source _ _, ?_⟩
    have := ((hW _).mp hq0W).2
    rwa [chart_fst q0 q0 (mem_chart_source _ q0)] at this
  -- section and division map
  let σ : Y13o X → OFr X := fun y => Ψ ((show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY y), 1)
  let τ : OFr X → O77 := fun p => (Ψinv p).2
  have hWsub : projOFr ⁻¹' V ⊆ W := by
    intro p hp
    have hp' : (p : HomTotM X).proj ∈ Vy := hp
    have hs : (p : HomTotM X) ∈ c.source := (mem_chart_source_iff q0 _).mpr ⟨hp'.1, hp'.2.1⟩
    refine (hW p).mpr ⟨hs, ?_⟩
    have := hp'.2.2
    rwa [← chart_fst q0 _ hs] at this
  refine ⟨V, hV, hbV, σ, τ, ?_, ?_, ?_, ?_⟩
  · -- σ smooth
    have hcY : ContMDiffOn ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
        𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) ∞
        (fun y : Y13o X => (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY y)) V := by
      rw [← contMDiffOn_modelProd_target_iff]
      exact (contMDiffOn_chart (x := q0.proj)).comp contMDiff_subtype_val.contMDiffOn
        fun y hy => hy.2.1
    exact hΨ.comp (hcY.prodMk contMDiffOn_const) fun y hy => ⟨hy.2.2, Set.mem_univ _⟩
  · -- σ is a section
    intro y hy
    have hy' : (y : Yobs X) ∈ Vy := hy
    have hyU : ((show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY y), (1 : O77)) ∈ U ×ˢ (Set.univ : Set O77) :=
      ⟨hy'.2.2, Set.mem_univ _⟩
    have hmem := (hW _).mp (h3 _ hyU).1
    have hb := hbase _ hyU
    have hf := chart_fst q0 _ hmem.1
    apply Subtype.ext
    exact cY.injOn (proj_mem_chart_source q0 _ hmem.1) hy'.2.1 (hf.symm.trans hb)
  · -- τ smooth
    exact ((contMDiff_snd.comp_contMDiffOn hΨinv)).mono hWsub
  · -- reconstruction
    intro p hp
    have hpW := hWsub hp
    obtain ⟨hin, hΨΨ⟩ := h4 p hpW
    have he : (Ψinv p).1 = (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY (p : HomTotM X).proj) := by
      have := hbase _ hin
      rw [hΨΨ, chart_fst q0 _ ((hW p).mp hpW).1] at this
      exact this.symm
    apply Subtype.ext
    show ractM (Ψ ((show (Fin 4 → ℝ) × (Fin 10 → ℝ) from cY (p : HomTotM X).proj), 1) : HomTotM X)
      (Ψinv p).2 = p
    rw [← he, ← hequiv _ hin.1 1 (Ψinv p).2, one_mul]
    exact congrArg Subtype.val hΨΨ

/-- **Phase 3, item 2: the chimeric (7,7)-orthonormal frame bundle `OFr → Y13` is a smooth
principal `O(7,7)`-bundle.** -/
noncomputable def frameBundle :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    SmoothPrincipalBundle ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
      𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ)
      (Y13o X) O77 (OFr X) := by
  letI := regCharted (Fframe_regular (X := X))
  haveI := isManifold_regularLevel (Fframe_regular (X := X))
  exact
  { proj := projOFr
    act := actOFr'
    act_one := fun p => Subtype.ext (ractM_one _)
    act_mul := fun p g h => Subtype.ext (ractM_mul _ g h)
    proj_act := fun _ _ => rfl
    free := fun p g h => by
      have hp : (p : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact p.2
      exact ractM_free hp g (congrArg Subtype.val h)
    transitive := fun p q h => by
      have hp : (p : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact p.2
      have hq : (q : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact q.2
      obtain ⟨g, hg⟩ := ractM_transitive' hp hq (congrArg Subtype.val h)
      exact ⟨g, Subtype.ext hg⟩
    proj_surjective := fun b => by
      obtain ⟨q, hqp, ho⟩ := (orthoM_iff_13 (b : Yobs X)).mpr b.2
      exact ⟨⟨q, by rw [OFr, levelSet_Fframe]; exact ho⟩, Subtype.ext hqp⟩
    smooth_proj := by
      rw [← ContMDiff.subtypeVal_comp_iff]
      exact contMDiff_OFr_proj
    smooth_act := contMDiff_actOFr
    locTriv := frame_locTriv }

end GU.Library
