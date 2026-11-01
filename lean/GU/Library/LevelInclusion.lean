/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Library.LevelManifold

namespace GU.Library
open scoped Manifold ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {c : F}

/-- **The inclusion of a regular level set is smooth.** -/
theorem contMDiff_levelSet_val (h : SmoothSubmersive f c) :
    letI := smoothLevelCharted h
    haveI := isManifold_level h
    ContMDiff 𝓘(ℝ, Fin (fibreDim E F) → ℝ) 𝓘(ℝ, E) ∞ (Subtype.val : levelSet f c → E) := by
  let _ := smoothLevelCharted h
  have _ := isManifold_level h
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun a y => ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  intro v hv
  have hvt : v ∈ (smoothLevelChart h a).target := by
    have : v ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hv.1
    exact this
  have hG : ContDiffAt ℝ ∞ (fun v => (smoothChart (a := (a : E)) h.smooth (h.surj a a.2)).symm
      (c, (kerEquiv (h.surj a a.2)).symm v)) v :=
    (contDiffAt_smoothChart_symm h.smooth (h.surj a a.2) (mem_smoothChart_target_of h a hvt)).comp v
      (contDiff_const.prodMk (kerEquiv (h.surj a a.2)).symm.contDiff).contDiffAt
  refine hG.contDiffWithinAt.congr (fun w hw => ?_) ?_
  · have hwt : w ∈ (smoothLevelChart h a).target := by
      have : w ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
        simpa [extChartAt, OpenPartialHomeomorph.extend] using hw.1
      exact this
    exact smoothLevelChart_symm_val h a hwt
  · exact smoothLevelChart_symm_val h a hvt

section Universal

variable {EM H M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ EM H} [IsManifold I ∞ M]

/-- **Universal property**: a map into a regular level set is smooth iff it is smooth into `E`. -/
theorem contMDiff_levelSet_iff (h : SmoothSubmersive f c) {g : M → levelSet f c} :
    letI := smoothLevelCharted h
    haveI := isManifold_level h
    ContMDiff I 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (fun x => (g x : E)) := by
  let _ := smoothLevelCharted h
  have _ := isManifold_level h
  refine ⟨fun hg => (contMDiff_levelSet_val h).comp hg, fun hg => ?_⟩
  rw [contMDiff_iff] at hg ⊢
  refine ⟨Topology.IsInducing.subtypeVal.continuous_iff.mpr hg.1, fun x y => ?_⟩
  have hx := hg.2 x (0 : E)
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    PartialEquiv.refl_source, Set.preimage_univ, Set.inter_univ] at hx
  have hL : ContDiff ℝ ∞ (fun z : E => kerEquiv (h.surj y y.2) (kerProj (fderiv ℝ f y) (z - y))) :=
    (kerEquiv (h.surj y y.2)).contDiff.comp
      ((kerProj (fderiv ℝ f y)).contDiff.comp (contDiff_id.sub contDiff_const))
  refine (hL.comp_contDiffOn (hx.mono Set.inter_subset_left)).congr (fun w _ => ?_)
  rfl

/-- **Universal property on a set**: a map into a regular level set is smooth on `t` iff it is
smooth on `t` into `E`. -/
theorem contMDiffOn_levelSet_iff (h : SmoothSubmersive f c) {g : M → levelSet f c} {t : Set M} :
    letI := smoothLevelCharted h
    haveI := isManifold_level h
    ContMDiffOn I 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ g t ↔
      ContMDiffOn I 𝓘(ℝ, E) ∞ (fun x => (g x : E)) t := by
  let _ := smoothLevelCharted h
  have _ := isManifold_level h
  refine ⟨fun hg => (contMDiff_levelSet_val h).comp_contMDiffOn hg, fun hg => ?_⟩
  rw [contMDiffOn_iff] at hg ⊢
  refine ⟨(Topology.IsInducing.subtypeVal.continuousOn_iff).mpr hg.1, fun x y => ?_⟩
  have hx := hg.2 x (0 : E)
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    PartialEquiv.refl_source, Set.preimage_univ, Set.inter_univ] at hx
  have hL : ContDiff ℝ ∞ (fun z : E => kerEquiv (h.surj y y.2) (kerProj (fderiv ℝ f y) (z - y))) :=
    (kerEquiv (h.surj y y.2)).contDiff.comp
      ((kerProj (fderiv ℝ f y)).contDiff.comp (contDiff_id.sub contDiff_const))
  refine (hL.comp_contDiffOn (hx.mono ?_)).congr (fun w _ => ?_)
  · exact fun w hw => ⟨hw.1, hw.2.1⟩
  · rfl

end Universal

end GU.Library
