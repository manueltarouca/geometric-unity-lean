import GU.Library.LevelOpen

/-!
# L2d: the inclusion and the universal property for `SmoothSubmersiveOn`

Port of `LevelInclusion.lean` to level sets of maps smooth only on an open `U`:
`contMDiff_levelSetOn_val` (the inclusion into `E` is smooth) and `contMDiff_levelSetOn_iff`
(a map into the level set is smooth iff it is smooth into `E`).
-/

namespace GU.Library
open scoped Manifold ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {c : F} {U : Set E}

/-- **The inclusion of a regular level set is smooth** (`f` smooth on `U`). -/
theorem contMDiff_levelSetOn_val (h : SmoothSubmersiveOn f c U) :
    letI := smoothLevelChartedOn h
    haveI := isManifold_levelOn h
    ContMDiff 𝓘(ℝ, Fin (fibreDim E F) → ℝ) 𝓘(ℝ, E) ∞ (Subtype.val : levelSet f c → E) := by
  let _ := smoothLevelChartedOn h
  have _ := isManifold_levelOn h
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun a y => ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  intro v hv
  have hvt : v ∈ (smoothLevelChartOn h a).target := by
    have : v ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hv.1
    exact this
  have hG : ContDiffAt ℝ ∞ (fun v => (smoothChartOn (a := (a : E)) h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2)).symm
      (c, (kerEquiv (h.surj a a.2)).symm v)) v :=
    (contDiffAt_smoothChartOn_symm h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2) (mem_smoothChartOn_target_of h a hvt)).comp v
      (contDiff_const.prodMk (kerEquiv (h.surj a a.2)).symm.contDiff).contDiffAt
  refine hG.contDiffWithinAt.congr (fun w hw => ?_) ?_
  · have hwt : w ∈ (smoothLevelChartOn h a).target := by
      have : w ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
        simpa [extChartAt, OpenPartialHomeomorph.extend] using hw.1
      exact this
    exact smoothLevelChartOn_symm_val h a hwt
  · exact smoothLevelChartOn_symm_val h a hvt

section Universal

variable {EM H M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ EM H} [IsManifold I ∞ M]

/-- **Universal property** (`f` smooth on `U`): a map into a regular level set is smooth iff it is smooth into `E`. -/
theorem contMDiff_levelSetOn_iff (h : SmoothSubmersiveOn f c U) {g : M → levelSet f c} :
    letI := smoothLevelChartedOn h
    haveI := isManifold_levelOn h
    ContMDiff I 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (fun x => (g x : E)) := by
  let _ := smoothLevelChartedOn h
  have _ := isManifold_levelOn h
  refine ⟨fun hg => (contMDiff_levelSetOn_val h).comp hg, fun hg => ?_⟩
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

end Universal

end GU.Library
