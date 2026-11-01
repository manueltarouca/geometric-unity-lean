import GU.Library.RegularValue

/-!
# Manifold structure pulled back along a local homeomorphism

For a local homeomorphism `f : P → M` to a smooth manifold `M` modelled on `E`, `P` gets charts
"local inverse of `f`, then chart of `M`" (`pullCharted`, `isManifold_pull`). For this structure:
`f` is smooth (`contMDiff_pull`) and a local diffeomorphism (`isLocalDiffeomorph_pull`), and a map into
`P` is smooth iff it is continuous and its composite with `f` is smooth
(`contMDiffAt_into_pull_iff`, `contMDiff_into_pull_iff`, `contMDiffOn_into_pull_iff`).
-/

namespace GU.Library

open TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {P : Type*} [TopologicalSpace P] {f : P → M}

/-- A local inverse domain of `f`. -/
def pullE (hf : IsLocalHomeomorph f) (s : P) : OpenPartialHomeomorph P M := (hf s).choose

lemma pullE_mem (hf : IsLocalHomeomorph f) (s : P) : s ∈ (pullE hf s).source := (hf s).choose_spec.1

lemma pullE_coe (hf : IsLocalHomeomorph f) (s : P) : f = pullE hf s := (hf s).choose_spec.2

/-- The chart of `P` at `s`. -/
def pullChart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {P : Type*} [TopologicalSpace P] {f : P → M} (hf : IsLocalHomeomorph f)
    (s : P) : OpenPartialHomeomorph P E :=
  (pullE hf s).trans (chartAt E (f s))

lemma pullChart_apply (hf : IsLocalHomeomorph f) (s t : P) :
    pullChart E hf s t = chartAt E (f s) (f t) := by
  show chartAt E (f s) (pullE hf s t) = _
  rw [← pullE_coe]

/-- **The pulled-back charted space.** -/
@[instance_reducible] def pullCharted (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {P : Type*} [TopologicalSpace P]
    {f : P → M} (hf : IsLocalHomeomorph f) : ChartedSpace E P where
  atlas := Set.range (pullChart E hf)
  chartAt := pullChart E hf
  mem_chart_source s := by
    rw [pullChart, OpenPartialHomeomorph.trans_source]
    refine ⟨pullE_mem hf s, ?_⟩
    show pullE hf s s ∈ (chartAt E (f s)).source
    rw [← pullE_coe]; exact mem_chart_source E _
  chart_mem_atlas s := ⟨s, rfl⟩

lemma mem_pullChart_source (hf : IsLocalHomeomorph f) {s t : P}
    (ht : t ∈ (pullChart E hf s).source) : f t ∈ (chartAt E (f s)).source := by
  rw [pullChart, OpenPartialHomeomorph.trans_source] at ht
  have h : pullE hf s t ∈ (chartAt E (f s)).source := ht.2
  rwa [← pullE_coe] at h

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **`P` is a smooth manifold.** -/
theorem isManifold_pull (hf : IsLocalHomeomorph f) :
    letI := pullCharted E hf
    IsManifold 𝓘(ℝ, E) ∞ P := by
  letI := pullCharted E hf
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ]
  have hg := chartTrans_contDiffOn (E := E) (f a) (f b)
  have hsub : ∀ v ∈ ((pullChart E hf a).symm.trans (pullChart E hf b)).source,
      v ∈ ((chartAt E (f a)).symm.trans (chartAt E (f b))).source ∧
      ((pullChart E hf a).symm.trans (pullChart E hf b)) v =
        ((chartAt E (f a)).symm.trans (chartAt E (f b))) v := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_source] at hv
    have hva : v ∈ (pullChart E hf a).target := hv.1
    set w := (pullChart E hf a).symm v
    have hwa : w ∈ (pullChart E hf a).source := (pullChart E hf a).map_target hva
    have hwb : w ∈ (pullChart E hf b).source := hv.2
    have hw1 : chartAt E (f a) (f w) = v := by
      rw [← pullChart_apply hf]; exact (pullChart E hf a).right_inv hva
    have hwO := mem_pullChart_source hf hwa
    have hw2 : (chartAt E (f a)).symm v = f w := by
      rw [← hw1]; exact (chartAt E (f a)).left_inv hwO
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨?_, ?_⟩
      · show v ∈ (chartAt E (f a)).target
        rw [← hw1]; exact (chartAt E (f a)).map_source hwO
      · show (chartAt E (f a)).symm v ∈ (chartAt E (f b)).source
        rw [hw2]; exact mem_pullChart_source hf hwb
    · show pullChart E hf b w = chartAt E (f b) ((chartAt E (f a)).symm v)
      rw [hw2, pullChart_apply hf]
  exact (hg.mono fun v hv => (hsub v hv).1).congr fun v hv => (hsub v hv).2

/-- **`f` is smooth.** -/
theorem contMDiff_pull (hf : IsLocalHomeomorph f) :
    letI := pullCharted E hf
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f := by
  letI := pullCharted E hf
  intro s
  rw [contMDiffAt_iff]
  refine ⟨hf.continuous.continuousAt, ?_⟩
  have hev : (extChartAt 𝓘(ℝ, E) (f s) ∘ f ∘ (extChartAt 𝓘(ℝ, E) s).symm)
      =ᶠ[𝓝[Set.range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) s s)] id := by
    have ht : (pullChart E hf s).target ∈ 𝓝 (pullChart E hf s s) :=
      (pullChart E hf s).open_target.mem_nhds ((pullChart E hf s).map_source (mem_chart_source E s))
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds ht) fun v hv => ?_
    show chartAt E (f s) (f ((pullChart E hf s).symm v)) = v
    rw [← pullChart_apply hf]; exact (pullChart E hf s).right_inv hv
  exact contDiffWithinAt_id.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin (by simp))

section Universal

variable {EM HM N : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace N] [ChartedSpace HM N] {I : ModelWithCorners ℝ EM HM}

/-- **A map into `P` is smooth at a point iff it is continuous there and its composite with `f` is
smooth there.** -/
theorem contMDiffAt_into_pull_iff (hf : IsLocalHomeomorph f) {g : N → P} {x : N} :
    letI := pullCharted E hf
    ContMDiffAt I 𝓘(ℝ, E) ∞ g x ↔
      ContinuousAt g x ∧ ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y => f (g y)) x := by
  letI := pullCharted E hf
  constructor
  · intro h
    exact ⟨h.continuousAt, (contMDiff_pull hf (g x)).comp x h⟩
  · rintro ⟨hc, h⟩
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨hc, ?_⟩
    have e : (extChartAt 𝓘(ℝ, E) (g x) ∘ g ∘ (extChartAt I x).symm) =
        (extChartAt 𝓘(ℝ, E) (f (g x)) ∘ (fun y => f (g y)) ∘ (extChartAt I x).symm) := by
      funext v
      exact pullChart_apply hf (g x) (g ((extChartAt I x).symm v))
    rw [e]; exact h.2

theorem contMDiff_into_pull_iff (hf : IsLocalHomeomorph f) {g : N → P} :
    letI := pullCharted E hf
    ContMDiff I 𝓘(ℝ, E) ∞ g ↔
      Continuous g ∧ ContMDiff I 𝓘(ℝ, E) ∞ (fun y => f (g y)) := by
  letI := pullCharted E hf
  exact ⟨fun h => ⟨h.continuous, (contMDiff_pull hf).comp h⟩, fun ⟨hc, h⟩ x =>
    (contMDiffAt_into_pull_iff hf).mpr ⟨hc.continuousAt, h x⟩⟩

theorem contMDiffOn_into_pull_iff (hf : IsLocalHomeomorph f) {g : N → P} {t : Set N}
    (ht : IsOpen t) :
    letI := pullCharted E hf
    ContMDiffOn I 𝓘(ℝ, E) ∞ g t ↔
      ContinuousOn g t ∧ ContMDiffOn I 𝓘(ℝ, E) ∞ (fun y => f (g y)) t := by
  letI := pullCharted E hf
  constructor
  · intro h
    exact ⟨h.continuousOn, (contMDiff_pull hf).comp_contMDiffOn h⟩
  · rintro ⟨hc, h⟩ x hx
    exact ((contMDiffAt_into_pull_iff hf).mpr ⟨hc.continuousAt (ht.mem_nhds hx),
      h.contMDiffAt (ht.mem_nhds hx)⟩).contMDiffWithinAt

end Universal

/-- The local inverse of `f` is smooth. -/
lemma contMDiffOn_pullE_symm (hf : IsLocalHomeomorph f) (s : P) :
    letI := pullCharted E hf
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (pullE hf s).symm (pullE hf s).target := by
  letI := pullCharted E hf
  rw [contMDiffOn_into_pull_iff hf (pullE hf s).open_target]
  refine ⟨(pullE hf s).continuousOn_symm, contMDiff_id.contMDiffOn.congr fun g hg => ?_⟩
  show f ((pullE hf s).symm g) = g
  exact (congrFun (pullE_coe hf s) _).trans ((pullE hf s).right_inv hg)

/-- **`f` is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_pull (hf : IsLocalHomeomorph f) :
    letI := pullCharted E hf
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f := by
  letI := pullCharted E hf
  exact fun s => ⟨{ (pullE hf s).toPartialEquiv with
      open_source := (pullE hf s).open_source
      open_target := (pullE hf s).open_target
      contMDiffOn_toFun := by
        refine (contMDiff_pull hf).contMDiffOn.congr fun t _ => ?_
        exact congrFun (pullE_coe hf s).symm t
      contMDiffOn_invFun := contMDiffOn_pullE_symm hf s },
    pullE_mem hf s, fun t _ => congrFun (pullE_coe hf s) t⟩

end

end GU.Library
