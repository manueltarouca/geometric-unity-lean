import GU.Library.LevelManifold

/-!
# Track 3, L2c: regular level sets of maps smooth only on an open set

`SmoothSubmersiveOn f c U`: `U` is open, `f` is `C^∞` on `U`, the level set `f⁻¹{c}` lies in `U`,
and `f′` is surjective along it. This is what charts of `Y` need (the chimeric metric is only
defined chartwise; outside `U` one may set `f` to any value `≠ c`). The construction reuses the
generic slice charts (`sliceG`) and `ψ x = (f x, Q(x − a))`, now restricted to
`U ∩ {dψ invertible}`. Transitions only use the inverse charts (smooth by the inverse function
theorem at points of `U`) and the linear second component of `ψ`, so
**`isManifold_levelOn`**: the level set is a smooth manifold of dimension `dim E − dim F`.
-/

namespace GU.Library

open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Smooth submersion hypothesis, smoothness only on an open set `U ⊇ f⁻¹{c}`. -/
structure SmoothSubmersiveOn (f : E → F) (c : F) (U : Set E) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ f U
  sub : ∀ x, f x = c → x ∈ U
  surj : ∀ x, f x = c → (fderiv ℝ f x).range = ⊤

/-- A globally smooth submersion is one on `univ`. -/
lemma SmoothSubmersive.toOn {f : E → F} {c : F} (h : SmoothSubmersive f c) :
    SmoothSubmersiveOn f c Set.univ :=
  ⟨isOpen_univ, h.smooth.contDiffOn, fun _ _ => Set.mem_univ _, h.surj⟩

section ChartOn

variable {f : E → F} {a : E} {U : Set E}

lemma ψmap_contDiffAt (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (ψmap f a) x :=
  (hf.contDiffAt (hU.mem_nhds hx)).prodMk
    ((kerProj (fderiv ℝ f a)).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

lemma hasFDerivAt_ψmapOn (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    HasFDerivAt (ψmap f a) (ψderiv f a x) x := by
  have h1 : HasFDerivAt f (fderiv ℝ f x) x :=
    ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => kerProj (fderiv ℝ f a) (y - a)) (kerProj (fderiv ℝ f a)) x := by
    have := (kerProj (fderiv ℝ f a)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
    rwa [ContinuousLinearMap.comp_id] at this
  exact h1.prodMk h2

lemma isOpen_invSetOn (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) : IsOpen (U ∩ invSet f a) := by
  have hc : ContinuousOn (fun x => ψderiv f a x) U := by
    have hd : ContinuousOn (fun x => fderiv ℝ f x) U :=
      hf.continuousOn_fderiv_of_isOpen hU (by simp)
    have : (fun x => ψderiv f a x) = fun x =>
        ContinuousLinearMap.prodₗᵢ ℝ (fderiv ℝ f x, kerProj (fderiv ℝ f a)) := rfl
    rw [this]
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn (hd.prodMk continuousOn_const)
  exact hc.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen

/-- The smooth chart at `a ∈ U`, restricted to `U ∩ {dψ invertible}`. -/
noncomputable def smoothChartOn (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U)
    (hg : (fderiv ℝ f a).range = ⊤) : OpenPartialHomeomorph E (F × (fderiv ℝ f a).ker) :=
  ((ψmap_contDiffAt (a := a) hU hf ha).toOpenPartialHomeomorph (ψmap f a)
      (f' := derivEquiv (fderiv ℝ f a) hg)
      (by rw [← ψderiv_self hg]; exact hasFDerivAt_ψmapOn hU hf ha) (by simp)).restrOpen
    (U ∩ invSet f a) (isOpen_invSetOn hU hf)

lemma smoothChartOn_coe (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U)
    (hg : (fderiv ℝ f a).range = ⊤) :
    (smoothChartOn hU hf ha hg : E → F × (fderiv ℝ f a).ker) = ψmap f a := rfl

lemma mem_smoothChartOn_source (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U)
    (hg : (fderiv ℝ f a).range = ⊤) : a ∈ (smoothChartOn hU hf ha hg).source :=
  ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, ha, mem_invSet_self hg⟩

lemma contDiffAt_smoothChartOn_symm (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U)
    (hg : (fderiv ℝ f a).range = ⊤) {y : F × (fderiv ℝ f a).ker}
    (hy : y ∈ (smoothChartOn hU hf ha hg).target) :
    ContDiffAt ℝ ∞ (smoothChartOn hU hf ha hg).symm y := by
  have hx := (smoothChartOn hU hf ha hg).map_target hy
  obtain ⟨hxU, D, hD⟩ := hx.2
  refine (smoothChartOn hU hf ha hg).contDiffAt_symm hy (f₀' := D) ?_ ?_
  · rw [hD]; exact hasFDerivAt_ψmapOn hU hf hxU
  · exact ψmap_contDiffAt hU hf hxU

end ChartOn

section ManifoldOn

variable {f : E → F} {c : F} {U : Set E}

/-- The chart at `a ∈ f⁻¹{c}`. -/
noncomputable def smoothLevelChartOn (h : SmoothSubmersiveOn f c U) (a : levelSet f c) :
    OpenPartialHomeomorph (levelSet f c) (Fin (fibreDim E F) → ℝ) :=
  (sliceG (smoothChartOn (a := (a : E)) h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2))
      (fun _ => rfl) a.2).trans
    (kerEquiv (h.surj a a.2)).toHomeomorph.toOpenPartialHomeomorph

/-- **Smooth charted structure** on a regular level set of a map smooth on `U`. -/
@[instance_reducible] noncomputable def smoothLevelChartedOn (h : SmoothSubmersiveOn f c U) :
    ChartedSpace (Fin (fibreDim E F) → ℝ) (levelSet f c) where
  atlas := Set.range (smoothLevelChartOn h)
  chartAt := smoothLevelChartOn h
  mem_chart_source a := by
    rw [smoothLevelChartOn, OpenPartialHomeomorph.trans_source]
    exact ⟨mem_smoothChartOn_source h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2), Set.mem_univ _⟩
  chart_mem_atlas a := ⟨a, rfl⟩

lemma mem_smoothChartOn_target_of (h : SmoothSubmersiveOn f c U) (a : levelSet f c)
    {v : Fin (fibreDim E F) → ℝ} (hv : v ∈ (smoothLevelChartOn h a).target) :
    (c, (kerEquiv (h.surj a a.2)).symm v) ∈
      (smoothChartOn (a := (a : E)) h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2)).target := by
  rw [smoothLevelChartOn, OpenPartialHomeomorph.trans_target] at hv
  exact hv.2

lemma smoothLevelChartOn_symm_val (h : SmoothSubmersiveOn f c U) (a : levelSet f c)
    {v : Fin (fibreDim E F) → ℝ} (hv : v ∈ (smoothLevelChartOn h a).target) :
    (((smoothLevelChartOn h a).symm v : levelSet f c) : E) =
      (smoothChartOn (a := (a : E)) h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2)).symm
        (c, (kerEquiv (h.surj a a.2)).symm v) :=
  sliceInvG_val (f := f) _ (fun _ => rfl) a.2 (mem_smoothChartOn_target_of h a hv)

/-- **Regular level sets of maps smooth on an open set are smooth manifolds.** -/
theorem isManifold_levelOn (h : SmoothSubmersiveOn f c U) :
    letI := smoothLevelChartedOn h
    IsManifold 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ (levelSet f c) := by
  let _ := smoothLevelChartedOn h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ]
  set Ka := kerEquiv (h.surj a a.2)
  set Kb := kerEquiv (h.surj b b.2)
  set φa := smoothChartOn (a := (a : E)) h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2)
  set φb := smoothChartOn (a := (b : E)) h.isOpen h.smooth (h.sub b b.2) (h.surj b b.2)
  let G : (Fin (fibreDim E F) → ℝ) → (Fin (fibreDim E F) → ℝ) :=
    fun v => Kb (kerProj (fderiv ℝ f b) (φa.symm (c, Ka.symm v) - b))
  intro v hv
  have hvt : v ∈ (smoothLevelChartOn h a).target := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hv; exact hv.1
  have hG : ContDiffAt ℝ ∞ G v := by
    have h1 : ContDiffAt ℝ ∞ (fun v => (c, Ka.symm v)) v :=
      (contDiff_const.prodMk Ka.symm.contDiff).contDiffAt
    have h2 := (contDiffAt_smoothChartOn_symm h.isOpen h.smooth (h.sub a a.2) (h.surj a a.2)
      (mem_smoothChartOn_target_of h a hvt)).comp v h1
    have h3 : ContDiff ℝ ∞ (fun x : E => Kb (kerProj (fderiv ℝ f b) (x - b))) :=
      Kb.contDiff.comp ((kerProj (fderiv ℝ f b)).contDiff.comp (contDiff_id.sub contDiff_const))
    exact h3.contDiffAt.comp v h2
  refine hG.contDiffWithinAt.congr (fun w hw => ?_) ?_
  · have hwt : w ∈ (smoothLevelChartOn h a).target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw; exact hw.1
    show Kb ((φb ((smoothLevelChartOn h a).symm w : E)).2) = G w
    rw [smoothLevelChartOn_symm_val h a hwt]; rfl
  · show Kb ((φb ((smoothLevelChartOn h a).symm v : E)).2) = G v
    rw [smoothLevelChartOn_symm_val h a hvt]; rfl

end ManifoldOn

section Extend

variable {f : E → F} {c : F} {U : Set E}

open Classical in
/-- **Extension recipe**: a map smooth and submersive on an open `U`, set to a value `d ≠ c`
outside `U`, satisfies `SmoothSubmersiveOn`; its level set is `{x ∈ U | f x = c}`. -/
lemma smoothSubmersiveOn_extend (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : ∀ x ∈ U, f x = c → (fderiv ℝ f x).range = ⊤) (d : F) (hd : d ≠ c) :
    SmoothSubmersiveOn (fun x => if x ∈ U then f x else d) c U := by
  have heq : ∀ x ∈ U, (fun y => if y ∈ U then f y else d) =ᶠ[nhds x] f := fun x hx =>
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => if_pos hy
  refine ⟨hU, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact ((hf.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq (heq x hx)).contDiffWithinAt
  · by_contra h; simp only [if_neg h] at hx; exact hd hx
  · have hxU : x ∈ U := by by_contra h; simp only [if_neg h] at hx; exact hd hx
    rw [(heq x hxU).fderiv_eq]
    exact hs x hxU (by simpa [if_pos hxU] using hx)

open Classical in
lemma mem_levelSet_extend_iff (d : F) (hd : d ≠ c) (x : E) :
    x ∈ levelSet (fun x => if x ∈ U then f x else d) c ↔ x ∈ U ∧ f x = c := by
  show (if x ∈ U then f x else d) = c ↔ _
  by_cases h : x ∈ U <;> simp [h, hd]

end Extend

end GU.Library
