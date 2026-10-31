import GU.Library.LevelSet

/-!
# Track 3, L2: explicit submersion charts with smooth inverses (parts A–C)

For `f : E → F` (finite-dimensional real spaces) with surjective derivative `g = f'(a)`, fix a
continuous projection `Q : E →L ker g` (`kerProj`), and set `ψ x = (f x, Q (x − a))`. Its derivative
at `a` is the isomorphism `(g, Q) : E ≃L F × ker g` (`derivEquiv`), so the inverse function theorem
gives a local homeomorphism whose first component is exactly `f`.

Part C restricts these to the level set (`sliceG`, `smoothLevelChart`) and proves the transition
maps are `C^∞`, so **`isManifold_level`**: a regular level set `f⁻¹{c}` of a smooth map with
surjective derivative along it is a smooth manifold modelled on `ℝ^(dim E − dim F)`.
-/

namespace GU.Library

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A continuous projection onto `ker g`. -/
noncomputable def kerProj (g : E →L[ℝ] F) : E →L[ℝ] g.ker :=
  Classical.choose (g.ker_closedComplemented_of_finiteDimensional_range)

lemma kerProj_apply (g : E →L[ℝ] F) (y : g.ker) : kerProj g y = y :=
  Classical.choose_spec (g.ker_closedComplemented_of_finiteDimensional_range) y

/-- `(g, Q) : E →L F × ker g`. -/
noncomputable def derivPair (g : E →L[ℝ] F) : E →L[ℝ] F × g.ker := g.prod (kerProj g)

lemma derivPair_injective (g : E →L[ℝ] F) : Function.Injective (derivPair g) := by
  intro x y hxy
  rw [← sub_eq_zero]
  have hx : derivPair g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  generalize x - y = x at hx ⊢
  have h1 : g x = 0 := congrArg Prod.fst hx
  have h2 : kerProj g x = 0 := congrArg Prod.snd hx
  have hk : x ∈ g.ker := h1
  have := kerProj_apply g ⟨x, hk⟩
  rw [h2] at this
  exact (congrArg Subtype.val this).symm

lemma derivPair_surjective (g : E →L[ℝ] F) (hg : g.range = ⊤) : Function.Surjective (derivPair g) := by
  rintro ⟨y, k⟩
  obtain ⟨x0, hx0⟩ : ∃ x0, g x0 = y := by
    have : y ∈ g.range := by rw [hg]; trivial
    exact this
  have hQ : ∀ z, g (kerProj g z : E) = 0 := fun z => (kerProj g z).2
  refine ⟨x0 - (kerProj g x0 : E) + k, Prod.ext ?_ ?_⟩
  · simp [derivPair, hx0, hQ, k.2]
  · show kerProj g (x0 - (kerProj g x0 : E) + k) = k
    rw [map_add, map_sub, kerProj_apply g (kerProj g x0), kerProj_apply g k, sub_self, zero_add]

/-- The derivative isomorphism `E ≃L F × ker g`. -/
noncomputable def derivEquiv (g : E →L[ℝ] F) (hg : g.range = ⊤) : E ≃L[ℝ] F × g.ker :=
  (LinearEquiv.ofBijective (derivPair g : E →ₗ[ℝ] F × g.ker)
    ⟨derivPair_injective g, derivPair_surjective g hg⟩).toContinuousLinearEquiv

@[simp] lemma derivEquiv_apply (g : E →L[ℝ] F) (hg : g.range = ⊤) (x : E) :
    derivEquiv g hg x = (g x, kerProj g x) := rfl

/-! ### The explicit chart `ψ x = (f x, Q (x − a))` -/

open scoped ContDiff

section Chart

variable {f : E → F} {a : E}

/-- `ψ x = (f x, Q (x − a))` with `Q` the projection onto `ker f'(a)`. -/
noncomputable def ψmap (f : E → F) (a : E) : E → F × (fderiv ℝ f a).ker :=
  fun x => (f x, kerProj (fderiv ℝ f a) (x - a))

lemma ψmap_fst (x : E) : (ψmap f a x).1 = f x := rfl

lemma ψmap_contDiff (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (ψmap f a) :=
  hf.prodMk ((kerProj (fderiv ℝ f a)).contDiff.comp (contDiff_id.sub contDiff_const))

/-- Derivative of `ψ` at `x`: `(f'(x), Q)`. -/
noncomputable def ψderiv (f : E → F) (a x : E) : E →L[ℝ] F × (fderiv ℝ f a).ker :=
  (fderiv ℝ f x).prod (kerProj (fderiv ℝ f a))

lemma hasFDerivAt_ψmap (hf : ContDiff ℝ ∞ f) (x : E) : HasFDerivAt (ψmap f a) (ψderiv f a x) x := by
  have h1 : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y => kerProj (fderiv ℝ f a) (y - a)) (kerProj (fderiv ℝ f a)) x := by
    have := (kerProj (fderiv ℝ f a)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
    rwa [ContinuousLinearMap.comp_id] at this
  exact h1.prodMk h2

/-- Where the derivative of `ψ` is invertible. -/
def invSet (f : E → F) (a : E) : Set E :=
  {x | ψderiv f a x ∈ Set.range ((↑) : (E ≃L[ℝ] F × (fderiv ℝ f a).ker) → E →L[ℝ] F × (fderiv ℝ f a).ker)}

lemma isOpen_invSet (hf : ContDiff ℝ ∞ f) : IsOpen (invSet f a) := by
  have hc : Continuous fun x => ψderiv f a x := by
    have hd : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv (by simp)
    have : (fun x => ψderiv f a x) = fun x =>
        ContinuousLinearMap.prodₗᵢ ℝ (fderiv ℝ f x, kerProj (fderiv ℝ f a)) := rfl
    rw [this]
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (hd.prodMk continuous_const)
  exact ContinuousLinearEquiv.isOpen.preimage hc

lemma ψderiv_self (hg : (fderiv ℝ f a).range = ⊤) :
    ψderiv f a a = (derivEquiv (fderiv ℝ f a) hg : E →L[ℝ] F × (fderiv ℝ f a).ker) := by
  ext x <;> rfl

lemma mem_invSet_self (hg : (fderiv ℝ f a).range = ⊤) : a ∈ invSet f a :=
  ⟨derivEquiv _ hg, (ψderiv_self hg).symm⟩

/-- The smooth chart: inverse-function chart of `ψ`, restricted to where `dψ` is invertible. -/
noncomputable def smoothChart (hf : ContDiff ℝ ∞ f) (hg : (fderiv ℝ f a).range = ⊤) :
    OpenPartialHomeomorph E (F × (fderiv ℝ f a).ker) :=
  ((ψmap_contDiff (a := a) hf).contDiffAt.toOpenPartialHomeomorph (ψmap f a)
      (f' := derivEquiv (fderiv ℝ f a) hg)
      (by rw [← ψderiv_self hg]; exact hasFDerivAt_ψmap hf a) (by simp)).restrOpen
    (invSet f a) (isOpen_invSet hf)

lemma smoothChart_coe (hf : ContDiff ℝ ∞ f) (hg : (fderiv ℝ f a).range = ⊤) :
    (smoothChart hf hg : E → F × (fderiv ℝ f a).ker) = ψmap f a := rfl

lemma mem_smoothChart_source (hf : ContDiff ℝ ∞ f) (hg : (fderiv ℝ f a).range = ⊤) :
    a ∈ (smoothChart hf hg).source :=
  ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, mem_invSet_self hg⟩

/-- **The inverse chart is smooth** at every point of its target. -/
lemma contDiffAt_smoothChart_symm (hf : ContDiff ℝ ∞ f) (hg : (fderiv ℝ f a).range = ⊤)
    {y : F × (fderiv ℝ f a).ker} (hy : y ∈ (smoothChart hf hg).target) :
    ContDiffAt ℝ ∞ (smoothChart hf hg).symm y := by
  have hx := (smoothChart hf hg).map_target hy
  obtain ⟨D, hD⟩ := hx.2
  refine (smoothChart hf hg).contDiffAt_symm hy (f₀' := D) ?_ ?_
  · rw [hD]; exact hasFDerivAt_ψmap hf _
  · exact (ψmap_contDiff hf).contDiffAt

end Chart

/-! ### Generic slice charts and the smooth structure (part C) -/

section Slice

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] {f : E → F} {c : F}

open Classical in
/-- Inverse of the generic slice chart (base point off the target). -/
noncomputable def sliceInvG (φ : OpenPartialHomeomorph E (F × K)) (hφ : ∀ x, (φ x).1 = f x)
    {a : E} (hac : f a = c) (w : K) : levelSet f c :=
  if h : (c, w) ∈ φ.target then
    ⟨φ.symm (c, w), by show f _ = c; rw [← hφ, φ.right_inv h]⟩
  else ⟨a, hac⟩

lemma sliceInvG_val (φ : OpenPartialHomeomorph E (F × K)) (hφ : ∀ x, (φ x).1 = f x)
    {a : E} (hac : f a = c) {w : K} (h : (c, w) ∈ φ.target) :
    (sliceInvG φ hφ hac w : E) = φ.symm (c, w) := by
  classical
  unfold sliceInvG; rw [dite_cond_eq_true (eq_true h)]

lemma sliceG_apply_eq (φ : OpenPartialHomeomorph E (F × K)) (hφ : ∀ x, (φ x).1 = f x)
    (s : levelSet f c) : φ s = (c, (φ s).2) := by
  ext
  · rw [hφ]; exact s.2
  · rfl

/-- **Generic slice chart**: for any local homeomorphism `φ` with first component `f`. -/
noncomputable def sliceG (φ : OpenPartialHomeomorph E (F × K)) (hφ : ∀ x, (φ x).1 = f x)
    {a : E} (hac : f a = c) : OpenPartialHomeomorph (levelSet f c) K where
  toFun s := (φ s).2
  invFun := sliceInvG φ hφ hac
  source := {s | (s : E) ∈ φ.source}
  target := {w | (c, w) ∈ φ.target}
  map_source' s hs := by
    show (c, (φ s).2) ∈ φ.target
    rw [← sliceG_apply_eq φ hφ]; exact φ.map_source hs
  map_target' w hw := by
    show (sliceInvG φ hφ hac w : E) ∈ φ.source
    rw [sliceInvG_val φ hφ hac hw]; exact φ.map_target hw
  left_inv' s hs := by
    have ht : (c, (φ s).2) ∈ φ.target := by rw [← sliceG_apply_eq φ hφ]; exact φ.map_source hs
    apply Subtype.ext
    show (sliceInvG φ hφ hac _ : E) = s
    rw [sliceInvG_val φ hφ hac ht, ← sliceG_apply_eq φ hφ, φ.left_inv hs]
  right_inv' w hw := by
    show (φ (sliceInvG φ hφ hac w : E)).2 = w
    rw [sliceInvG_val φ hφ hac hw, φ.right_inv hw]
  open_source := φ.open_source.preimage continuous_subtype_val
  open_target := φ.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn (φ.continuousOn.comp continuous_subtype_val.continuousOn fun _ hs => hs)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun w : K => φ.symm (c, w)) {w | (c, w) ∈ φ.target} :=
      φ.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hw => hw
    exact hc.congr fun w hw => sliceInvG_val φ hφ hac hw

end Slice

section Smooth

variable {f : E → F} {c : F}

/-- Smooth submersion hypothesis on a level set: `f` is `C^∞` on all of `E`, and `f′(x)` is
surjective at every `x` with `f x = c`. -/
structure SmoothSubmersive (f : E → F) (c : F) : Prop where
  smooth : ContDiff ℝ ∞ f
  surj : ∀ x, f x = c → (fderiv ℝ f x).range = ⊤

/-- The smooth model-valued chart at `a ∈ f⁻¹{c}`. -/
noncomputable def smoothLevelChart (h : SmoothSubmersive f c) (a : levelSet f c) :
    OpenPartialHomeomorph (levelSet f c) (Fin (fibreDim E F) → ℝ) :=
  (sliceG (smoothChart (a := (a : E)) h.smooth (h.surj a a.2)) (fun _ => rfl) a.2).trans
    (kerEquiv (h.surj a a.2)).toHomeomorph.toOpenPartialHomeomorph

/-- **Smooth charted structure** on a regular level set (`isManifold_level`). Its charts differ from
L1's `levelChartedSpace`; use this one for the smooth structure. -/
@[instance_reducible] noncomputable def smoothLevelCharted (h : SmoothSubmersive f c) :
    ChartedSpace (Fin (fibreDim E F) → ℝ) (levelSet f c) where
  atlas := Set.range (smoothLevelChart h)
  chartAt := smoothLevelChart h
  mem_chart_source a := by
    rw [smoothLevelChart, OpenPartialHomeomorph.trans_source]
    exact ⟨mem_smoothChart_source h.smooth (h.surj a a.2), Set.mem_univ _⟩
  chart_mem_atlas a := ⟨a, rfl⟩

end Smooth

section Manifold

open scoped Manifold ContDiff

variable {f : E → F} {c : F}

lemma smoothLevelChart_apply (h : SmoothSubmersive f c) (a s : levelSet f c) :
    smoothLevelChart h a s = kerEquiv (h.surj a a.2) (kerProj (fderiv ℝ f a) ((s : E) - a)) := rfl

lemma mem_smoothChart_target_of (h : SmoothSubmersive f c) (a : levelSet f c)
    {v : Fin (fibreDim E F) → ℝ} (hv : v ∈ (smoothLevelChart h a).target) :
    (c, (kerEquiv (h.surj a a.2)).symm v) ∈ (smoothChart (a := (a : E)) h.smooth (h.surj a a.2)).target := by
  rw [smoothLevelChart, OpenPartialHomeomorph.trans_target] at hv
  exact hv.2

lemma smoothLevelChart_symm_val (h : SmoothSubmersive f c) (a : levelSet f c)
    {v : Fin (fibreDim E F) → ℝ} (hv : v ∈ (smoothLevelChart h a).target) :
    (((smoothLevelChart h a).symm v : levelSet f c) : E) =
      (smoothChart (a := (a : E)) h.smooth (h.surj a a.2)).symm (c, (kerEquiv (h.surj a a.2)).symm v) := by
  exact sliceInvG_val (f := f) _ (fun _ => rfl) a.2 (mem_smoothChart_target_of h a hv)

/-- **Regular level sets of smooth maps are smooth manifolds.** -/
theorem isManifold_level (h : SmoothSubmersive f c) :
    letI := smoothLevelCharted h
    IsManifold 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ (levelSet f c) := by
  let _ := smoothLevelCharted h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ]
  set Ka := kerEquiv (h.surj a a.2)
  set Kb := kerEquiv (h.surj b b.2)
  set φa := smoothChart (a := (a : E)) h.smooth (h.surj a a.2)
  set φb := smoothChart (a := (b : E)) h.smooth (h.surj b b.2)
  let G : (Fin (fibreDim E F) → ℝ) → (Fin (fibreDim E F) → ℝ) :=
    fun v => Kb ((ψmap f (b : E) (φa.symm (c, Ka.symm v))).2)
  intro v hv
  have hvt : v ∈ (smoothLevelChart h a).target := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hv; exact hv.1
  have hG : ContDiffAt ℝ ∞ G v := by
    have h1 : ContDiffAt ℝ ∞ (fun v => (c, Ka.symm v)) v :=
      (contDiff_const.prodMk Ka.symm.contDiff).contDiffAt
    have h2 := (contDiffAt_smoothChart_symm h.smooth (h.surj a a.2) (mem_smoothChart_target_of h a hvt)).comp v h1
    have h3 := (ψmap_contDiff (a := (b : E)) h.smooth).contDiffAt.comp v h2
    exact Kb.contDiff.contDiffAt.comp v (contDiff_snd.contDiffAt.comp v h3)
  refine hG.contDiffWithinAt.congr (fun w hw => ?_) ?_
  · have hwt : w ∈ (smoothLevelChart h a).target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw; exact hw.1
    show Kb ((φb ((smoothLevelChart h a).symm w : E)).2) = G w
    rw [smoothLevelChart_symm_val h a hwt]; rfl
  · show Kb ((φb ((smoothLevelChart h a).symm v : E)).2) = G v
    rw [smoothLevelChart_symm_val h a hvt]; rfl

end Manifold

end GU.Library
