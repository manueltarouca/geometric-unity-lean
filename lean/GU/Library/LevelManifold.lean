import GU.Library.LevelSet

/-!
# Track 3, L2: explicit submersion charts with smooth inverses (part A)

For `f : E → F` (finite-dimensional real spaces) with surjective derivative `g = f'(a)`, fix a
continuous projection `Q : E →L ker g` (`kerProj`), and set `ψ x = (f x, Q (x − a))`. Its derivative
at `a` is the isomorphism `(g, Q) : E ≃L F × ker g` (`derivEquiv`), so the inverse function theorem
gives a local homeomorphism whose first component is exactly `f`.
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

end GU.Library
