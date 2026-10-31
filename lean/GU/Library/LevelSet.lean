import Mathlib

/-!
# Level sets of submersions: slice charts (Track 3, L1)

For `f : E → F` between finite-dimensional real normed spaces, strictly differentiable at a point `a`
with surjective derivative, Mathlib's `implicitToOpenPartialHomeomorph` gives a local homeomorphism
`φ : E ⊃ U → F × ker f'` with `(φ x).1 = f x`. On the level set `S = f⁻¹{c}` (with `c = f a`),
`s ↦ (φ s).2` is a **slice chart** `S ⊃ S ∩ U → ker f'` (`sliceChart`): an open partial
homeomorphism from the subtype `S` onto an open subset of `ker f'`.

This is the local building block for giving `S` a manifold structure (L2: a fixed model space, smooth
transition maps).
-/

namespace GU.Library

open Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {f' : E →L[ℝ] F} {a : E}

/-- The implicit-function chart at `a`. -/
noncomputable abbrev φImp (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  hf.implicitToOpenPartialHomeomorph f f' hf'

/-- The level set through `a`. -/
def levelSet (f : E → F) (c : F) : Set E := {x | f x = c}

lemma φImp_fst (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (x : E) :
    (φImp hf hf' x).1 = f x := HasStrictFDerivAt.implicitToOpenPartialHomeomorph_fst hf hf' x

/-- `f (φ⁻¹ (c, w)) = c` on the chart target. -/
lemma f_symm (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {p : F × f'.ker}
    (hp : p ∈ (φImp hf hf').target) : f ((φImp hf hf').symm p) = p.1 := by
  rw [← φImp_fst hf hf', (φImp hf hf').right_inv hp]

lemma mem_levelSet_self (f : E → F) (a : E) : a ∈ levelSet f (f a) := rfl

variable {c : F}

open Classical in
/-- Inverse of the slice chart (the base point `a` off the target). -/
noncomputable def sliceInv (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hac : f a = c)
    (w : f'.ker) : levelSet f c :=
  if h : (c, w) ∈ (φImp hf hf').target then ⟨(φImp hf hf').symm (c, w), f_symm hf hf' h⟩
  else ⟨a, hac⟩

lemma sliceInv_val (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hac : f a = c) {w : f'.ker}
    (h : (c, w) ∈ (φImp hf hf').target) :
    (sliceInv hf hf' hac w : E) = (φImp hf hf').symm (c, w) := by
  classical
  unfold sliceInv; rw [dif_pos h]

lemma φImp_level (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (s : levelSet f c) :
    φImp hf hf' s = (c, (φImp hf hf' s).2) := by
  ext
  · rw [φImp_fst]; exact s.2
  · rfl

/-- **Slice chart** at `a` on the level set `S = f⁻¹{c}` (`f a = c`). -/
noncomputable def sliceChart (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hac : f a = c) :
    OpenPartialHomeomorph (levelSet f c) f'.ker where
  toFun s := (φImp hf hf' s).2
  invFun := sliceInv hf hf' hac
  source := {s | (s : E) ∈ (φImp hf hf').source}
  target := {w | (c, w) ∈ (φImp hf hf').target}
  map_source' s hs := by
    show (c, (φImp hf hf' s).2) ∈ (φImp hf hf').target
    rw [← φImp_level]; exact (φImp hf hf').map_source hs
  map_target' w hw := by
    show (sliceInv hf hf' hac w : E) ∈ (φImp hf hf').source
    rw [sliceInv_val hf hf' hac hw]; exact (φImp hf hf').map_target hw
  left_inv' s hs := by
    have ht : (c, (φImp hf hf' s).2) ∈ (φImp hf hf').target := by
      rw [← φImp_level]; exact (φImp hf hf').map_source hs
    apply Subtype.ext
    show (sliceInv hf hf' hac _ : E) = s
    rw [sliceInv_val hf hf' hac ht, ← φImp_level, (φImp hf hf').left_inv hs]
  right_inv' w hw := by
    show (φImp hf hf' (sliceInv hf hf' hac w : E)).2 = w
    rw [sliceInv_val hf hf' hac hw, (φImp hf hf').right_inv hw]
  open_source := (φImp hf hf').open_source.preimage continuous_subtype_val
  open_target := (φImp hf hf').open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn
      ((φImp hf hf').continuousOn.comp continuous_subtype_val.continuousOn fun _ hs => hs)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun w : f'.ker => (φImp hf hf').symm (c, w))
        {w | (c, w) ∈ (φImp hf hf').target} :=
      (φImp hf hf').continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
        fun _ hw => hw
    exact hc.congr fun w hw => sliceInv_val hf hf' hac hw

lemma mem_sliceChart_source (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hac : f a = c) :
    (⟨a, hac⟩ : levelSet f c) ∈ (sliceChart hf hf' hac).source :=
  HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source hf hf'

/-! ### Fixed model and the charted space -/

section Charted

variable [FiniteDimensional ℝ E]

/-- Submersion hypothesis on a level set: smooth, with surjective derivative at every point. -/
structure SubmersiveAt (f : E → F) (c : F) : Prop where
  strict : ∀ x, f x = c → HasStrictFDerivAt f (fderiv ℝ f x) x
  surj : ∀ x, f x = c → (fderiv ℝ f x).range = ⊤

/-- Fibre dimension `dim E − dim F`. -/
noncomputable def fibreDim (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : ℕ :=
  Module.finrank ℝ E - Module.finrank ℝ F

lemma finrank_ker_eq {g : E →L[ℝ] F} (hg : g.range = ⊤) :
    Module.finrank ℝ g.ker = fibreDim E F := by
  have h := LinearMap.finrank_range_add_finrank_ker (g : E →ₗ[ℝ] F)
  have hr : Module.finrank ℝ (LinearMap.range (g : E →ₗ[ℝ] F)) = Module.finrank ℝ F := by
    rw [show LinearMap.range (g : E →ₗ[ℝ] F) = ⊤ from hg, finrank_top]
  unfold fibreDim; rw [← h, hr]; simp

/-- The kernel identified with the fixed model `Fin k → ℝ`. -/
noncomputable def kerEquiv {g : E →L[ℝ] F} (hg : g.range = ⊤) :
    g.ker ≃L[ℝ] (Fin (fibreDim E F) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_ker_eq hg, Module.finrank_fin_fun])

/-- The model-valued slice chart at a point of the level set. -/
noncomputable def levelChart {c : F} (h : SubmersiveAt f c) (a : levelSet f c) :
    OpenPartialHomeomorph (levelSet f c) (Fin (fibreDim E F) → ℝ) :=
  (sliceChart (h.strict a a.2) (h.surj a a.2) a.2).trans
    (kerEquiv (h.surj a a.2)).toHomeomorph.toOpenPartialHomeomorph

/-- **The level set is a charted space** modelled on `Fin (dim E − dim F) → ℝ`. This is a
topological atlas only; for the smooth structure use `smoothLevelCharted` and `isManifold_level`
(`LevelManifold.lean`), whose charts are different. -/
@[instance_reducible] noncomputable def levelChartedSpace {c : F} (h : SubmersiveAt f c) :
    ChartedSpace (Fin (fibreDim E F) → ℝ) (levelSet f c) where
  atlas := Set.range (levelChart h)
  chartAt := levelChart h
  mem_chart_source a := by
    rw [levelChart, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, by simp⟩
    exact mem_sliceChart_source (h.strict a a.2) (h.surj a a.2) a.2
  chart_mem_atlas a := ⟨a, rfl⟩

end Charted

end GU.Library
