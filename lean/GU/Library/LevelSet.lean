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

open Classical in
/-- Inverse of the slice chart (the base point `a` off the target). -/
noncomputable def sliceInv (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (w : f'.ker) :
    levelSet f (f a) :=
  if h : (f a, w) ∈ (φImp hf hf').target then ⟨(φImp hf hf').symm (f a, w), f_symm hf hf' h⟩
  else ⟨a, mem_levelSet_self f a⟩

lemma sliceInv_val (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {w : f'.ker}
    (h : (f a, w) ∈ (φImp hf hf').target) :
    (sliceInv hf hf' w : E) = (φImp hf hf').symm (f a, w) := by
  classical
  unfold sliceInv; rw [dif_pos h]

lemma φImp_level (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (s : levelSet f (f a)) :
    φImp hf hf' s = (f a, (φImp hf hf' s).2) := by
  ext
  · rw [φImp_fst]; exact s.2
  · rfl

/-- **Slice chart** on the level set `S = f⁻¹{f a}`. -/
noncomputable def sliceChart (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    OpenPartialHomeomorph (levelSet f (f a)) f'.ker where
  toFun s := (φImp hf hf' s).2
  invFun := sliceInv hf hf'
  source := {s | (s : E) ∈ (φImp hf hf').source}
  target := {w | (f a, w) ∈ (φImp hf hf').target}
  map_source' s hs := by
    show (f a, (φImp hf hf' s).2) ∈ (φImp hf hf').target
    rw [← φImp_level]; exact (φImp hf hf').map_source hs
  map_target' w hw := by
    show (sliceInv hf hf' w : E) ∈ (φImp hf hf').source
    rw [sliceInv_val hf hf' hw]; exact (φImp hf hf').map_target hw
  left_inv' s hs := by
    have ht : (f a, (φImp hf hf' s).2) ∈ (φImp hf hf').target := by
      rw [← φImp_level]; exact (φImp hf hf').map_source hs
    apply Subtype.ext
    show (sliceInv hf hf' _ : E) = s
    rw [sliceInv_val hf hf' ht, ← φImp_level, (φImp hf hf').left_inv hs]
  right_inv' w hw := by
    show (φImp hf hf' (sliceInv hf hf' w : E)).2 = w
    rw [sliceInv_val hf hf' hw, (φImp hf hf').right_inv hw]
  open_source := (φImp hf hf').open_source.preimage continuous_subtype_val
  open_target := (φImp hf hf').open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn
      ((φImp hf hf').continuousOn.comp continuous_subtype_val.continuousOn fun _ hs => hs)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun w : f'.ker => (φImp hf hf').symm (f a, w))
        {w | (f a, w) ∈ (φImp hf hf').target} :=
      (φImp hf hf').continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
        fun _ hw => hw
    exact hc.congr fun w hw => sliceInv_val hf hf' hw

lemma mem_sliceChart_source (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    (⟨a, mem_levelSet_self f a⟩ : levelSet f (f a)) ∈ (sliceChart hf hf').source :=
  HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source hf hf'

end GU.Library
