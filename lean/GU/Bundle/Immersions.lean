import GU.Bundle.AdaptedPrincipal

/-!
# Phase 4, item 3: the block homomorphism and the sub-bundle inclusion are immersions

Here "immersion" means smooth with injective `mfderiv` at every point (cf. Mathlib's
`IsDiffImmersionAt`; Mathlib's chart-normal-form `IsImmersion` is not claimed, nor is a topological
embedding). A map `f` with `r ∘ f = (chart at a)` near `a` for some differentiable `r` has injective derivative
at `a` (`injective_mfderiv_of_chart_factor`): the derivative of a chart is invertible. Charts of
level sets are affine functions of the ambient chart (`smoothLevelChart_apply`, `regChart_apply`),
which supplies `r`.
* **`injective_mfderiv_ιB`**: `ιB : O(6,4) × O(1,3) → O(7,7)`.
* **`injective_mfderiv_frameA`**, **`injective_mfderiv_inclA`**: `AFrM → HomTotM`, `AFrM → OFr`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor TopologicalSpace
open scoped ContDiff Manifold Topology

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace N] [ChartedSpace H' N] {J : ModelWithCorners ℝ E' H'}
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace N'] [ChartedSpace H'' N'] {K : ModelWithCorners ℝ E'' H''}

/-- If `r ∘ f` is the chart at `a` near `a`, the derivative of `f` at `a` is injective. -/
theorem injective_mfderiv_of_chart_factor {f : M → N} {a : M} (hf : MDifferentiableAt I J f a)
    {r : N → E} (hr : MDifferentiableAt J 𝓘(ℝ, E) r (f a))
    (h : r ∘ f =ᶠ[𝓝 a] extChartAt I a) : Function.Injective (mfderiv I J f a) := by
  have hinv := isInvertible_mfderiv_extChartAt (I := I) (x := a) (y := a) (mem_extChartAt_source a)
  have hc := mfderiv_comp (I := I) (I' := J) (I'' := 𝓘(ℝ, E)) a hr hf
  have hi : Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I a) a) := by
    obtain ⟨e, he⟩ := hinv
    rw [← he]; exact e.injective
  have hi2 : Function.Injective (mfderiv I 𝓘(ℝ, E) (r ∘ f) a) := by
    rw [h.mfderiv_eq]
    exact fun x y hxy => hi ((tangentSpaceCast 𝓘(ℝ, E) _ _).injective hxy)
  rw [hc] at hi2
  exact Function.Injective.of_comp (f := mfderiv J 𝓘(ℝ, E) r (f a)) hi2

/-- If `g ∘ f` has injective derivative, so does `f`. -/
theorem injective_mfderiv_of_comp {f : M → N} {g : N → N'} {a : M}
    (hf : MDifferentiableAt I J f a) (hg : MDifferentiableAt J K g (f a))
    (h : Function.Injective (mfderiv I K (g ∘ f) a)) : Function.Injective (mfderiv I J f a) := by
  rw [mfderiv_comp (I := I) (I' := J) (I'' := K) a hg hf] at h
  exact Function.Injective.of_comp (f := mfderiv J K g (f a)) h

end General

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### The frame inclusion -/

/-- **`AFrM → HomTotM` is an immersion.** -/
theorem injective_mfderiv_frameA (p : AFrM X) :
    Function.Injective (mfderiv IA 𝓘(ℝ, HomModel) (frameA (X := X)) p) := by
  set a : ΩO X := (p : ΩO X)
  set c := chartAt HomModel (a : HomTotM X)
  let L := fun w : HomModel => kerEquiv ((gch_sub (fA_regular (X := X)) a).surj _ (basePt HomModel p).2)
    (kerProj (fderiv ℝ (gch (E := HomModel) (fA (X := X)) cA a) (basePt HomModel p))
      (w - chartAt HomModel a a))
  have hL : ContDiff ℝ ∞ L :=
    (kerEquiv ((gch_sub (fA_regular (X := X)) a).surj _ (basePt HomModel p).2)).contDiff.comp
      ((kerProj (fderiv ℝ (gch (E := HomModel) (fA (X := X)) cA a) (basePt HomModel p))).contDiff.comp
        (contDiff_id.sub contDiff_const))
  have hfA : ContMDiff IA 𝓘(ℝ, HomModel) ∞ (frameA (X := X)) := contMDiff_frameA
  refine injective_mfderiv_of_chart_factor (r := fun q => L (c q))
    (hfA.mdifferentiableAt (by simp)) ?_ ?_
  · have hc0 : ContMDiffAt 𝓘(ℝ, HomModel) 𝓘(ℝ, HomModel) ∞ c (frameA p) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _)
        (mem_chart_source HomModel (frameA p))
    have hc : MDifferentiableAt 𝓘(ℝ, HomModel) 𝓘(ℝ, HomModel) c (frameA p) :=
      hc0.mdifferentiableAt (by simp)
    have hLm : ContMDiff 𝓘(ℝ, HomModel) 𝓘(ℝ, Fin (fibreDim HomModel FA) → ℝ) ∞ L := hL.contMDiff
    exact (hLm.mdifferentiableAt (by simp)).comp _ hc
  · have hs : ((Subtype.val : AFrM X → ΩO X) ⁻¹' (chartAt HomModel a).source) ∈ 𝓝 p :=
      ((chartAt HomModel a).open_source.preimage continuous_subtype_val).mem_nhds
        (mem_chart_source HomModel a)
    refine Filter.eventually_of_mem hs fun s hsrc => ?_
    show L (c (frameA s)) = extChartAt IA p s
    exact (regChart_apply fA_regular p s hsrc).symm

/-- **`AFrM → OFr` is an immersion.** -/
theorem injective_mfderiv_inclA (p : AFrM X) :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    Function.Injective (mfderiv IA 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) (inclA (X := X)) p) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  have hi : ContMDiff IA 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ (inclA (X := X)) :=
    contMDiff_inclA
  have hv : ContMDiff 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) 𝓘(ℝ, HomModel) ∞
      (Subtype.val : OFr X → HomTotM X) := contMDiff_regularLevel_val (Fframe_regular (X := X))
  exact injective_mfderiv_of_comp (K := 𝓘(ℝ, HomModel)) (g := Subtype.val)
    (hi.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp)) (injective_mfderiv_frameA p)

/-! ### The block homomorphism -/

/-- **`ιB : O(6,4) × O(1,3) → O(7,7)` is an immersion.** -/
theorem injective_mfderiv_ιB (g : Gp) :
    Function.Injective (mfderiv IGp 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) (ιB : Gp → O77) g) := by
  have hιc : ContMDiff IGp 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ (ιB : Gp → O77) := contMDiff_ιB
  have hv : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Mat 14) ∞
      (Subtype.val : O77 → Mat 14) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
  let h1 := orth_submersive η64 (ηSig_mem 6 4) (ηSig_sq 6 4)
  let h2 := orth_submersive η13 (ηSig_mem 1 3) (ηSig_sq 1 3)
  let L1 : Mat 10 → Fin (fibreDim (Mat 10) (symS 10)) → ℝ := fun w =>
    kerEquiv (h1.surj g.1 g.1.2) (kerProj (fderiv ℝ (orthF η64) (g.1 : Mat 10)) (w - (g.1 : Mat 10)))
  let L2 : Mat 4 → Fin (fibreDim (Mat 4) (symS 4)) → ℝ := fun w =>
    kerEquiv (h2.surj g.2 g.2.2) (kerProj (fderiv ℝ (orthF η13) (g.2 : Mat 4)) (w - (g.2 : Mat 4)))
  have hL1 : ContDiff ℝ ∞ L1 := (kerEquiv (h1.surj g.1 g.1.2)).contDiff.comp
    ((kerProj (fderiv ℝ (orthF η64) (g.1 : Mat 10))).contDiff.comp (contDiff_id.sub contDiff_const))
  have hL2 : ContDiff ℝ ∞ L2 := (kerEquiv (h2.surj g.2 g.2.2)).contDiff.comp
    ((kerProj (fderiv ℝ (orthF η13) (g.2 : Mat 4))).contDiff.comp (contDiff_id.sub contDiff_const))
  let ex1 : Mat 14 → Mat 10 := fun z a b => z (vI a) (vI b)
  let ex2 : Mat 14 → Mat 4 := fun z a b => z (hI a) (hI b)
  have hex1 : ContDiff ℝ ∞ ex1 := contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
    contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (vI a) (vI b)
  have hex2 : ContDiff ℝ ∞ ex2 := contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
    contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (hI a) (hI b)
  let R : Mat 14 → (Fin (fibreDim (Mat 10) (symS 10)) → ℝ) × (Fin (fibreDim (Mat 4) (symS 4)) → ℝ) :=
    fun z => (L1 (ex1 z), L2 (ex2 z))
  have hR : ContDiff ℝ ∞ R := (hL1.comp hex1).prodMk (hL2.comp hex2)
  have hRm : ContMDiff 𝓘(ℝ, Mat 14) 𝓘(ℝ, (Fin (fibreDim (Mat 10) (symS 10)) → ℝ) ×
      (Fin (fibreDim (Mat 4) (symS 4)) → ℝ)) ∞ R := hR.contMDiff
  refine injective_mfderiv_of_chart_factor (r := fun z : O77 => R (z : Mat 14))
    (hιc.mdifferentiableAt (by simp)) ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact ((hRm.comp hv).mdifferentiableAt (by simp))
  · have e1 : ex1 (ιB s : O77) = (s.1 : Mat 10) := by
      funext a b; exact blkM_vv _ _ a b
    have e2 : ex2 (ιB s : O77) = (s.2 : Mat 4) := by
      funext a b; exact blkM_hh _ _ a b
    show (L1 (ex1 (ιB s : O77)), L2 (ex2 (ιB s : O77))) = extChartAt IGp g s
    rw [e1, e2, extChartAt_prod]
    rfl

end

end GU.Library
