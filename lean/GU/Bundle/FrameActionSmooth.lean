import GU.Bundle.FrameAction

/-!
# The right action of matrices on `HomTotM` is smooth

In a total-space chart, `ractM` is `(e, h) ↦ (e, h ∘ g)` (`chart_ractM`): trivialisations act on
frames by post-composition (`triv_apply`), which commutes with pre-composition by `g`. Hence the
action map `HomTotM × Mat 14 → HomTotM` is `C^∞` (`contMDiff_ractM_joint`); in particular right
translations (`contMDiff_ractM_right`) and orbit maps (`contMDiff_ractM_orbit`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

lemma triv_ractM (y : Yobs X) (q : HomTotM X)
    (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) (g : Mat 14) :
    ((trivializationAt HomF (HomCb (X := X)) y) (ractM q g)).2 =
      (((trivializationAt HomF (HomCb (X := X)) y) q).2).comp (matCLM g) := by
  rw [triv_apply y (ractM q g) hq, triv_apply y q hq]
  rfl

lemma ractM_mem_source (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) (g : Mat 14) :
    ractM q g ∈ (chartAt HomModel a).source := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hq ⊢
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    OpenPartialHomeomorph.prod_source, Set.mem_prod, OpenPartialHomeomorph.refl_source,
    Set.mem_univ, and_true] at hq ⊢
  have hs : ractM q g ∈ (trivializationAt HomF (HomCb (X := X)) a.proj).source := by
    rw [Trivialization.mem_source] at hq ⊢; exact hq.1
  refine ⟨hs, ?_⟩
  rw [Trivialization.coe_coe, Trivialization.coe_fst _ hs]
  have := hq.2
  rwa [Trivialization.coe_coe, Trivialization.coe_fst _ hq.1] at this

/-- **`ractM` in charts**: `chart (q · g) = ((chart q).1, (chart q).2 ∘ g)`. -/
lemma chart_ractM (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) (g : Mat 14) :
    chartAt HomModel a (ractM q g) =
      ((chartAt HomModel a q).1, ((chartAt HomModel a q).2).comp (matCLM g)) := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hq ⊢
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff] at hq
  have hb : q.proj ∈ (trivializationAt CFib (Cb (X := X)) a.proj).baseSet :=
    ((Trivialization.mem_source _).mp hq.1).2
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have hs : ractM q g ∈ (trivializationAt HomF (HomCb (X := X)) a.proj).source := by
    rw [Trivialization.mem_source] at hq ⊢; exact hq.1
  refine Prod.ext ?_ ?_
  · show chartAt _ a.proj ((trivializationAt HomF (HomCb (X := X)) a.proj) (ractM q g)).1 =
      chartAt _ a.proj ((trivializationAt HomF (HomCb (X := X)) a.proj) q).1
    rw [Trivialization.coe_fst _ hs, Trivialization.coe_fst _ hq.1]; rfl
  · show ((trivializationAt HomF (HomCb (X := X)) a.proj) (ractM q g)).2 =
      ((trivializationAt HomF (HomCb (X := X)) a.proj) q).2.comp (matCLM g)
    rw [triv_ractM a.proj q hb g]

/-- `matCLM` as a continuous linear map. -/
noncomputable def matL : Mat 14 →L[ℝ] (R14 →L[ℝ] R14) :=
  LinearMap.toContinuousLinearMap
    { toFun := matCLM
      map_add' := fun g g' => ContinuousLinearMap.ext fun x => by
        simp only [matCLM_apply, ContinuousLinearMap.add_apply]
        show (Matrix.of g + Matrix.of g') *ᵥ x = _
        rw [add_mulVec]
      map_smul' := fun r g => ContinuousLinearMap.ext fun x => by
        simp only [matCLM_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        show (r • Matrix.of g) *ᵥ x = _
        rw [smul_mulVec] }

lemma matL_apply (g : Mat 14) : matL g = matCLM g := rfl

/-- The chart-level right translation `p ↦ (p.1, p.2 ∘ g)`. -/
noncomputable def ψR (g : Mat 14) (p : HomModel) : HomModel := (p.1, p.2.comp (matCLM g))

-- Proved on the plain product type and transported by `show`: `ModelProd` is a `def`, so `p.1`
-- for `p : HomModel` has no normed instance and the `Prod` lemmas do not unify directly.
lemma contMDiff_ψR (g : Mat 14) : ContMDiff 𝓘(ℝ, HomModel) 𝓘(ℝ, HomModel) ∞ (ψR g) := by
  have h : ContDiff ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => (p.1, p.2.comp (matCLM g))) :=
    contDiff_fst.prodMk (contDiff_snd.clm_comp contDiff_const)
  exact (show ContDiff ℝ ∞ (ψR g) from h).contMDiff

/-- **Right translations are smooth**: `q ↦ q · g` is `C^∞` on `HomTotM`. -/
theorem contMDiff_ractM_right (g : Mat 14) :
    ContMDiff 𝓘(ℝ, HomModel) 𝓘(ℝ, HomModel) ∞ (fun q : HomTotM X => ractM q g) := by
  intro q0
  set c := chartAt HomModel q0
  have hloc : ContMDiffOn 𝓘(ℝ, HomModel) 𝓘(ℝ, HomModel) ∞
      (fun q => c.symm (ψR g (c q))) c.source := by
    refine (contMDiffOn_chart_symm (x := q0)).comp ((contMDiff_ψR g).comp_contMDiffOn
      (contMDiffOn_chart (x := q0))) ?_
    intro q hq
    show ψR g (c q) ∈ c.target
    have := c.map_source (ractM_mem_source q0 q hq g)
    rwa [chart_ractM q0 q hq g] at this
  refine (hloc.contMDiffAt (c.open_source.mem_nhds (mem_chart_source _ q0))).congr_of_eventuallyEq ?_
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ q0)] with q hq
  show ractM q g = c.symm (ψR g (c q))
  rw [show ψR g (c q) = c (ractM q g) from (chart_ractM q0 q hq g).symm,
    c.left_inv (ractM_mem_source q0 q hq g)]

/-- **Orbit maps are smooth**: `g ↦ q · g` is `C^∞` from `Mat 14` to `HomTotM`. -/
theorem contMDiff_ractM_orbit (q : HomTotM X) :
    ContMDiff 𝓘(ℝ, Mat 14) 𝓘(ℝ, HomModel) ∞ (fun g : Mat 14 => ractM q g) := by
  set c := chartAt HomModel q
  set p := c q
  have hψ : ContMDiff 𝓘(ℝ, Mat 14) 𝓘(ℝ, HomModel) ∞ (fun g : Mat 14 => (ψR g p : HomModel)) := by
    have h : ContDiff ℝ ∞ (fun g : Mat 14 =>
        (((p.1 : (Fin 4 → ℝ) × (Fin 10 → ℝ)), (p.2 : HomF).comp (matL g)) :
          ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF)) :=
      contDiff_const.prodMk (contDiff_const.clm_comp matL.contDiff)
    exact (show ContDiff ℝ ∞ (fun g : Mat 14 => (ψR g p : HomModel)) from h).contMDiff
  have hq : q ∈ c.source := mem_chart_source _ q
  have htgt : ∀ g, ψR g p ∈ c.target := fun g => by
    have := c.map_source (ractM_mem_source q q hq g)
    rwa [chart_ractM q q hq g] at this
  have hsym : ContMDiff 𝓘(ℝ, Mat 14) 𝓘(ℝ, HomModel) ∞ (fun g : Mat 14 => c.symm (ψR g p)) :=
    fun g => (contMDiffOn_chart_symm (x := q)).contMDiffAt
      (c.open_target.mem_nhds (htgt g)) |>.comp g (hψ g)
  refine hsym.congr fun g => ?_
  show ractM q g = c.symm (ψR g p)
  rw [show ψR g p = c (ractM q g) from (chart_ractM q q hq g).symm,
    c.left_inv (ractM_mem_source q q hq g)]

/-- The chart-level joint action `(p, g) ↦ (p.1, p.2 ∘ g)`. -/
noncomputable def ΨJ (pg : HomModel × Mat 14) : HomModel := (pg.1.1, pg.1.2.comp (matCLM pg.2))

lemma contMDiff_ΨJ : ContMDiff (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) 𝓘(ℝ, HomModel) ∞ ΨJ := by
  have h : ContDiff ℝ ∞ (fun pg : (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) × Mat 14 =>
      ((pg.1.1, pg.1.2.comp (matL pg.2)) : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).clm_comp (matL.contDiff.comp contDiff_snd))
  have h' : ContMDiff 𝓘(ℝ, HomModel × Mat 14) 𝓘(ℝ, HomModel) ∞ ΨJ :=
    (show ContDiff ℝ ∞ ΨJ from h).contMDiff
  have hid : ContMDiff (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) 𝓘(ℝ, HomModel × Mat 14) ∞
      (fun pg : HomModel × Mat 14 => (pg.1, pg.2)) :=
    contMDiff_fst.prodMk_space contMDiff_snd
  exact h'.comp hid

/-- **The action map `HomTotM × Mat 14 → HomTotM` is jointly smooth.** -/
theorem contMDiff_ractM_joint :
    ContMDiff (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) 𝓘(ℝ, HomModel) ∞
      (fun qg : HomTotM X × Mat 14 => ractM qg.1 qg.2) := by
  intro qg0
  set c := chartAt HomModel qg0.1
  have hs : c.source ×ˢ (Set.univ : Set (Mat 14)) ∈ nhds qg0 :=
    (c.open_source.prod isOpen_univ).mem_nhds ⟨mem_chart_source _ _, Set.mem_univ _⟩
  have hloc : ContMDiffOn (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) 𝓘(ℝ, HomModel) ∞
      (fun qg : HomTotM X × Mat 14 => c.symm (ΨJ (c qg.1, qg.2))) (c.source ×ˢ Set.univ) := by
    have h1 : ContMDiffOn (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) (𝓘(ℝ, HomModel).prod 𝓘(ℝ, Mat 14)) ∞
        (fun qg : HomTotM X × Mat 14 => (c qg.1, qg.2)) (c.source ×ˢ Set.univ) :=
      ((contMDiffOn_chart (x := qg0.1)).comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd
    refine (contMDiffOn_chart_symm (x := qg0.1)).comp (contMDiff_ΨJ.comp_contMDiffOn h1) ?_
    rintro ⟨q, g⟩ ⟨hq, -⟩
    show ΨJ (c q, g) ∈ c.target
    have := c.map_source (ractM_mem_source qg0.1 q hq g)
    rwa [chart_ractM qg0.1 q hq g] at this
  refine (hloc.contMDiffAt hs).congr_of_eventuallyEq ?_
  filter_upwards [hs] with qg hqg
  show ractM qg.1 qg.2 = c.symm (ΨJ (c qg.1, qg.2))
  rw [show ΨJ (c qg.1, qg.2) = c (ractM qg.1 qg.2) from (chart_ractM qg0.1 qg.1 hqg.1 qg.2).symm,
    c.left_inv (ractM_mem_source qg0.1 qg.1 hqg.1 qg.2)]

/-! ### The action on the orthonormal frame submanifold -/

/-- The frame submanifold `Fframe⁻¹{η₇₇}` (`= orthoSetM`). -/
abbrev OFr (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :=
  levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩

lemma ractM_mem_OFr {q : HomTotM X} (hq : q ∈ OFr X) (g : O77) : ractM q g ∈ OFr X := by
  rw [OFr, levelSet_Fframe] at hq ⊢
  exact ractM_mem hq g

/-- The right `O(7,7)`-action on orthonormal frames. -/
noncomputable def actOFr (qg : OFr X × O77) : OFr X :=
  ⟨ractM qg.1 qg.2, ractM_mem_OFr qg.1.2 qg.2⟩

/-- **The `O(7,7)`-action on the orthonormal frame bundle is smooth** (for the regular-level-set
manifold structure on the frames and the Lie group structure on `O77`). -/
theorem contMDiff_actOFr :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ContMDiff (𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ).prod
        𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ))
      𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ (actOFr (X := X)) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  rw [contMDiff_regularLevel_iff]
  have hv := contMDiff_regularLevel_val (Fframe_regular (X := X))
  have hO : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Mat 14) ∞
      (Subtype.val : O77 → Mat 14) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
  exact contMDiff_ractM_joint.comp ((hv.comp contMDiff_fst).prodMk (hO.comp contMDiff_snd))

end GU.Library
