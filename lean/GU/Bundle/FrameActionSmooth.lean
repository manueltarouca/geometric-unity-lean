import GU.Bundle.FrameAction

/-!
# The right action of matrices on `HomTotM` is smooth

In a total-space chart, `ractM` is `(e, h) ↦ (e, h ∘ g)` (`chart_ractM`): trivialisations act on
frames by post-composition (`triv_apply`), which commutes with pre-composition by `g`. Hence the
action map `HomTotM × Mat 14 → HomTotM` is `C^∞` (`contMDiff_ractM`), via chart transitions of
`HomTotM`.
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

-- Proved on the plain product type and transported by `show`: this avoids the `ModelProd`
-- topology diamond that blocks continuous linear maps out of `HomModel`.
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

end GU.Library
