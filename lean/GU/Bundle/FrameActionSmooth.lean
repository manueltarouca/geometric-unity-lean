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

end GU.Library
