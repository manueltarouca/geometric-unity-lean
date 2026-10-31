import GU.Bundle.FramesCb
import GU.Bundle.OrthoFrames
import GU.Observerse.ChimericCovariance

/-!
# Orthonormal frames of `C` form a closed, chart-invariant subset of `Hom(ℝ¹⁴, C)`

On the smooth frame bundle `FrY ⊆ Hom(ℝ¹⁴, C)` (`SmoothFrames.lean`):

* `continuousAt_Bmod`: the chimeric metric `Bmod G u v` is continuous in `(G, u, v)` where `det G ≠ 0`
  (`G⁻¹` via `continuousAt_matrix_inv`).
* `gX_eq_TP`: the transitions of `C` are the chart transports `TP` of `OrthoFrames.lean`, with
  `Pm a b x` the matrix of the tangent transition.
* `Gi i y`: the metric of `y` in chart `i` coordinates; `Gi_eq` (`= P G Pᵀ`), `Gi_det_neg` (Lorentzian: `det < 0`), `Gi_det_ne`.
* **`mem_orthoSet_iff`**: orthonormality of a frame (`Bmod (Gpt y) (A u) (A w) = Bη u w`, raw
  coordinates) is chart invariant: equivalently it holds in any chart `i` (via `Bmod_covariant`).
* **`isClosed_orthoSet`**: the orthonormal frames form a closed subset of the total space
  `Hom(ℝ¹⁴, C)` (hence of `FrY`: `orthoSet_subset_frameSet` in `OrthoGlue.lean`).
* `ract_ortho`, **`ortho_transitive`**: `Bη`-preserving `g` (the group `O(Bη)`, as a predicate on
  `EndC`; not linked to the subgroup `OG ⊆ GLC` of `OrthoFrames.lean`) preserve orthonormal frames,
  and two orthonormal frames over the same point differ by such a `g` (unique by `ract_unique`).

This is NOT yet a reduction of the structure group over all of `Y`: `Yobs` contains both Lorentzian
components, and at (3,1) points (`Gpt = P(−η)Pᵀ`) `Bmod G` has an orthogonal basis with 9 positive
and 5 negative norms and is not isometric to the (7,7) model, so those fibres of `orthoSet` are empty
(`no_ortho_31`, `NoOrtho31.lean`). This depends on the relative sign `+DeWitt ⊕ +g⁻¹` chosen in
`Chimeric.lean` (with the opposite sign the two Lorentzian components swap roles); that `Yobs` is
exactly the union of the (1,3) and (3,1) points is not formalised. Over (1,3) points orthonormal frames exist
in the smooth total space (`ortho_exists_Y13`, `OrthoGlue.lean`). Not done: the
submanifold structure (needs a regular-value theorem; Mathlib has no submanifolds).
-/

namespace GU.Observerse

open Bundle Manifold Matrix GU.Chimeric
open scoped ContDiff


lemma continuousAt_inv4 {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : G.det ≠ 0) :
    ContinuousAt (fun G : Matrix (Fin 4) (Fin 4) ℝ => G⁻¹) G :=
  continuousAt_matrix_inv G (by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hG)

lemma continuous_covec : Continuous (covec : ((Fin 4 → ℝ) →L[ℝ] ℝ) → Fin 4 → ℝ) :=
  continuous_pi fun i => (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous

/-- `Bmod` with `G⁻¹` replaced by a free variable `H`: a polynomial, hence continuous. -/
lemma continuous_BmodH : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib =>
    trace (r.1 * symMat r.2.2.1.1 * r.1 * symMat r.2.2.2.1) -
      trace (r.1 * symMat r.2.2.1.1) * trace (r.1 * symMat r.2.2.2.1) +
      covec r.2.2.1.2 ⬝ᵥ (r.2.1 *ᵥ covec r.2.2.2.2)) := by
  have hu : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib =>
      symMat r.2.2.1.1) := continuous_symMat.comp (by fun_prop)
  have hv : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib =>
      symMat r.2.2.2.1) := continuous_symMat.comp (by fun_prop)
  have hcu : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib =>
      covec r.2.2.1.2) := continuous_covec.comp (by fun_prop)
  have hcv : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib =>
      covec r.2.2.2.2) := continuous_covec.comp (by fun_prop)
  have h1 : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib => r.1) :=
    continuous_fst
  have h2 : Continuous (fun r : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib => r.2.1) :=
    by fun_prop
  exact ((((h1.matrix_mul hu).matrix_mul h1).matrix_mul hv).matrix_trace.sub
    ((h1.matrix_mul hu).matrix_trace.mul (h1.matrix_mul hv).matrix_trace)).add
    (hcu.dotProduct (h2.matrix_mulVec hcv))

lemma continuousAt_Bmod {q : Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib} (hq : q.1.det ≠ 0) :
    ContinuousAt (fun q : Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib => Bmod q.1 q.2.1 q.2.2) q := by
  have hpair : ContinuousAt (fun q : Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib => (q.1⁻¹, q)) q :=
    ((continuousAt_inv4 hq).comp continuous_fst.continuousAt).prodMk continuousAt_id
  have := continuous_BmodH.continuousAt.comp hpair
  convert this using 1
  funext q
  simp only [Function.comp, Bmod, chimY, Matrix.mul_assoc]

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Transition matrix between charts `a, b` at `x`. -/
noncomputable def Pm (a b : atlas (Fin 4 → ℝ) X) (x : X) : Matrix (Fin 4) (Fin 4) ℝ :=
  mat ((Zt X).coordChange a b x)

lemma toCLM_mat (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : toCLM (mat T) = T := by
  ext v : 1
  simp [toCLM, mat]

lemma Pm_mul (a b : atlas (Fin 4 → ℝ) X) (x : X) (hx : x ∈ (Zt X).baseSet a ∩ (Zt X).baseSet b) :
    Pm b a x * Pm a b x = 1 := by
  have hc : ((Zt X).coordChange b a x).comp ((Zt X).coordChange a b x) = ContinuousLinearMap.id ℝ _ := by
    ext w : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [(Zt X).coordChange_comp a b a x ⟨hx, hx.1⟩ w, (Zt X).coordChange_self a x hx.1 w]
  simp only [Pm, ← mat_comp, hc, mat_id]

lemma Pm_isUnit (a b : atlas (Fin 4 → ℝ) X) (x : X) (hx : x ∈ (Zt X).baseSet a ∩ (Zt X).baseSet b) :
    IsUnit (Pm a b x) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
    (mat_coordChange_det_ne (Zt X) a b x hx))

/-- **The transitions of `C` are the chart transports `TP`.** -/
lemma gX_eq_TP (a b : atlas (Fin 4 → ℝ) X) (x : X) (hx : x ∈ (Zt X).baseSet a ∩ (Zt X).baseSet b)
    (v : CFib) : gX a b x v = TP (Pm a b x) (Pm_isUnit a b x hx) v := by
  have hinv : (Pm a b x)⁻¹ = Pm b a x := Matrix.inv_eq_left_inv (Pm_mul a b x hx)
  refine Prod.ext rfl ?_
  show v.2.comp ((Zt X).coordChange b a x) = v.2.comp (toCLM (Pm a b x)⁻¹)
  rw [hinv, Pm, toCLM_mat]

/-- The metric of `y` in chart `i` coordinates. -/
noncomputable def Gi (i : atlas (Fin 4 → ℝ) X) (y : Yobs X) : Matrix (Fin 4) (Fin 4) ℝ :=
  symMat (((symCore (Zt X)).localTriv i (y : Sym2TX X)).2)

lemma Gi_eq (i : atlas (Fin 4 → ℝ) X) (y : Yobs X) :
    Gi i y = Pm ((Zt X).indexAt (πY y)) i (πY y) * Gpt y * (Pm ((Zt X).indexAt (πY y)) i (πY y))ᵀ := by
  have hs : (Pm ((Zt X).indexAt (πY y)) i (πY y) * Gpt y * (Pm ((Zt X).indexAt (πY y)) i (πY y))ᵀ).IsSymm := by
    have e : (Gpt y)ᵀ = Gpt y := (symMat_isSymm _).eq
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, e, Matrix.mul_assoc]
  rw [Gi, VectorBundleCore.localTriv_apply]
  exact symMat_symCoords _ hs

lemma Gi_det_neg (i : atlas (Fin 4 → ℝ) X) (y : Yobs X) (hy : πY y ∈ (Zt X).baseSet i) :
    (Gi i y).det < 0 := by
  rw [Gi, VectorBundleCore.localTriv_apply]
  have hl : (symMat (y : Sym2TX X).2).det < 0 := y.2
  change (symMat (symAct ((Zt X).coordChange ((Zt X).indexAt (πY y)) i (πY y))
    ((y : Sym2TX X).2 : Fin 10 → ℝ))).det < 0
  have hP := mat_coordChange_det_ne (Zt X) _ i _ ⟨(Zt X).mem_baseSet_at (πY y), hy⟩
  exact (det_symAct _ _).symm ▸ mul_neg_of_pos_of_neg (by positivity) hl

lemma Gi_det_ne (i : atlas (Fin 4 → ℝ) X) (y : Yobs X) (hy : πY y ∈ (Zt X).baseSet i) :
    (Gi i y).det ≠ 0 := by
  rw [Gi, VectorBundleCore.localTriv_apply]
  have hl : (symMat (y : Sym2TX X).2).det < 0 := y.2
  change (symMat (symAct ((Zt X).coordChange ((Zt X).indexAt (πY y)) i (πY y))
    ((y : Sym2TX X).2 : Fin 10 → ℝ))).det ≠ 0
  refine (det_symAct _ _).trans_ne ?_
  have hP := mat_coordChange_det_ne (Zt X) _ i _ ⟨(Zt X).mem_baseSet_at (πY y), hy⟩
  exact mul_ne_zero (pow_ne_zero 2 hP) hl.ne

/-- Orthonormal frames: `A` carries `Bη` to the chimeric metric at `p.proj`. -/
def orthoSet : Set (HomTot X) :=
  {p | ∀ u w, Bmod (Gpt p.proj) ((show EndC from p.2) u) ((show EndC from p.2) w) = Bη u w}

/-- **Chart invariance** of the orthonormality condition. -/
lemma mem_orthoSet_iff (i : atlas (Fin 4 → ℝ) X) (p : HomTot X) (hp : πY p.proj ∈ (Zt X).baseSet i) :
    p ∈ orthoSet (X := X) ↔ ∀ u w, Bmod (Gi i p.proj)
      ((((frameCore (X := X)).localTriv i p).2 : EndC) u)
      ((((frameCore (X := X)).localTriv i p).2 : EndC) w) = Bη u w := by
  have hx : πY p.proj ∈ (Zt X).baseSet ((Zt X).indexAt (πY p.proj)) ∩ (Zt X).baseSet i :=
    ⟨(Zt X).mem_baseSet_at _, hp⟩
  have key : ∀ u w, Bmod (Gi i p.proj) ((((frameCore (X := X)).localTriv i p).2 : EndC) u)
      ((((frameCore (X := X)).localTriv i p).2 : EndC) w) =
      Bmod (Gpt p.proj) ((show EndC from p.2) u) ((show EndC from p.2) w) := by
    intro u w
    rw [VectorBundleCore.localTriv_apply, Gi_eq]
    show Bmod _ (gX ((Zt X).indexAt (πY p.proj)) i _ _) (gX ((Zt X).indexAt (πY p.proj)) i _ _) = _
    rw [gX_eq_TP _ _ _ hx, gX_eq_TP _ _ _ hx]
    exact GU.Bmod_covariant _ _ _ _ _
  simp only [orthoSet, Set.mem_ofPred_eq, key]

lemma continuousOn_Gi (i : atlas (Fin 4 → ℝ) X) :
    ContinuousOn (fun p : HomTot X => Gi i p.proj) {p | πY p.proj ∈ (Zt X).baseSet i} := by
  have ht := ((symCore (Zt X)).localTriv i).continuousOn
  have hy : Continuous (fun p : HomTot X => ((p.proj : Yobs X) : Sym2TX X)) :=
    continuous_subtype_val.comp (FiberBundle.continuous_proj EndC (frameCore (X := X)).Fiber)
  refine continuous_symMat.comp_continuousOn (continuous_snd.comp_continuousOn (ht.comp hy.continuousOn ?_))
  intro p hp
  rw [VectorBundleCore.mem_localTriv_source]
  exact hp

lemma continuousOn_triv_apply (i : atlas (Fin 4 → ℝ) X) (u : CFib) :
    ContinuousOn (fun p : HomTot X => (((frameCore (X := X)).localTriv i p).2 : EndC) u)
      {p | πY p.proj ∈ (Zt X).baseSet i} := by
  have ht := ((frameCore (X := X)).localTriv i).continuousOn
  refine ((ContinuousLinearMap.apply ℝ CFib u).continuous.comp continuous_snd).comp_continuousOn
    (ht.mono ?_)
  intro p hp
  rw [VectorBundleCore.mem_localTriv_source]
  exact hp

/-- **Orthonormal frames form a closed subset** of `Hom(ℝ¹⁴, C)`. -/
theorem isClosed_orthoSet : IsClosed (orthoSet (X := X)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  set i := (Zt X).indexAt (πY p.proj)
  have hpi : πY p.proj ∈ (Zt X).baseSet i := (Zt X).mem_baseSet_at _
  rw [Set.mem_compl_iff, mem_orthoSet_iff i p hpi] at hp
  push Not at hp
  obtain ⟨u, w, huw⟩ := hp
  let S : Set (HomTot X) := {q | πY q.proj ∈ (Zt X).baseSet i}
  have hS : IsOpen S := ((Zt X).isOpen_baseSet i).preimage
    (contMDiff_πY.continuous.comp (FiberBundle.continuous_proj EndC (frameCore (X := X)).Fiber))
  let F : HomTot X → ℝ := fun q => Bmod (Gi i q.proj)
    ((((frameCore (X := X)).localTriv i q).2 : EndC) u) ((((frameCore (X := X)).localTriv i q).2 : EndC) w)
  have hF : ContinuousOn F S := by
    intro q hq
    have hB := continuousAt_Bmod (q := (Gi i q.proj, (((frameCore (X := X)).localTriv i q).2 : EndC) u,
      (((frameCore (X := X)).localTriv i q).2 : EndC) w)) (Gi_det_ne i q.proj hq)
    have hP : ContinuousWithinAt (fun x : HomTot X => (Gi i x.proj,
        (((frameCore (X := X)).localTriv i x).2 : EndC) u, (((frameCore (X := X)).localTriv i x).2 : EndC) w)) S q :=
      ((continuousOn_Gi i) q hq).prodMk (((continuousOn_triv_apply i u) q hq).prodMk
        ((continuousOn_triv_apply i w) q hq))
    have hB' : ContinuousAt (fun r : Matrix (Fin 4) (Fin 4) ℝ × CFib × CFib => Bmod r.1 r.2.1 r.2.2)
        ((fun x : HomTot X => (Gi i x.proj, (((frameCore (X := X)).localTriv i x).2 : EndC) u,
          (((frameCore (X := X)).localTriv i x).2 : EndC) w)) q) := hB
    exact ContinuousAt.comp_continuousWithinAt (x := q) (s := S)
      (f := fun x : HomTot X => (Gi i x.proj, (((frameCore (X := X)).localTriv i x).2 : EndC) u,
          (((frameCore (X := X)).localTriv i x).2 : EndC) w)) hB' hP
  refine ⟨S ∩ F ⁻¹' {Bη u w}ᶜ, ?_, hF.isOpen_inter_preimage hS isOpen_compl_singleton, hpi, huw⟩
  rintro q ⟨hq, hFq⟩ hmem
  exact hFq (((mem_orthoSet_iff i q hq).mp hmem) u w)

/-- `O(Bη)` preserves orthonormal frames. -/
theorem ract_ortho {p : HomTot X} (hp : p ∈ orthoSet (X := X)) (g : EndC)
    (hg : ∀ u v, Bη (g u) (g v) = Bη u v) : ract p g ∈ orthoSet (X := X) := by
  intro u w
  show Bmod (Gpt p.proj) ((show EndC from p.2) (g u)) ((show EndC from p.2) (g w)) = Bη u w
  rw [hp, hg]

/-- **Fibre-transitivity of `O(7,7)`**: two orthonormal frames over the same point differ by a unit
preserving `Bη`. -/
theorem ortho_transitive {p q : HomTot X} (hp : p ∈ frameSet (X := X)) (hq : q ∈ frameSet (X := X))
    (hpo : p ∈ orthoSet (X := X)) (hqo : q ∈ orthoSet (X := X)) (h : p.proj = q.proj) :
    ∃ g : EndCˣ, ract p g = q ∧ ∀ u v, Bη ((g : EndC) u) ((g : EndC) v) = Bη u v := by
  obtain ⟨g, hg⟩ := ract_transitive hp hq h
  refine ⟨g, hg, fun u v => ?_⟩
  subst hg
  rw [← hpo]
  exact hqo u v

end GU.Observerse
