import GU.Bundle.CoverSpinAPI

/-!
# Phase 6, item 4: smoothness over `ℝ⁴`

The global frame `Ff` of the chimeric bundle over the cover of `Y13(ℝ⁴)` is smooth (`contMDiff_Ff`), and
`coverSpin` carries a smooth principal `Spin(7,7)`-bundle structure (`smoothCoverSpin`, the product
structure on `Ytilde ℝ⁴ × Spin(7,7)`) whose map to the frames is smooth (`contMDiff_coverSpin_Φ_full`).
No local-diffeomorphism property of `Φ` is claimed (unlike `smoothSpinBundle`).

Smoothness of matrix-valued maps is handled entrywise (`SmoothEntries`): determinants and adjugates by
the Leibniz formula, the inverse of `quat g` by `quat g · (quat g)ᵀ = |g|² 1`, and `gaugeP` by its square
roots on the gauge set.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### Entrywise smoothness on a manifold -/

section Entries

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- A real function on `M` is smooth. -/
abbrev Sm (I : ModelWithCorners ℝ EM HM) (f : M → ℝ) : Prop := ContMDiff I 𝓘(ℝ, ℝ) ∞ f

/-- All entries of a matrix-valued map are smooth. -/
def SmoothEntries (I : ModelWithCorners ℝ EM HM) {n : Type*} (A : M → Matrix n n ℝ) : Prop :=
  ∀ i j, Sm I fun q => A q i j

lemma Sm.add {f g : M → ℝ} (hf : Sm I f) (hg : Sm I g) : Sm I fun q => f q + g q :=
  ContMDiff.add hf hg
lemma Sm.mul {f g : M → ℝ} (hf : Sm I f) (hg : Sm I g) : Sm I fun q => f q * g q :=
  ContMDiff.mul hf hg
lemma Sm.const (c : ℝ) : Sm I fun _ : M => c := contMDiff_const

lemma Sm.sum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ} (hf : ∀ i ∈ s, Sm I (f i)) :
    Sm I fun q => ∑ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sm.const (I := I) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma Sm.prod {ι : Type*} (s : Finset ι) {f : ι → M → ℝ} (hf : ∀ i ∈ s, Sm I (f i)) :
    Sm I fun q => ∏ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sm.const (I := I) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma Sm.inv {f : M → ℝ} (hf : Sm I f) (h0 : ∀ q, f q ≠ 0) : Sm I fun q => (f q)⁻¹ :=
  fun q => (contDiffAt_inv ℝ (h0 q)).contMDiffAt.comp q (hf q)

lemma Sm.div {f g : M → ℝ} (hf : Sm I f) (hg : Sm I g) (h0 : ∀ q, g q ≠ 0) :
    Sm I fun q => f q / g q := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv h0)

lemma Sm.sqrt {f : M → ℝ} (hf : Sm I f) (h0 : ∀ q, 0 < f q) : Sm I fun q => Real.sqrt (f q) :=
  fun q => (Real.contDiffAt_sqrt (h0 q).ne').contMDiffAt.comp q (hf q)

lemma Sm.neg {f : M → ℝ} (hf : Sm I f) : Sm I fun q => -f q := ContMDiff.neg hf

lemma Sm.sub {f g : M → ℝ} (hf : Sm I f) (hg : Sm I g) : Sm I fun q => f q - g q :=
  ContMDiff.sub hf hg

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma SmoothEntries.mul {A B : M → Matrix n n ℝ} (hA : SmoothEntries I A) (hB : SmoothEntries I B) :
    SmoothEntries I fun q => A q * B q := fun i j => by
  simp only [Matrix.mul_apply]
  exact Sm.sum _ fun k _ => (hA i k).mul (hB k j)

lemma SmoothEntries.transpose {A : M → Matrix n n ℝ} (hA : SmoothEntries I A) :
    SmoothEntries I fun q => (A q)ᵀ := fun i j => hA j i

lemma SmoothEntries.const (C : Matrix n n ℝ) : SmoothEntries I fun _ : M => C := fun _ _ => Sm.const _

lemma SmoothEntries.smul {c : M → ℝ} {A : M → Matrix n n ℝ} (hc : Sm I c) (hA : SmoothEntries I A) :
    SmoothEntries I fun q => c q • A q := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]; exact hc.mul (hA i j)

/-- **The determinant of a smooth matrix is smooth** (Leibniz formula). -/
lemma SmoothEntries.det {A : M → Matrix n n ℝ} (hA : SmoothEntries I A) : Sm I fun q => (A q).det := by
  simp only [Matrix.det_apply]
  refine Sm.sum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (Sm.const _).mul (Sm.prod _ fun i _ => hA _ _)

lemma SmoothEntries.adjugate {A : M → Matrix n n ℝ} (hA : SmoothEntries I A) :
    SmoothEntries I fun q => (A q).adjugate := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine SmoothEntries.det (A := fun q => (A q).updateRow j (Pi.single i 1)) (fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact Sm.const _
  · exact hA a b

/-- **The inverse of a smooth invertible matrix is smooth.** -/
lemma SmoothEntries.inv {A : M → Matrix n n ℝ} (hA : SmoothEntries I A) (hd : ∀ q, (A q).det ≠ 0) :
    SmoothEntries I fun q => (A q)⁻¹ := by
  have h : ∀ q, (A q)⁻¹ = ((A q).det)⁻¹ • (A q).adjugate := fun q => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  simp only [h]
  exact (SmoothEntries.smul (hA.det.inv hd) hA.adjugate) i j

end Entries

/-! ### Maps into spaces of linear maps -/

section CLM

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

lemma contMDiff_finset_sum' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}
    (s : Finset ι) {f : ι → M → F} (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, F) ∞ (f i)) :
    ContMDiff I 𝓘(ℝ, F) ∞ fun q => ∑ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contMDiff_const : ContMDiff I 𝓘(ℝ, F) ∞ fun _ : M => (0 : F))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **A map into linear maps from `ℝⁿ` is smooth if its values on the basis are.** -/
lemma contMDiff_clm_of_eval {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → (Fin n → ℝ) →L[ℝ] F}
    (h : ∀ j, ContMDiff I 𝓘(ℝ, F) ∞ fun q => f q (Pi.single j 1)) :
    ContMDiff I 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] F) ∞ f := by
  have e : f = fun q => ∑ j, ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) F
      (ContinuousLinearMap.proj j) (f q (Pi.single j 1)) := by
    funext q
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  rw [e]
  exact contMDiff_finset_sum' _ fun j _ => (ContinuousLinearMap.contMDiff _).comp (h j)

end CLM

/-! ### The cover of `Y13(ℝ⁴)` -/

attribute [local instance] chartTilde chartY13

instance isManifold_Ytilde_R4 : IsManifold 𝓘(ℝ, EY) ∞ (Ytilde R4) := isManifold_tilde_R4
instance isManifold_Y13_R4 : IsManifold 𝓘(ℝ, EY) ∞ (Y13o R4) := isManifold_Y13_self

/-- The coordinates of the metric point of the cover, in the global chart. -/
lemma contMDiff_cYp :
    ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, EY) ∞ fun q : Ytilde R4 => cYp a₀ ((piT q : Y13o R4) : Yobs R4) := by
  intro q0
  have hπ : ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, EY) ∞ (piT : Ytilde R4 → Y13o R4) := isLocalDiffeomorph_tilde.contMDiff
  have hc := (contMDiffOn_chart (I := 𝓘(ℝ, EY)) (n := ∞) (x := piT q0)).contMDiffAt
    ((chartAt EY (piT q0)).open_source.mem_nhds (mem_chart_source EY (piT q0)))
  exact hc.comp q0 (hπ q0)

/-- **The metric is smooth on the cover.** -/
lemma smooth_G : SmoothEntries 𝓘(ℝ, EY) fun q : Ytilde R4 => Gpt (q.proj : Yobs R4) := by
  intro i j
  have h : (fun q : Ytilde R4 => Gpt (q.proj : Yobs R4) i j) =
      fun q => (cYp a₀ ((piT q : Y13o R4) : Yobs R4)).2 (symIdx i j) := by
    funext q
    rw [← gaugeMetric_R4 a₀]
    rfl
  rw [h]
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) (symIdx i j)).comp
    (ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) (Fin 10 → ℝ))).contMDiff.comp contMDiff_cYp

lemma smooth_gF (k : Fin 4) : Sm 𝓘(ℝ, EY) fun q : Ytilde R4 => gF q k :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).contMDiff.comp gF_smooth

lemma smooth_quat : SmoothEntries 𝓘(ℝ, EY) fun q : Ytilde R4 => quat (gF q) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [quat] <;>
    first | exact smooth_gF _ | exact (smooth_gF _).neg

lemma quat_inv_eq {g : R4} (hg : g ≠ 0) :
    (quat g)⁻¹ = (g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2)⁻¹ • (quat g)ᵀ := by
  have hn : g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2 ≠ 0 := by
    intro h; apply hg
    have h0 : g 0 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h1 : g 1 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h2 : g 2 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h3 : g 3 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    ext i; fin_cases i <;> simp [h0, h1, h2, h3]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, quat_mul_transpose, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma smooth_quat_inv : SmoothEntries 𝓘(ℝ, EY) fun q : Ytilde R4 => (quat (gF q))⁻¹ := by
  have h : (fun q : Ytilde R4 => (quat (gF q))⁻¹) = fun q =>
      (gF q 0 ^ 2 + gF q 1 ^ 2 + gF q 2 ^ 2 + gF q 3 ^ 2)⁻¹ • (quat (gF q))ᵀ :=
    funext fun q => quat_inv_eq (gF_ne q)
  rw [h]
  refine SmoothEntries.smul ?_ smooth_quat.transpose
  refine Sm.inv ?_ fun q => ?_
  · exact (((smooth_gF 0).mul (smooth_gF 0)).add ((smooth_gF 1).mul (smooth_gF 1))).add
      ((smooth_gF 2).mul (smooth_gF 2)) |>.add ((smooth_gF 3).mul (smooth_gF 3)) |>.congr
      fun q => by ring
  · intro h0
    have := gF_ne q
    apply this
    have : gF q 0 ^ 2 + gF q 1 ^ 2 + gF q 2 ^ 2 + gF q 3 ^ 2 = 0 := h0
    ext k; fin_cases k <;> simp <;> nlinarith [sq_nonneg (gF q 0), sq_nonneg (gF q 1),
      sq_nonneg (gF q 2), sq_nonneg (gF q 3)]

/-! ### The gauge factor is smooth on the gauge set -/

section Gauge

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {G : M → M4} (hG : SmoothEntries I G) (hS : ∀ q, G q ∈ gaugeSet)
include hG hS

lemma sm_G00_pos (q : M) : 0 < G q 0 0 := (hS q).1

lemma sm_schur (i j : Fin 4) : Sm I fun q => schur (G q) i j :=
  (((hG 0 i).mul (hG 0 j)).div (hG 0 0) fun q => (sm_G00_pos hG hS q).ne').sub (hG i j)

lemma sm_c11 : Sm I fun q => c11 (G q) := (sm_schur hG hS 1 1).sqrt fun q => (hS q).2.1

lemma c11_pos (q : M) : 0 < c11 (G q) := Real.sqrt_pos.mpr (hS q).2.1

lemma sm_c21 : Sm I fun q => c21 (G q) :=
  (sm_schur hG hS 1 2).div (sm_c11 hG hS) fun q => (c11_pos hG hS q).ne'

lemma sm_c31 : Sm I fun q => c31 (G q) :=
  (sm_schur hG hS 1 3).div (sm_c11 hG hS) fun q => (c11_pos hG hS q).ne'

lemma sm_m2 : Sm I fun q => m2 (G q) :=
  (sm_schur hG hS 2 2).sub ((sm_c21 hG hS).mul (sm_c21 hG hS) |>.congr fun q => by ring)

lemma sm_c22 : Sm I fun q => c22 (G q) := (sm_m2 hG hS).sqrt fun q => (hS q).2.2.1

lemma c22_pos (q : M) : 0 < c22 (G q) := Real.sqrt_pos.mpr (hS q).2.2.1

lemma sm_c32 : Sm I fun q => c32 (G q) :=
  ((sm_schur hG hS 2 3).sub ((sm_c31 hG hS).mul (sm_c21 hG hS))).div (sm_c22 hG hS)
    fun q => (c22_pos hG hS q).ne'

lemma sm_m3 : Sm I fun q => m3 (G q) :=
  ((sm_schur hG hS 3 3).sub ((sm_c31 hG hS).mul (sm_c31 hG hS) |>.congr fun q => by ring)).sub
    ((sm_c32 hG hS).mul (sm_c32 hG hS) |>.congr fun q => by ring)

lemma sm_c33 : Sm I fun q => c33 (G q) := (sm_m3 hG hS).sqrt fun q => (hS q).2.2.2

lemma sm_sqrt00 : Sm I fun q => Real.sqrt (G q 0 0) := (hG 0 0).sqrt fun q => sm_G00_pos hG hS q

/-- **The gauge factor of a smooth metric in the gauge set is smooth.** -/
lemma SmoothEntries.gaugeP : SmoothEntries I fun q => gaugeP (G q) := by
  have h0 : ∀ q, Real.sqrt (G q 0 0) ≠ 0 := fun q => (Real.sqrt_pos.mpr (sm_G00_pos hG hS q)).ne'
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [GU.Library.gaugeP, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | exact Sm.const _
    | exact sm_sqrt00 hG hS
    | exact (hG _ _).div (sm_sqrt00 hG hS) h0
    | exact sm_c11 hG hS
    | exact sm_c21 hG hS
    | exact sm_c31 hG hS
    | exact sm_c22 hG hS
    | exact sm_c32 hG hS
    | exact sm_c33 hG hS

end Gauge

/-! ### The global frame is smooth -/

lemma smooth_conjG : SmoothEntries 𝓘(ℝ, EY) conjG :=
  (smooth_quat.mul smooth_G).mul smooth_quat.transpose

lemma smooth_Pf : SmoothEntries 𝓘(ℝ, EY) Pf :=
  smooth_quat_inv.mul (SmoothEntries.gaugeP smooth_conjG conjG_mem)

lemma smooth_Pf_inv : SmoothEntries 𝓘(ℝ, EY) fun q => (Pf q)⁻¹ :=
  smooth_Pf.inv fun q => ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Pf q)).ne_zero

lemma clm_eval_sum (w : (Fin 4 → ℝ) →L[ℝ] ℝ) (v : Fin 4 → ℝ) :
    w v = ∑ l, v l * w (Pi.single l 1) := by
  conv_lhs => rw [show v = ∑ l, v l • (Pi.single l 1 : Fin 4 → ℝ) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul]

/-- `TP` applied to a fixed vector is smooth in a smooth invertible matrix. -/
lemma contMDiff_TP {P : Ytilde R4 → M4} (hP : SmoothEntries 𝓘(ℝ, EY) P)
    (hPi : SmoothEntries 𝓘(ℝ, EY) fun q => (P q)⁻¹) (hu : ∀ q, IsUnit (P q)) (u : CFib) :
    ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, CFib) ∞ fun q => TP (P q) (hu q) u := by
  refine ContMDiff.prodMk_space ?_ ?_
  · show ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, Fin 10 → ℝ) ∞ fun q => symCoords (P q * symMat u.1 * (P q)ᵀ)
    refine contMDiff_pi_module_iff.mpr fun k => ?_
    have h := (hP.mul (SmoothEntries.const (symMat u.1))).mul hP.transpose
    exact h _ _
  · show ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, (Fin 4 → ℝ) →L[ℝ] ℝ) ∞ fun q => u.2.comp (toCLM (P q)⁻¹)
    refine contMDiff_clm_of_eval fun k => ?_
    have e : (fun q => (u.2.comp (toCLM (P q)⁻¹)) (Pi.single k 1)) =
        fun q => ∑ l, (P q)⁻¹ l k * u.2 (Pi.single l 1) := by
      funext q
      rw [ContinuousLinearMap.comp_apply, toCLM_apply, clm_eval_sum]
      congr 1; funext l
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e]
    exact Sm.sum _ fun l _ => (hPi l k).mul (Sm.const _)

/-- The frame `tpF (Pf q)` is smooth. -/
lemma contMDiff_tpF_Pf : ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, HomF) ∞ fun q => tpF (Pf q) := by
  refine contMDiff_clm_of_eval fun j => ?_
  have e : (fun q => tpF (Pf q) (Pi.single j 1)) = fun q => TP (Pf q) (isUnit_Pf q) (ΦL (Pi.single j 1)) := by
    funext q; rw [tpF_of_unit (isUnit_Pf q), tpFrame_apply]
  rw [e]
  exact contMDiff_TP smooth_Pf smooth_Pf_inv isUnit_Pf _

/-- The frame in the model space of `HomTotM`. -/
lemma contMDiff_pair :
    ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, HomModel) ∞
      fun q : Ytilde R4 => pairHM (cYp a₀ ((piT q : Y13o R4) : Yobs R4)) (tpF (Pf q)) := by
  have h : ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, EY × HomF) ∞
      fun q : Ytilde R4 => (cYp a₀ ((piT q : Y13o R4) : Yobs R4), tpF (Pf q)) :=
    ContMDiff.prodMk_space contMDiff_cYp contMDiff_tpF_Pf
  exact h

/-- **The global frame is smooth**, as a map into the frames of `C`. -/
theorem contMDiff_Ff_val : ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, HomModel) ∞ fun q : Ytilde R4 => (Ff q : HomTotM R4) := by
  intro q
  have hT := pair_mem_target a₀ (chartDom_R4 a₀ (q.proj : Yobs R4)) (tpF (Pf q))
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, HomModel)) (n := ∞) (x := a₀)).contMDiffAt
    ((chartAt HomModel a₀).open_target.mem_nhds hT)
  show ContMDiffAt 𝓘(ℝ, EY) 𝓘(ℝ, HomModel) ∞
    (fun q : Ytilde R4 => (chartAt HomModel a₀).symm
      (pairHM (cYp a₀ ((piT q : Y13o R4) : Yobs R4)) (tpF (Pf q)))) q
  exact hs.comp q (contMDiff_pair q)

/-- **The global frame `Ff` of the chimeric bundle over the cover of `Y13(ℝ⁴)` is smooth.** -/
theorem contMDiff_Ff :
    letI := regCharted (Fframe_regular (X := R4))
    ContMDiff 𝓘(ℝ, EY) 𝓘(ℝ, EF) ∞ Ff := by
  letI := regCharted (Fframe_regular (X := R4))
  exact (contMDiff_regularLevel_iff (Fframe_regular (X := R4))).mpr contMDiff_Ff_val

/-! ### The spin structure on the cover is a smooth principal bundle -/

/-- **`coverSpin` is a smooth principal `Spin(7,7)`-bundle over the cover**, with the same total space
and action as `coverSpin`. -/
def smoothCoverSpin :
    SmoothPrincipalBundle 𝓘(ℝ, EY) 𝓘(ℝ, E77) (𝓘(ℝ, EY).prod 𝓘(ℝ, E77)) (Ytilde R4) Spin77
      (Ytilde R4 × Spin77) where
  proj := Prod.fst
  act p g := (p.1, p.2 * g)
  act_one p := by simp
  act_mul p g h := by simp [mul_assoc]
  proj_act _ _ := rfl
  free p g h := by
    have : p.2 * g = p.2 := congrArg Prod.snd h
    exact mul_eq_left.mp this
  transitive p q h := ⟨p.2⁻¹ * q.2, Prod.ext h (by simp)⟩
  proj_surjective b := ⟨(b, 1), rfl⟩
  smooth_proj := contMDiff_fst
  smooth_act := (contMDiff_fst.comp contMDiff_fst).prodMk
    ((contMDiff_snd.comp contMDiff_fst).mul contMDiff_snd)
  locTriv _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun y => (y, 1), Prod.snd,
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn, fun _ _ => rfl, contMDiff_snd.contMDiffOn,
    fun p _ => Prod.ext rfl (one_mul _)⟩

lemma smoothCoverSpin_act (p : Ytilde R4 × Spin77) (g : Spin77) :
    smoothCoverSpin.act p g = coverSpin.actS p g := rfl

/-- **The map of `coverSpin` to the frames is smooth** (its `OFr` component; the cover component is
the projection). -/
theorem contMDiff_coverSpin_Φ :
    letI := regCharted (Fframe_regular (X := R4))
    ContMDiff (𝓘(ℝ, EY).prod 𝓘(ℝ, E77)) 𝓘(ℝ, EF) ∞
      fun p : Ytilde R4 × Spin77 => (coverSpin.Φ p).1.2 := by
  letI := regCharted (Fframe_regular (X := R4))
  haveI := isManifold_regularLevel (Fframe_regular (X := R4))
  have hρ : ContMDiff 𝓘(ℝ, E77) 𝓘(ℝ, E77) ∞ (spinToO77 : Spin77 → O77) := isLocalDiffeomorph_ρ.contMDiff
  have h := (contMDiff_actOFr (X := R4)).comp ((contMDiff_Ff.comp contMDiff_fst).prodMk (hρ.comp contMDiff_snd))
  exact h


/-- **The whole map of `coverSpin` to the pulled-back frames is smooth**, as a map into
`Ytilde ℝ⁴ × OFr ℝ⁴` (`OFrT` itself carries no manifold structure here). Unlike `smoothSpinBundle`, no
local-diffeomorphism property of `Φ` is claimed. -/
theorem contMDiff_coverSpin_Φ_full :
    letI := regCharted (Fframe_regular (X := R4))
    ContMDiff (𝓘(ℝ, EY).prod 𝓘(ℝ, E77)) (𝓘(ℝ, EY).prod 𝓘(ℝ, EF)) ∞
      fun p : Ytilde R4 × Spin77 => ((coverSpin.Φ p).1 : Ytilde R4 × OFr R4) := by
  letI := regCharted (Fframe_regular (X := R4))
  exact contMDiff_fst.prodMk contMDiff_coverSpin_Φ

end

end GU.Library

