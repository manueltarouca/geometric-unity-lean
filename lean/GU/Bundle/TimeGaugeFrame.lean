/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TimeGauge

/-!
# Phase 4, item 4: spin structures over the time-gauge locus

In the total-space chart at `a` (fibre over a chart of `X`), `gaugeW a` is the open set of points of
`Y13` in the chart domain whose chart metric lies in `gaugeSet`. **`exists_spinLiftData_gauge`**:
`gaugeW a` carries a global frame, hence a spin structure with trivial lifts. For the base point `pLoop x 0` it is nonempty
(`yLoop_zero_mem_gaugeW`); it never contains the whole metric loop (by `no_spinStructure`). Not
shown here: that `gaugeSet` is exactly `{G₀₀ > 0}` among (1,3) metrics (`mem_gaugeSet_iff`), that `gaugeW` is a maximal open set
with a spin structure among arbitrary open sets (among `HGauge`-invariant ones over `ℝ⁴`, it is the
largest: `gauge_largest_iff`), or anything about the chart domain being all of `Y13` when `X = ℝ⁴`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

open Classical in
/-- The frame `TP_P ∘ Φ`, total in `P`. -/
def tpF (P : M4) : HomF := if h : IsUnit P then tpFrame P h else 0

lemma tpF_of_unit {P : M4} (h : IsUnit P) : tpF P = tpFrame P h := dif_pos h

lemma continuousOn_inv_of_unit {Z : Type*} [TopologicalSpace Z] {A : Set Z} {P : Z → M4}
    (hP : ContinuousOn P A) (hu : ∀ x ∈ A, IsUnit (P x)) :
    ContinuousOn (fun x => (P x)⁻¹) A := by
  have hdet : ContinuousOn (fun x => (P x).det) A :=
    (continuous_id.matrix_det.comp_continuousOn hP)
  have hadj : ContinuousOn (fun x => (P x).adjugate) A :=
    (continuous_id.matrix_adjugate.comp_continuousOn hP)
  have hne : ∀ x ∈ A, (P x).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hu x hx)).ne_zero
  refine ((hdet.inv₀ hne).smul hadj).congr fun x _ => ?_
  show (P x)⁻¹ = (P x).det⁻¹ • (P x).adjugate
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

lemma continuousOn_tpF {Z : Type*} [TopologicalSpace Z] {A : Set Z} {P : Z → M4}
    (hP : ContinuousOn P A) (hu : ∀ x ∈ A, IsUnit (P x)) :
    ContinuousOn (fun x => tpF (P x)) A := by
  refine continuousOn_clm_apply.mpr fun v => ?_
  set u : CFib := ΦL v
  have h1 : ContinuousOn (fun x => symCoords (P x * symMat u.1 * (P x)ᵀ)) A := by
    have hc : Continuous fun M : M4 => M * symMat u.1 * Mᵀ :=
      (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose
    have hM : ContinuousOn (fun x => P x * symMat u.1 * (P x)ᵀ) A := hc.comp_continuousOn hP
    exact continuousOn_pi.mpr fun k => (continuous_apply_apply _ _).comp_continuousOn hM
  have h2 : ContinuousOn (fun x => u.2.comp (toCLM (P x)⁻¹)) A := by
    refine continuousOn_clm_apply.mpr fun w => ?_
    show ContinuousOn (fun x => u.2 ((P x)⁻¹ *ᵥ w)) A
    have hc : Continuous fun M : M4 => M *ᵥ w := continuous_id.matrix_mulVec continuous_const
    exact u.2.continuous.comp_continuousOn (hc.comp_continuousOn (continuousOn_inv_of_unit hP hu))
  refine (h1.prodMk h2).congr fun x hx => ?_
  show tpF (P x) v = _
  rw [tpF_of_unit (hu x hx)]; rfl

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The base chart at `a`, in product form. -/
def cYp (a : HomTotM X) (y : Yobs X) : (Fin 4 → ℝ) × (Fin 10 → ℝ) :=
  chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj y

/-- The metric in the chart at `a`. -/
def gaugeMetric (a : HomTotM X) (y : Yobs X) : M4 := symMat (cYp a y).2

/-- The chart domain at `a`. -/
def chartDom (a : HomTotM X) : Set (Yobs X) :=
  (trivializationAt HomF (HomCb (X := X)) a.proj).baseSet ∩
    (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).source

lemma isOpen_chartDom (a : HomTotM X) : IsOpen (chartDom a) :=
  (trivializationAt HomF (HomCb (X := X)) a.proj).open_baseSet.inter
    (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).open_source

lemma continuousOn_cYp (a : HomTotM X) : ContinuousOn (cYp a) (chartDom a) :=
  (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).continuousOn.mono fun _ h => h.2

lemma continuous_symMat : Continuous (symMat : (Fin 10 → ℝ) → M4) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _

lemma continuousOn_gaugeMetric (a : HomTotM X) : ContinuousOn (gaugeMetric a) (chartDom a) :=
  continuous_symMat.comp_continuousOn (continuous_snd.comp_continuousOn (continuousOn_cYp a))

/-- **The time-gauge locus in the chart at `a`.** -/
def gaugeW (a : HomTotM X) : Set (Y13o X) :=
  {y | (y : Yobs X) ∈ chartDom a ∧ gaugeMetric a y ∈ gaugeSet}

lemma isOpen_gaugeW (a : HomTotM X) : IsOpen (gaugeW a) := by
  have h := (continuousOn_gaugeMetric a).isOpen_inter_preimage (isOpen_chartDom a) isOpen_gaugeSet
  exact h.preimage continuous_subtype_val

/-- The zero frame over `y` lies in the chart source. -/
lemma zero_mem_source (a : HomTotM X) {y : Yobs X} (hy : y ∈ chartDom a) :
    (⟨y, (0 : HomF)⟩ : HomTotM X) ∈ (chartAt HomModel a).source :=
  (mem_chart_source_iff a _).mpr hy

lemma cYp_eq (a : HomTotM X) {y : Yobs X} (hy : y ∈ chartDom a) :
    (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a ⟨y, (0 : HomF)⟩).1) = cYp a y :=
  chart_fst a _ (zero_mem_source a hy)

lemma gaugeMetric_det_ne (a : HomTotM X) {y : Yobs X} (hy : y ∈ chartDom a) :
    (gaugeMetric a y).det ≠ 0 := by
  have h := chart_target_nondeg a ((chartAt HomModel a).map_source (zero_mem_source a hy))
  rw [Lchart_apply] at h
  have h2 : (cYp a y).2 ∈ nondeg := by rw [← cYp_eq a hy]; exact h
  exact h2

lemma gaugeMetric_symm (a : HomTotM X) (y : Yobs X) : (gaugeMetric a y).IsSymm := symMat_isSymm _

lemma gaugeP_unit (a : HomTotM X) {y : Y13o X} (hy : y ∈ gaugeW a) :
    IsUnit (gaugeP (gaugeMetric a y)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply gaugeMetric_det_ne a hy.1
  rw [← gaugeP_eq (gaugeMetric_symm a y) hy.2, Matrix.det_mul, Matrix.det_mul, h0]; simp

/-- The frame in chart coordinates. -/
def gaugeFrame (a : HomTotM X) (y : Yobs X) : HomF := tpF (gaugeP (gaugeMetric a y))

/-- The frame as a point of the bundle. -/
def σ0 (a : HomTotM X) (y : Yobs X) : HomTotM X :=
  (chartAt HomModel a).symm (pairHM (cYp a y) (gaugeFrame a y))

lemma pair_mem_target (a : HomTotM X) {y : Yobs X} (hy : y ∈ chartDom a) (h : HomF) :
    pairHM (cYp a y) h ∈ (chartAt HomModel a).target := by
  have h0 := (chartAt HomModel a).map_source (zero_mem_source a hy)
  have h1 : pairHM (cYp a y) (show HomF from (chartAt HomModel a ⟨y, (0 : HomF)⟩).2) ∈
      (chartAt HomModel a).target := by
    rw [← cYp_eq a hy]; exact h0
  exact (mem_chart_target_iff a _ _ _).mp h1

lemma Bm_singles (i j : Fin 14) :
    Bm (Pi.single i 1) (Pi.single j 1) = η77 i j := by
  rw [Bm_single]
  show _ = Matrix.of η77 i j
  rw [η77_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h), zero_mul]

/-- **The gauge frame is orthonormal.** -/
lemma σ0_mem (a : HomTotM X) {y : Y13o X} (hy : y ∈ gaugeW a) : σ0 a y ∈ OFr X := by
  have hT := pair_mem_target a hy.1 (gaugeFrame a y)
  show Fframe ((chartAt HomModel a).symm _) = ⟨η77, ηSig_mem 7 7⟩
  rw [Fframe_chart a hT]
  apply Subtype.ext
  set s := (cYp a (y : Yobs X)).2
  set h := gaugeFrame a (y : Yobs X)
  show (symP 14 (bil (Gchim s) (homMat.symm h) (homMat.symm h)) : Mat 14) = η77
  have hb : bil (Gchim s) (homMat.symm h) (homMat.symm h) = η77 := by
    funext i j
    rw [bil_homMat_entry]
    have hG : symMat s = gaugeP (gaugeMetric a y) * ηR * (gaugeP (gaugeMetric a y))ᵀ :=
      (gaugeP_eq (gaugeMetric_symm a y) hy.2).symm
    show Bmod (symMat s) (gaugeFrame a y _) (gaugeFrame a y _) = _
    rw [hG]
    unfold gaugeFrame
    rw [tpF_of_unit (gaugeP_unit a hy), tpFrame_apply, tpFrame_apply, TP_isometry, Bη_Φ_eq,
      Bm_singles]
  rw [hb, symP_of_mem (ηSig_mem 7 7)]

lemma proj_σ0 (a : HomTotM X) {y : Yobs X} (hy : y ∈ chartDom a) : (σ0 a y).proj = y := by
  have hT := pair_mem_target a hy (gaugeFrame a y)
  have hsrc := (chartAt HomModel a).map_target hT
  have h1 := chart_fst a _ hsrc
  have h2 : (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a (σ0 a y)).1) = cYp a y := by
    show (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a
      ((chartAt HomModel a).symm (pairHM (cYp a y) (gaugeFrame a y)))).1) = _
    rw [(chartAt HomModel a).right_inv hT]; rfl
  exact (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).injOn
    (proj_mem_chart_source a _ hsrc) hy.2 (h1.symm.trans h2)

lemma continuousOn_σ0 (a : HomTotM X) :
    ContinuousOn (fun y : Y13o X => σ0 a y) (gaugeW a) := by
  have hm : ContinuousOn (fun y : Y13o X => gaugeMetric a y) (gaugeW a) :=
    (continuousOn_gaugeMetric a).comp continuous_subtype_val.continuousOn fun _ h => h.1
  have hP : ContinuousOn (fun y : Y13o X => gaugeP (gaugeMetric a y)) (gaugeW a) :=
    continuousOn_gaugeP.comp hm fun _ h => h.2
  have hF : ContinuousOn (fun y : Y13o X => gaugeFrame a y) (gaugeW a) :=
    continuousOn_tpF hP fun _ h => gaugeP_unit a h
  have hc : ContinuousOn (fun y : Y13o X => cYp a y) (gaugeW a) :=
    (continuousOn_cYp a).comp continuous_subtype_val.continuousOn fun _ h => h.1
  have hpair : ContinuousOn (fun y : Y13o X => pairHM (cYp a y) (gaugeFrame a y)) (gaugeW a) :=
    hc.prodMk hF
  exact (chartAt HomModel a).continuousOn_symm.comp hpair fun y hy => pair_mem_target a hy.1 _

open Classical in
/-- **The gauge frame as a map to the frame bundle.** -/
def σG (a : HomTotM X) (y : Y13o X) : OFr X :=
  if hy : y ∈ gaugeW a then ⟨σ0 a y, σ0_mem a hy⟩
  else
    let q := (orthoM_iff_13 (y : Yobs X)).mpr y.2
    ⟨q.choose, by rw [OFr, levelSet_Fframe]; exact q.choose_spec.2⟩

lemma continuousOn_σG (a : HomTotM X) : ContinuousOn (σG a) (gaugeW a) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  refine (continuousOn_σ0 a).congr fun y hy => ?_
  show ((σG a y : OFr X) : HomTotM X) = σ0 a y
  unfold σG; rw [dif_pos hy]

lemma proj_σG (a : HomTotM X) {y : Y13o X} (hy : y ∈ gaugeW a) : projOFr (σG a y) = y := by
  apply Subtype.ext
  show ((σG a y : OFr X) : HomTotM X).proj = y
  unfold σG; rw [dif_pos hy]
  exact proj_σ0 a hy.1

/-- **Spin structure over the time-gauge locus.** -/
theorem exists_spinLiftData_gauge (a : HomTotM X) : ∃ D : SpinLiftData X, D.W = gaugeW a :=
  ⟨SpinLiftData.ofSection (gaugeW a) (isOpen_gaugeW a) (σG a) (continuousOn_σG a)
    fun _ hy => proj_σG a hy, rfl⟩

/-- The metric-loop base point `ηR` lies in the time-gauge locus of its own chart, so the locus is
nonempty over every `x`. -/
theorem yLoop_zero_mem_gaugeW (x : X) :
    projOFr (pLoop x 0) ∈ gaugeW (pLoop x 0 : HomTotM X) := by
  have hdom : ((projOFr (pLoop x 0) : Y13o X) : Yobs X) ∈ chartDom (pLoop x 0 : HomTotM X) :=
    (mem_chart_source_iff (pLoop x 0 : HomTotM X) (pLoop x 0 : HomTotM X)).mp
      (mem_chart_source HomModel _)
  refine ⟨hdom, ?_⟩
  have hG : gaugeMetric (pLoop x 0 : HomTotM X) (projOFr (pLoop x 0) : Y13o X) = ηR := by
    show symMat ((symCore (Zt X)).coordChange ((symCore (Zt X)).indexAt x)
      ((symCore (Zt X)).indexAt x) x (sθ 0)) = ηR
    rw [(symCore (Zt X)).coordChange_self _ _ ((symCore (Zt X)).mem_baseSet_at x), symMat_sθ, Gθ,
      Rθ_zero]
    simp
  rw [hG]; exact ηR_mem_gaugeSet

end

end GU.Library
