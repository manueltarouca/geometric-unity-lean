/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.CoverSmooth
import GU.Bundle.TimeCoverReduction
import GU.Bundle.CoverSpinLocal

/-!
# Phase 7, item 2: the cover of a parallelisable `X`

`TXFrame X`: a global frame `F` of `TX`, given in the preferred chart at each point and continuous in
every chart. From it:

* **`yF`**: the metric of `y` in the frame, `F⁻¹ G F⁻ᵀ`, as a point of `Y13(ℝ⁴)` over `0` (continuous);
* **`Ψ`**: the map of covers `Ytilde X → Ytilde ℝ⁴`, sending the future cone of `p` to the frame
  coordinates of it (continuous, `continuous_Ψ`);
* **`PX`**: the Lorentz frame `F · Pf (Ψ p)`, pulled back from the global frame over `ℝ⁴`; its time
  covector is future (`tcov_PX`), so it lies in the reduction `redT X`;
* **`exists_coverSpin_parallel`**: a `Spin⁺(7,7)` structure over the whole cover with image `redT X`.

No hypothesis on `X` beyond the frame (no Hausdorff or σ-compactness): the global future covector
comes from the cover of `ℝ⁴` through `Ψ`, which sends every point to the fibre over `0`.

Instances (`TXFrame.ofSubsingleton`, any one-chart `X`, with `F = 1`):
* `ℝ⁴` (`frameR4`, `exists_coverSpin_R4'`). Its image is `redT ℝ⁴`, which is the image `QT` of
  `coverSpin` (`QT_eq_redT`, via `Ff_mem_redT`), so it recovers `coverSpin`'s image
  (`exists_coverSpin_R4''`).
* `ℝ⁴` minus the plane `x⁰ = x¹ = 0` (`frameHole`, `exists_coverSpin_hole`), which is not simply
  connected (`loopU_not_nullHomotopic`, by the angle map to the circle; `not_simplyConnected_holeU`).

`continuous_section`: the columns of `F` are continuous sections of Mathlib's tangent bundle.

Not covered: smoothness of the frame for general `X`, and non-parallelisable `X`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **A global frame of `TX`**: at each `x` an invertible matrix `F x`, whose columns are the frame
vectors in the preferred chart at `x`, continuous in every chart. -/
structure TXFrame (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] where
  F : X → M4
  unit : ∀ x, IsUnit (F x)
  cont : ∀ i : atlas (Fin 4 → ℝ) X,
    ContinuousOn (fun x => ccM ((Zt X).indexAt x) i x * F x) ((Zt X).baseSet i)

namespace TXFrame

variable (T : TXFrame X)

/-- **Faithfulness of the encoding**: the columns of `F` are continuous sections of Mathlib's
tangent bundle. -/
theorem continuous_section (j : Fin 4) :
    Continuous fun x : X =>
      (⟨x, (T.F x)ᵀ j⟩ : TangentBundle (modelWithCornersSelf ℝ (Fin 4 → ℝ)) X) := by
  refine continuous_iff_continuousAt.mpr fun x0 => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  set i := (Zt X).indexAt x0
  have hS : IsOpen ((Zt X).baseSet i) := (Zt X).isOpen_baseSet i
  have hx0 : x0 ∈ (Zt X).baseSet i := (Zt X).mem_baseSet_at _
  have hc : ContinuousOn (fun x => (ccM ((Zt X).indexAt x) i x * T.F x)ᵀ j) ((Zt X).baseSet i) :=
    (continuous_apply j).comp_continuousOn (continuous_id.matrix_transpose.comp_continuousOn (T.cont i))
  refine (hc.congr fun x hx => ?_).continuousAt (hS.mem_nhds hx0)
  rw [TangentBundle.trivializationAt_eq_localTriv]
  show ((Zt X).coordChange ((Zt X).indexAt x) i x) ((T.F x)ᵀ j) = _
  rw [← toCLM_mat ((Zt X).coordChange ((Zt X).indexAt x) i x), toCLM_apply]
  rfl

lemma det_ne (x : X) : (T.F x).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (T.unit x)).ne_zero

/-- The metric of `y` in the frame. -/
def Gf (y : Y13o X) : M4 := (T.F (baseX y))⁻¹ * Gpt (y : Yobs X) * ((T.F (baseX y))⁻¹)ᵀ

lemma Gf_eq (y : Y13o X) (P : M4) (hP : Gpt (y : Yobs X) = P * ηR * Pᵀ) :
    T.Gf y = ((T.F (baseX y))⁻¹ * P) * ηR * ((T.F (baseX y))⁻¹ * P)ᵀ := by
  rw [Gf, hP, transpose_mul]; simp only [Matrix.mul_assoc]

/-- In the chart `i`, `Gf = (J F)⁻¹ · chartG · (J F)⁻ᵀ`. -/
lemma Gf_chart {i : atlas (Fin 4 → ℝ) X} {y : Y13o X} (hy : baseX y ∈ (Zt X).baseSet i) :
    T.Gf y = (ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y))⁻¹ * chartG i y *
      ((ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y))⁻¹)ᵀ := by
  set J := ccM ((Zt X).indexAt (baseX y)) i (baseX y)
  have hJ : IsUnit J := isUnit_ccM ((Zt X).mem_baseSet_at _) hy
  have hJd : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ
  rw [Gf, chartG, transMat_eq, Matrix.mul_inv_rev, transpose_mul, transpose_nonsing_inv J]
  set A := (T.F (baseX y))⁻¹
  symm
  calc A * J⁻¹ * (J * Gpt (y : Yobs X) * Jᵀ) * (Jᵀ⁻¹ * Aᵀ)
      = A * (J⁻¹ * J) * Gpt (y : Yobs X) * (Jᵀ * Jᵀ⁻¹) * Aᵀ := by simp only [Matrix.mul_assoc]
    _ = A * Gpt (y : Yobs X) * Aᵀ := by
        rw [Matrix.nonsing_inv_mul _ hJd, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hJd)]
        simp

lemma continuous_Gf : Continuous T.Gf := by
  refine continuous_iff_continuousAt.mpr fun y0 => ?_
  set i := (Zt X).indexAt (baseX y0)
  set S := {y : Y13o X | baseX y ∈ (Zt X).baseSet i}
  have hS : IsOpen S := ((Zt X).isOpen_baseSet i).preimage continuous_baseX
  have hy0 : y0 ∈ S := (Zt X).mem_baseSet_at _
  have hJF : ContinuousOn (fun y : Y13o X => ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y)) S :=
    (T.cont i).comp continuous_baseX.continuousOn fun _ h => h
  have hu : ∀ y ∈ S, IsUnit (ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y)) := fun y hy =>
    (isUnit_ccM ((Zt X).mem_baseSet_at _) hy).mul (T.unit _)
  have hinv := continuousOn_inv_of_unit hJF hu
  have hG := continuousOn_chartG (X := X) i
  have hc : ContinuousOn (fun y : Y13o X =>
      (ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y))⁻¹ * chartG i y *
        ((ccM ((Zt X).indexAt (baseX y)) i (baseX y) * T.F (baseX y))⁻¹)ᵀ) S :=
    (hinv.mul (hG.mono fun _ h => h)).mul (continuous_id.matrix_transpose.comp_continuousOn hinv)
  exact (hc.congr fun y hy => T.Gf_chart hy).continuousAt (hS.mem_nhds hy0)

/-- The frame metric as a point of `Y13(ℝ⁴)` over `0`. -/
def yF (y : Y13o X) : Y13o R4 :=
  mkY 0 ((T.F (baseX y))⁻¹ * (y.2).choose)
    ((Matrix.isUnit_nonsing_inv_iff.mpr (T.unit _)).mul (y.2).choose_spec.1)

lemma Gpt_yF (y : Y13o X) : Gpt (T.yF y : Yobs R4) = T.Gf y := by
  rw [yF, Gpt_mkY, T.Gf_eq y _ (y.2).choose_spec.2]

lemma yF_val (y : Y13o X) :
    (((T.yF y : Y13o R4) : Yobs R4) : Sym2TX R4) = ⟨(0 : R4), symCoords (T.Gf y)⟩ := by
  show (⟨(0 : R4), symCoords _⟩ : Sym2TX R4) = _
  rw [← T.Gf_eq y _ (y.2).choose_spec.2]

lemma continuous_yF : Continuous T.yF := by
  have hs : Continuous fun y : Y13o X => symCoords (T.Gf y) :=
    continuous_pi fun k => (continuous_apply_apply _ _).comp T.continuous_Gf
  have h := continuous_mkSym' (x := fun _ : Y13o X => (0 : R4)) continuous_const hs
  rw [Topology.IsInducing.subtypeVal.continuous_iff, Topology.IsInducing.subtypeVal.continuous_iff]
  exact h.congr fun y => (T.yF_val y).symm

/-- Pairings in the frame: `lp (Gf y) (Fᵀ u) (Fᵀ v) = lp G u v`. -/
lemma lp_Gf (y : Y13o X) (u v : R4) :
    lp (T.Gf y) ((T.F (baseX y))ᵀ *ᵥ u) ((T.F (baseX y))ᵀ *ᵥ v) = lp (Gpt (y : Yobs X)) u v := by
  rw [lp_conj]
  congr 1
  have hd : IsUnit (T.F (baseX y)).det := (Matrix.isUnit_iff_isUnit_det _).mp (T.unit _)
  rw [Gf]
  calc T.F (baseX y) * ((T.F (baseX y))⁻¹ * Gpt (y : Yobs X) * ((T.F (baseX y))⁻¹)ᵀ) * (T.F (baseX y))ᵀ
      = (T.F (baseX y) * (T.F (baseX y))⁻¹) * Gpt (y : Yobs X) *
          ((T.F (baseX y) * (T.F (baseX y))⁻¹))ᵀ := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

lemma lp_yF (y : Y13o X) (u v : R4) :
    lp (Gpt (T.yF y : Yobs R4)) ((T.F (baseX y))ᵀ *ᵥ u) ((T.F (baseX y))ᵀ *ᵥ v) =
      lp (Gpt (y : Yobs X)) u v := by
  rw [Gpt_yF, lp_Gf]

end TXFrame

/-- `pt y u` depends only on the side of `u`. -/
lemma pt_congr {Z : Type} [TopologicalSpace Z] [ChartedSpace (Fin 4 → ℝ) Z]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ Z] {y : Y13o Z} {a b : R4}
    (ha : 0 < lp (Gpt (y : Yobs Z)) a a) (hb : 0 < lp (Gpt (y : Yobs Z)) b b)
    (hab : 0 < lp (Gpt (y : Yobs Z)) a b) : pt y a = pt y b := by
  obtain ⟨P, -, hG⟩ := y.2
  refine eq_of_future_eq rfl ?_
  rw [future_pt ha, future_pt hb]
  ext v
  exact and_congr_right fun hv => side_iff hG ha hb hv hab

namespace TXFrame

variable (T : TXFrame X)

/-- **The map of covers** `Ytilde X → Ytilde ℝ⁴`: the metric in the frame, with the future cone
in frame coordinates. -/
def Ψ (p : Ytilde X) : Ytilde R4 :=
  pt (T.yF p.proj) ((T.F (baseX p.proj))ᵀ *ᵥ rep p)

lemma proj_Ψ (p : Ytilde X) : (T.Ψ p).proj = T.yF p.proj := rfl

/-- In frame coordinates, a future covector of `p` is a future covector of `Ψ p`. -/
lemma Ψ_eq {p : Ytilde X} {v : R4} (hv : v ∈ future p) :
    T.Ψ p = pt (T.yF p.proj) ((T.F (baseX p.proj))ᵀ *ᵥ v) := by
  obtain ⟨Q, -, hG⟩ := p.proj.2
  refine pt_congr ?_ ?_ ?_
  · rw [T.lp_yF]; exact timelike_rep p
  · rw [T.lp_yF]; exact hv.1
  · rw [T.lp_yF, lp_comm hG]; exact hv.2

lemma mem_future_Ψ {p : Ytilde X} {v : R4} (hv : v ∈ future p) :
    (T.F (baseX p.proj))ᵀ *ᵥ v ∈ future (T.Ψ p) := by
  rw [T.Ψ_eq hv, future_pt (by rw [T.lp_yF]; exact hv.1)]
  exact ⟨by rw [T.lp_yF]; exact hv.1, by rw [T.lp_yF]; exact hv.1⟩

/-- The pulled-back covector is future for `p` iff its frame image is future for `Ψ p`. -/
lemma mem_future_iff {p : Ytilde X} (w : R4) :
    (T.F (baseX p.proj))ᵀ *ᵥ w ∈ future (T.Ψ p) ↔ w ∈ future p := by
  obtain ⟨Q, -, hG⟩ := p.proj.2
  have hr := timelike_rep p
  rw [T.Ψ_eq ⟨hr, hr⟩, future_pt (by rw [T.lp_yF]; exact hr)]
  show (_ ∧ _) ↔ (_ ∧ _)
  rw [T.lp_yF, T.lp_yF]

lemma continuous_Ψ : Continuous T.Ψ := by
  refine continuous_iff_continuousAt.mpr fun p0 => ?_
  obtain ⟨I, hI⟩ := exists_sheetY p0
  set S := sheetY I
  have hS : IsOpen S := isOpen_sheetY I
  set u : Ytilde X → R4 := fun p =>
    (ccM ((Zt X).indexAt (baseX p.proj)) I.1 (baseX p.proj) * T.F (baseX p.proj))ᵀ *ᵥ I.2
  have hu : ContinuousOn u S := by
    have h := (T.cont I.1).comp (continuous_baseX.comp continuous_piT).continuousOn
      (s := S) fun p hp => hp.1.1
    have hm : Continuous fun q : M4 × R4 => q.1 *ᵥ q.2 := continuous_fst.matrix_mulVec continuous_snd
    exact hm.comp_continuousOn ((continuous_id.matrix_transpose.comp_continuousOn h).prodMk
      continuousOn_const)
  have heq : ∀ p ∈ S, T.Ψ p = pt (T.yF p.proj) (u p) := by
    intro p hp
    have hf : cov I (baseX p.proj) ∈ future p := (mem_future_iff_localTriv I p hp.1).mpr hp.2
    rw [T.Ψ_eq hf]
    congr 1
    simp only [u, cov, transMat_eq, transpose_mul, Matrix.mulVec_mulVec]
  have hc : ContinuousOn (fun p => pt (T.yF p.proj) (u p)) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_pt_R4 ((T.continuous_yF.comp continuous_piT).comp continuous_subtype_val)
      (continuousOn_iff_continuous_domRestrict.mp hu) fun p => ?_
    have hf : cov I (baseX p.1.proj) ∈ future p.1 :=
      (mem_future_iff_localTriv I p.1 p.2.1).mpr p.2.2
    have e : u p.1 = (T.F (baseX p.1.proj))ᵀ *ᵥ cov I (baseX p.1.proj) := by
      simp only [u, cov, transMat_eq, transpose_mul, Matrix.mulVec_mulVec]
    rw [e, T.lp_yF]; exact hf.1
  exact ((hc.congr heq).continuousAt (hS.mem_nhds hI))

end TXFrame

/-- The time covector of the global Lorentz frame over `ℝ⁴` is future. -/
lemma tcov_Pf_mem (q : Ytilde R4) : tcov (Pf q) ∈ future q := by
  have hu := isUnit_Pf q
  have hq := isUnit_quat (gF_ne q)
  have ha := gaugeP_00_pos (conjG_mem q)
  have hrow : ∀ G : M4, (gaugeP G)ᵀ *ᵥ (Pi.single 0 1 : R4) = gaugeP G 0 0 • Pi.single 0 1 := by
    intro G
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply, gaugeP]
  have hqe : (quat (gF q))ᵀ *ᵥ (Pi.single 0 1 : R4) = gF q := by
    ext i; fin_cases i <;> simp [quat, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hqi : ((quat (gF q))ᵀ)⁻¹ *ᵥ gF q = Pi.single 0 1 := by
    have := congrArg (fun v => ((quat (gF q))ᵀ)⁻¹ *ᵥ v) hqe
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' hq)), Matrix.one_mulVec] at this
    exact this.symm
  have h1 : (Pf q)ᵀ *ᵥ gF q = gaugeP (conjG q) 0 0 • Pi.single 0 1 := by
    rw [Pf, transpose_mul, transpose_nonsing_inv, ← Matrix.mulVec_mulVec, hqi, hrow]
  have he : tcov (Pf q) = (gaugeP (conjG q) 0 0)⁻¹ • gF q := by
    apply Matrix.mulVec_injective_of_isUnit (isUnit_transpose' hu)
    rw [tr_mulVec_tcov hu, Matrix.mulVec_smul, h1, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [he]
  exact smul_mem_future (gF_future q) (inv_pos.mpr ha)

lemma tcov_mul (A B : M4) : tcov (A * B) = (Aᵀ)⁻¹ *ᵥ tcov B := by
  rw [tcov, tcov, transpose_mul, Matrix.mul_inv_rev, Matrix.mulVec_mulVec]

namespace TXFrame

variable (T : TXFrame X)

/-- **The Lorentz frame over the cover of `X`**, in the preferred chart: `F · Pf (Ψ p)`. -/
def PX (p : Ytilde X) : M4 := T.F (baseX p.proj) * Pf (T.Ψ p)

lemma isLF_PX (p : Ytilde X) : IsLF (Gpt (piT p : Yobs X)) (T.PX p) := by
  refine ⟨(T.unit _).mul (isUnit_Pf _), ?_⟩
  have hd : IsUnit (T.F (baseX p.proj)).det := (Matrix.isUnit_iff_isUnit_det _).mp (T.unit _)
  have h := Pf_eq (T.Ψ p)
  rw [proj_Ψ, T.Gpt_yF, Gf] at h
  rw [PX, transpose_mul]
  calc Gpt (piT p : Yobs X)
      = (T.F (baseX p.proj) * (T.F (baseX p.proj))⁻¹) * Gpt (p.proj : Yobs X) *
          (T.F (baseX p.proj) * (T.F (baseX p.proj))⁻¹)ᵀ := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp [piT]
    _ = T.F (baseX p.proj) * ((T.F (baseX p.proj))⁻¹ * Gpt (p.proj : Yobs X) *
          ((T.F (baseX p.proj))⁻¹)ᵀ) * (T.F (baseX p.proj))ᵀ := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]

/-- **Its time covector is future**, so the frame lies in the reduction `redT X`. -/
lemma tcov_PX (p : Ytilde X) : tcov (T.PX p) ∈ future p := by
  rw [← T.mem_future_iff, PX, tcov_mul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' (T.unit _))),
    Matrix.one_mulVec]
  exact tcov_Pf_mem _

/-- **The global frame of `C` on the cover.** -/
def secX (p : Ytilde X) : OFrT X := ⟨(p, rawO (piT p) (T.PX p) (T.isLF_PX p)), rfl⟩

lemma secX_mem_redT (p : Ytilde X) : T.secX p ∈ redT X :=
  ⟨T.PX p, T.isLF_PX p, T.tcov_PX p, 1, one_mem _, by rw [actOFr'_one]; rfl⟩

lemma continuous_secX : Continuous T.secX := by
  refine continuous_iff_continuousAt.mpr fun p0 => ?_
  set i := (Zt X).indexAt (baseX p0.proj)
  set S := {p : Ytilde X | baseX p.proj ∈ (Zt X).baseSet i}
  have hS : IsOpen S := ((Zt X).isOpen_baseSet i).preimage (continuous_baseX.comp continuous_piT)
  have hp0 : p0 ∈ S := (Zt X).mem_baseSet_at _
  have hJF : ContinuousOn (fun p : Ytilde X =>
      ccM ((Zt X).indexAt (baseX p.proj)) i (baseX p.proj) * T.F (baseX p.proj)) S :=
    (T.cont i).comp (continuous_baseX.comp continuous_piT).continuousOn fun _ h => h
  have hQ : ContinuousOn (fun p : Ytilde X =>
      (ccM ((Zt X).indexAt (baseX p.proj)) i (baseX p.proj) * T.F (baseX p.proj)) * Pf (T.Ψ p)) S :=
    hJF.mul (continuous_Pf.comp T.continuous_Ψ).continuousOn
  have hraw := continuousOn_rawF hS (y := fun p : Ytilde X => ((piT p : Y13o X) : Yobs X))
    (continuous_subtype_val.comp continuous_piT) i (fun p hp => hp) hQ
    (fun p hp => ((isUnit_ccM ((Zt X).mem_baseSet_at _) hp).mul (T.unit _)).mul (isUnit_Pf _))
  have h2 : ContinuousOn (fun p => rawO (piT p) (T.PX p) (T.isLF_PX p)) S := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hraw.congr fun p hp => ?_
    show rawF _ (T.PX p) = rawF _ _
    have hd : IsUnit (ccM ((Zt X).indexAt (baseX p.proj)) i (baseX p.proj)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_ccM ((Zt X).mem_baseSet_at _) hp)
    congr 1
    rw [PX]
    change _ = (ccM ((Zt X).indexAt (baseX p.proj)) i (baseX p.proj))⁻¹ *
      (ccM ((Zt X).indexAt (baseX p.proj)) i (baseX p.proj) * T.F (baseX p.proj) * Pf (T.Ψ p))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have h3 : ContinuousOn T.secX S :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr (continuousOn_id.prodMk h2)
  exact h3.continuousAt (hS.mem_nhds hp0)

include T in
/-- **A `Spin⁺(7,7)` structure over the whole cover of a parallelisable `X`**, with image the
reduction `redT X`: the spin lift of the global frame `secX`. -/
theorem exists_coverSpin_parallel : ∃ S : CoverSpin X, Set.range S.Φ = redT X := by
  rw [coverSpin_iff_data]
  let D : Gen.SpinLiftData (coverFS X) :=
    Gen.SpinLiftData.ofSection Set.univ isOpen_univ T.secX T.continuous_secX.continuousOn
      fun _ _ => rfl
  refine ⟨D, rfl, ?_⟩
  rw [D.range_Φ]
  ext q
  constructor
  · rintro ⟨-, hq⟩
    obtain ⟨g, hg, e⟩ := hq () (Set.mem_univ _)
    rw [e]
    exact redT_reduction.2.1 _ (T.secX_mem_redT _) _ hg
  · intro hq
    refine ⟨Set.mem_univ _, fun _ _ => ?_⟩
    obtain ⟨g, hg, e⟩ := redT_reduction.2.2.2 _ (T.secX_mem_redT ((coverFS X).proj q)) _ hq rfl
    exact ⟨g, hg, e.symm⟩

end TXFrame

/-! ### Instances -/

/-- **One-chart manifolds are parallelisable**: the coordinate frame `F = 1`. -/
def TXFrame.ofSubsingleton [Subsingleton (atlas (Fin 4 → ℝ) X)] : TXFrame X where
  F _ := 1
  unit _ := isUnit_one
  cont i := by
    refine (continuousOn_const (c := (1 : M4))).congr fun x hx => ?_
    show ccM ((Zt X).indexAt x) i x * 1 = (1 : M4)
    have h : (Zt X).indexAt x = i := Subsingleton.elim _ _
    rw [h, Matrix.mul_one, ccM_self hx]

instance instSubsingletonAtlasR4 : Subsingleton (atlas (Fin 4 → ℝ) R4) :=
  ⟨fun a b => Subtype.ext ((chartedSpaceSelf_atlas.mp a.2).trans (chartedSpaceSelf_atlas.mp b.2).symm)⟩

/-- **The instance `ℝ⁴`.** -/
def frameR4 : TXFrame R4 := TXFrame.ofSubsingleton

/-- Over `ℝ⁴`: a `Spin⁺(7,7)` structure over the whole cover with image `redT ℝ⁴`, from the general
construction (compare `coverSpin`, whose image is `QT`). -/
theorem exists_coverSpin_R4' : ∃ S : CoverSpin R4, Set.range S.Φ = redT R4 :=
  frameR4.exists_coverSpin_parallel

/-! #### Comparison with `coverSpin` -/

lemma jacM_R4 (y0 y : Yobs R4) : jacM y0 y = 1 := by
  unfold jacM
  have h : (Zt R4).indexAt (πY y0) = (Zt R4).indexAt (πY y) := Subsingleton.elim _ _
  rw [h]
  exact ccM_self ((Zt R4).mem_baseSet_at _)

lemma frameAt_eq_rawF (y : Yobs R4) (P : M4) : frameAt y P = rawF y P := by
  have hdom : y ∈ chartDom a₀ := chartDom_R4 a₀ y
  have hsrc : rawF y P ∈ (chartAt HomModel a₀).source := (mem_chart_source_iff a₀ _).mpr hdom
  have hT := pair_mem_target a₀ hdom (tpF P)
  -- chartAt a₀ (rawF y P) = pairHM (cYp a₀ y) (tpF P)
  have key : chartAt HomModel a₀ (rawF y P) = pairHM (cYp a₀ y) (tpF P) := by
    refine Prod.ext ?_ ?_
    · exact chart_fst a₀ _ hsrc
    · show (chartAt HomModel a₀ (rawF y P)).2 = tpF P
      rw [show chartAt HomModel a₀ = _ from FiberBundle.chartedSpace_chartAt a₀]
      show ((trivializationAt HomF (HomCb (X := R4)) a₀.proj) (rawF y P)).2 = tpF P
      have hb : (rawF y P).proj ∈ (trivializationAt CFib (Cb (X := R4)) a₀.proj).baseSet := by
        rw [Cb_baseSet]
        show πY y ∈ (Zt R4).baseSet ((Zt R4).indexAt (πY a₀.proj))
        rw [Subsingleton.elim ((Zt R4).indexAt (πY a₀.proj)) ((Zt R4).indexAt (πY y))]
        exact (Zt R4).mem_baseSet_at _
      rw [triv_apply _ _ hb]
      refine ContinuousLinearMap.ext fun v => ?_
      have e := Tz_eq_TP a₀.proj y hb (tpF P v)
      rw [TP_congr (jacM_R4 _ _) _ isUnit_one, TP_one] at e
      exact e
  calc frameAt y P = (chartAt HomModel a₀).symm (chartAt HomModel a₀ (rawF y P)) := by
        rw [key]; rfl
    _ = rawF y P := (chartAt HomModel a₀).left_inv hsrc

lemma Ff_eq_rawO (p : Ytilde R4) :
    Ff p = rawO (piT p) (Pf p) ⟨isUnit_Pf p, (Pf_eq p).symm⟩ :=
  Subtype.ext (frameAt_eq_rawF _ _)

/-- `Ff` lies in `redT`. -/
lemma Ff_mem_redT (p : Ytilde R4) : (⟨(p, Ff p), (proj_Ff p).symm⟩ : OFrT R4) ∈ redT R4 :=
  ⟨Pf p, ⟨isUnit_Pf p, (Pf_eq p).symm⟩, tcov_Pf_mem p, 1, one_mem _, by
    rw [actOFr'_one]; exact (Ff_eq_rawO p).symm⟩

theorem QT_eq_redT : QT = redT R4 := by
  ext z
  have h : IsLF (Gpt (piT z.1.1 : Yobs R4)) (Pf z.1.1) := ⟨isUnit_Pf _, (Pf_eq _).symm⟩
  rw [redT_iff h (tcov_Pf_mem _)]
  show trF z ∈ (SO0 : Subgroup O77) ↔ _
  have e : transO (rawO (piT z.1.1) (Pf z.1.1) h) z.1.2 = trF z := by
    apply transO_unique
    · exact z.2
    · rw [← Ff_eq_rawO]; exact trF_spec z
  rw [e]

/-- **The ℝ⁴ instance recovers `coverSpin`'s image**: a `Spin⁺(7,7)` structure from the general
construction with the same image `QT` as `coverSpin` (`range_coverSpin`). -/
theorem exists_coverSpin_R4'' : ∃ S : CoverSpin R4, Set.range S.Φ = Set.range coverSpin.Φ := by
  rw [range_coverSpin, QT_eq_redT]; exact exists_coverSpin_R4'

/-- `ℝ⁴` minus the plane `x⁰ = x¹ = 0`. -/
def holeU : Opens R4 := ⟨{x | x 0 ≠ 0 ∨ x 1 ≠ 0},
  (isOpen_ne_fun (continuous_apply 0) continuous_const).union
    (isOpen_ne_fun (continuous_apply 1) continuous_const)⟩

/-- Every chart of `holeU` is the restriction of the identity chart (this uses the shape of Mathlib's
`Opens.instChartedSpace` atlas). -/
instance instSubsingletonAtlasHoleU : Subsingleton (atlas (Fin 4 → ℝ) holeU) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨_, ⟨x, rfl⟩, ha⟩ := a.2
  obtain ⟨_, ⟨y, rfl⟩, hb⟩ := b.2
  rw [Set.mem_singleton_iff] at ha hb
  rw [ha, hb, chartAt_self_eq, chartAt_self_eq]

/-- **The instance `ℝ⁴ ∖ plane`**, an open subset of `ℝ⁴` that is not simply connected. -/
def frameHole : TXFrame holeU := TXFrame.ofSubsingleton

theorem exists_coverSpin_hole : ∃ S : CoverSpin holeU, Set.range S.Φ = redT holeU :=
  frameHole.exists_coverSpin_parallel

section HoleAngle

/-- `x⁰ + i x¹`. -/
def zU (x : holeU) : ℂ := ⟨(x : R4) 0, (x : R4) 1⟩

lemma zU_ne (x : holeU) : zU x ≠ 0 := by
  intro h
  rcases x.2 with h' | h'
  · exact h' (congrArg Complex.re h)
  · exact h' (congrArg Complex.im h)

lemma continuous_zU : Continuous zU := by
  have h0 : Continuous fun x : holeU => (x : R4) 0 := (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun x : holeU => (x : R4) 1 := (continuous_apply 1).comp continuous_subtype_val
  exact Complex.equivRealProdCLM.symm.continuous.comp (h0.prodMk h1)

/-- The angle map to the circle. -/
def angleU (x : holeU) : Circle := ⟨zU x / ‖zU x‖, by simp [Submonoid.unitSphere, zU_ne x]⟩

lemma continuous_angleU : Continuous angleU :=
  Continuous.subtype_mk (continuous_zU.div (Complex.continuous_ofReal.comp continuous_zU.norm)
    fun y => by simpa using zU_ne y) _

/-- The unit circle in the `x⁰x¹`-plane. -/
def ℓU (θ : ℝ) : R4 := ![Real.cos θ, Real.sin θ, 0, 0]

lemma ℓU_mem (θ : ℝ) : ℓU θ ∈ holeU := by
  by_cases h : Real.cos θ = 0
  · refine Or.inr ?_
    show Real.sin θ ≠ 0
    intro hs
    have := Real.sin_sq_add_cos_sq θ
    rw [h, hs] at this
    norm_num at this
  · exact Or.inl h

lemma angleU_ℓ (θ : ℝ) : angleU ⟨ℓU θ, ℓU_mem θ⟩ = Circle.exp θ := by
  have hz : zU ⟨ℓU θ, ℓU_mem θ⟩ = Complex.exp (θ * Complex.I) := by
    rw [Complex.exp_mul_I]
    refine Complex.ext ?_ ?_
    · simp [zU, ℓU, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · simp [zU, ℓU, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Subtype.ext
  show zU _ / ‖zU _‖ = _
  rw [hz, Complex.norm_exp_ofReal_mul_I]
  simp [Circle.coe_exp]

lemma continuous_ℓU : Continuous ℓU := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [ℓU] <;> fun_prop

def baseU : holeU := ⟨ℓU 0, ℓU_mem 0⟩

/-- The loop around the plane. -/
def loopU : Path baseU baseU where
  toFun t := ⟨ℓU (2 * Real.pi * t), ℓU_mem _⟩
  continuous_toFun := (continuous_ℓU.comp (continuous_const.mul continuous_subtype_val)).subtype_mk _
  source' := by apply Subtype.ext; simp [baseU]
  target' := by
    apply Subtype.ext
    simp only [Set.Icc.coe_one, mul_one, baseU]
    funext i; fin_cases i <;> simp [ℓU]

/-- **The loop around the plane is not null-homotopic in `holeU`.** -/
theorem loopU_not_nullHomotopic : ¬ Path.Homotopic loopU (Path.refl baseU) := by
  intro hhom
  let A : C(holeU, Circle) := ⟨angleU, continuous_angleU⟩
  obtain ⟨H⟩ := hhom.map A
  let γ₀ : C(unitInterval, Circle) := (loopU.map A.continuous).toContinuousMap
  let γ₁ : C(unitInterval, Circle) := ((Path.refl baseU).map A.continuous).toContinuousMap
  have hrel : γ₀.HomotopicRel γ₁ {0, 1} := ⟨H⟩
  have h1 : γ₀ 0 = Circle.exp (0 : ℝ) := by
    show angleU (loopU 0) = _
    rw [loopU.source]; exact angleU_ℓ 0
  have h2 : γ₁ 0 = Circle.exp (0 : ℝ) := angleU_ℓ 0
  have hend := Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel hrel 0 h1 h2
  let Γ₀ : C(unitInterval, ℝ) := ⟨fun t => 2 * Real.pi * t, continuous_const.mul continuous_subtype_val⟩
  let Γ₁ : C(unitInterval, ℝ) := ContinuousMap.const _ 0
  have e₀ : Γ₀ = Circle.isCoveringMap_exp.liftPath γ₀ 0 h1 := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, by simp [Γ₀]⟩
    exact (angleU_ℓ (2 * Real.pi * t)).symm
  have e₁ : Γ₁ = Circle.isCoveringMap_exp.liftPath γ₁ 0 h2 := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, rfl⟩
    exact (angleU_ℓ 0).symm
  rw [← e₀, ← e₁] at hend
  have : (2 * Real.pi * ((1 : unitInterval) : ℝ)) = 0 := hend
  simp at this

/-- **`ℝ⁴ ∖ plane` is not simply connected.** -/
theorem not_simplyConnected_holeU : ¬ SimplyConnectedSpace holeU := fun _ =>
  loopU_not_nullHomotopic (SimplyConnectedSpace.paths_homotopic _ _)

end HoleAngle

/-- The hole instance is not vacuous: its cover is nonempty. -/
lemma nonempty_tilde_hole : Nonempty (Ytilde holeU) := nonempty_tilde baseU

end

end GU.Library
