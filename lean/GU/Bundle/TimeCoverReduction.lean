/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.LorentzPaths

/-!
# Phase 6, item 1: the `SO₀`-reduction on the time-orientation cover, for general `X`

(This closes the general-X clause of Phase 5 item 5, recorded there as path (b).)

* **`Tz_eq_TP`**: the trivialisation of `C` at `y₀` acts on the fibre over `y` as `TP J`, with `J` the
  Jacobian from the preferred chart at `y` to the one at `y₀`.
* **`redT X`**: a pulled-back frame `(p, q)` is in the reduction iff `q` is in the `SO₀`-orbit of a Lorentz
  frame of the metric whose time covector lies in the future cone of `p`.
* **`redT_reduction`**: it is clopen, `SO₀`-stable, meets every fibre and is one `SO₀`-coset per fibre.
  No hypothesis on `X`.

Independence of the choice of frame is `lorO_mem_SO0` (orthochronous Lorentz transformations act
through `SO₀`), not convexity of the cone; `mem_redT_iff_cT` recovers the planned description (on each
sheet, the `SO₀`-orbit of the gauge frame of a chart covector). `convex_futureX` is the convexity for
general `X`; it is proved but not used. `redT_reduction_R4` is the instance over `ℝ⁴`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### The trivialisation of `C` is `TP` of a Jacobian -/

lemma toCLM_mat (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : toCLM (mat T) = T := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [toCLM_apply, mat, LinearMap.toMatrix'_mulVec]
  rfl

/-- The chart change, as a matrix, between two charts at `x`. -/
def ccM (i j : atlas (Fin 4 → ℝ) X) (x : X) : M4 := mat ((Zt X).coordChange i j x)

lemma ccM_mul {i j k : atlas (Fin 4 → ℝ) X} {x : X} (hi : x ∈ (Zt X).baseSet i)
    (hj : x ∈ (Zt X).baseSet j) (hk : x ∈ (Zt X).baseSet k) :
    ccM j k x * ccM i j x = ccM i k x := by
  unfold ccM
  rw [← mat_comp]
  congr 1
  ext v : 1
  exact (Zt X).coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩ v

lemma ccM_self {i : atlas (Fin 4 → ℝ) X} {x : X} (hi : x ∈ (Zt X).baseSet i) : ccM i i x = 1 := by
  unfold ccM
  have h : (Zt X).coordChange i i x = ContinuousLinearMap.id ℝ _ := by
    ext w : 1; exact (Zt X).coordChange_self i x hi w
  rw [h]; exact mat_id

lemma isUnit_ccM {i j : atlas (Fin 4 → ℝ) X} {x : X} (hi : x ∈ (Zt X).baseSet i)
    (hj : x ∈ (Zt X).baseSet j) : IsUnit (ccM i j x) :=
  IsUnit.of_mul_eq_one (ccM j i x) (by rw [ccM_mul hj hi hj, ccM_self hj])

lemma ccM_inv {i j : atlas (Fin 4 → ℝ) X} {x : X} (hi : x ∈ (Zt X).baseSet i)
    (hj : x ∈ (Zt X).baseSet j) : (ccM i j x)⁻¹ = ccM j i x :=
  Matrix.inv_eq_right_inv (by rw [ccM_mul hj hi hj, ccM_self hj])

lemma cotriv_apply (x0 x : X) (w : (Fin 4 → ℝ) →L[ℝ] ℝ) (hx : x ∈ (Zt X).baseSet ((Zt X).indexAt x0)) :
    ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ)
        (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ) x0) ⟨x, w⟩).2 =
      w.comp ((Zt X).coordChange ((Zt X).indexAt x0) ((Zt X).indexAt x) x) := by
  have h1 : ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ)
        (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ) x0) ⟨x, w⟩).2 =
      ((trivializationAt ℝ (Bundle.Trivial X ℝ) x0).continuousLinearMapAt ℝ x).comp
        (w.comp ((trivializationAt (Fin 4 → ℝ) (Zt X).Fiber x0).symmL ℝ x)) := rfl
  rw [h1, VectorBundleCore.trivializationAt_symmL]
  · ext v
    simp
  · exact hx

lemma mem_base_of_Cb {y0 y : Yobs X} (hz : y ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) :
    πY y ∈ (Zt X).baseSet ((Zt X).indexAt (πY y0)) := by
  rw [Cb_baseSet] at hz
  exact hz

/-- The Jacobian from the preferred chart at `y` to the one at `y₀`. -/
def jacM (y0 y : Yobs X) : M4 := ccM ((Zt X).indexAt (πY y)) ((Zt X).indexAt (πY y0)) (πY y)

lemma isUnit_jacM {y0 y : Yobs X} (hz : y ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) :
    IsUnit (jacM y0 y) :=
  isUnit_ccM ((Zt X).mem_baseSet_at _) (mem_base_of_Cb hz)

/-- **The trivialisation of `C` is `TP` of the Jacobian.** -/
theorem Tz_eq_TP (y0 y : Yobs X) (hz : y ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet)
    (u : CFib) : Tz y0 y hz u = TP (jacM y0 y) (isUnit_jacM hz) u := by
  have hx := mem_base_of_Cb hz
  refine Prod.ext ?_ ?_
  · rw [Tz_fst']
    rfl
  · rw [Tz_snd', cotriv_apply _ _ _ hx]
    show _ = u.2.comp (toCLM (jacM y0 y)⁻¹)
    rw [jacM, ccM_inv ((Zt X).mem_baseSet_at _) hx, ccM, toCLM_mat]

lemma TP_congr {A B : M4} (e : A = B) (hA : IsUnit A) (hB : IsUnit B) (u : CFib) :
    TP A hA u = TP B hB u := by
  subst e; rfl

/-! ### Frames given by Lorentz matrices in the preferred chart -/

/-- `P` is a Lorentz frame of the contravariant metric `G`. -/
def IsLF (G P : M4) : Prop := IsUnit P ∧ G = P * ηR * Pᵀ

/-- The frame of `C` over `y` given by `P` in the preferred chart. -/
def rawF (y : Yobs X) (P : M4) : HomTotM X := ⟨y, tpF P⟩

lemma rawF_mem {y : Yobs X} {P : M4} (h : IsLF (Gpt y) P) : rawF y P ∈ OFr X := by
  have := tpFrame_mem y P h.1 h.2
  rw [rawF, tpF_of_unit h.1]
  exact this.1

/-- As a point of `OFr`. -/
def rawO (y : Y13o X) (P : M4) (h : IsLF (Gpt (y : Yobs X)) P) : OFr X := ⟨rawF y P, rawF_mem h⟩

lemma projOFr_rawO (y : Y13o X) (P : M4) (h : IsLF (Gpt (y : Yobs X)) P) : projOFr (rawO y P h) = y :=
  rfl

/-- **Raw frames built in a fixed chart `i` are continuous**, although the preferred chart jumps. -/
theorem continuousOn_rawF {Z : Type*} [TopologicalSpace Z] {S : Set Z} (hS : IsOpen S)
    {y : Z → Yobs X} (hy : Continuous y) (i : atlas (Fin 4 → ℝ) X)
    (hi : ∀ z ∈ S, πY (y z) ∈ (Zt X).baseSet i) {Q : Z → M4} (hQ : ContinuousOn Q S)
    (hu : ∀ z ∈ S, IsUnit (Q z)) :
    ContinuousOn (fun z => rawF (y z) ((ccM ((Zt X).indexAt (πY (y z))) i (πY (y z)))⁻¹ * Q z)) S := by
  intro z0 hz0
  refine ContinuousAt.continuousWithinAt ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hy.continuousAt, ?_⟩
  set y0 := y z0
  set i0 := (Zt X).indexAt (πY y0)
  have hπ : Continuous fun z => πY (y z) :=
    (FiberBundle.continuous_proj _ _).comp (continuous_subtype_val.comp hy)
  set S' := S ∩ (fun z => πY (y z)) ⁻¹' (Zt X).baseSet i0
  have hS' : IsOpen S' := hS.inter (((Zt X).isOpen_baseSet i0).preimage hπ)
  have hz0' : z0 ∈ S' := ⟨hz0, (Zt X).mem_baseSet_at _⟩
  have hbase : ∀ z ∈ S', y z ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet := by
    intro z hz
    rw [Cb_baseSet]
    exact hz.2
  -- in the trivialisation at `y0` the frame is `tpF (ccM i i0 x * Q z)`
  have hform : ∀ z ∈ S', ((trivializationAt HomF (HomCb (X := X)) y0)
      (rawF (y z) ((ccM ((Zt X).indexAt (πY (y z))) i (πY (y z)))⁻¹ * Q z))).2 =
      tpF (ccM i i0 (πY (y z)) * Q z) := by
    intro z hz
    have hx := hz.2
    have hxi := hi z hz.1
    have hxx := (Zt X).mem_baseSet_at (πY (y z))
    have hJu : IsUnit ((ccM ((Zt X).indexAt (πY (y z))) i (πY (y z)))⁻¹) := by
      rw [ccM_inv hxx hxi]; exact isUnit_ccM hxi hxx
    have hR := (hJu.mul (hu z hz.1))
    rw [triv_apply y0 _ (hbase z hz)]
    refine ContinuousLinearMap.ext fun v => ?_
    show Tz y0 (y z) (hbase z hz) (tpF _ v) = tpF _ v
    rw [Tz_eq_TP, tpF_of_unit hR, tpF_of_unit ((isUnit_ccM hxi hx).mul (hu z hz.1)), tpFrame_apply,
      tpFrame_apply, ← TP_mul]
    have e : jacM y0 (y z) * ((ccM ((Zt X).indexAt (πY (y z))) i (πY (y z)))⁻¹ * Q z) =
        ccM i i0 (πY (y z)) * Q z := by
      rw [jacM, ccM_inv hxx hxi, ← Matrix.mul_assoc, ccM_mul hxi hxx hx]
    exact TP_congr e _ _ _
  have hcc : ContinuousOn (fun z => ccM i i0 (πY (y z))) S' := by
    have h1 := ((Zt X).continuousOn_coordChange i i0)
    exact continuous_mat.comp_continuousOn (h1.comp hπ.continuousOn fun z hz => ⟨hi z hz.1, hz.2⟩)
  have hT : ContinuousOn (fun z => tpF (ccM i i0 (πY (y z)) * Q z)) S' :=
    continuousOn_tpF (hcc.mul (hQ.mono Set.inter_subset_left)) fun z hz =>
      (isUnit_ccM (hi z hz.1) hz.2).mul (hu z hz.1)
  exact (hT.continuousAt (hS'.mem_nhds hz0')).congr
    (Filter.eventuallyEq_of_mem (hS'.mem_nhds hz0') fun z hz => (hform z hz).symm)

/-! ### The transition between two frames -/

open Classical in
/-- The element of `O(7,7)` taking `a` to `b` (over the same point). -/
def transO (a b : OFr X) : O77 :=
  if h : projOFr a = projOFr b then (exists_act_eq a b h).choose else 1

lemma transO_spec {a b : OFr X} (h : projOFr a = projOFr b) : actOFr' a (transO a b) = b := by
  classical
  unfold transO; rw [dif_pos h]; exact (exists_act_eq a b h).choose_spec

lemma transO_unique {a b : OFr X} (h : projOFr a = projOFr b) {g : O77} (hg : actOFr' a g = b) :
    transO a b = g :=
  actOFr'_cancel ((transO_spec h).trans hg.symm)

/-- **The transition between two continuous frames over the same points is continuous.** -/
theorem continuousOn_transO {Z : Type*} [TopologicalSpace Z] {S : Set Z} (hS : IsOpen S)
    {a b : Z → OFr X} (ha : ContinuousOn a S) (hb : Continuous b)
    (hab : ∀ z ∈ S, projOFr (a z) = projOFr (b z)) :
    ContinuousOn (fun z => transO (a z) (b z)) S := by
  intro z0 hz0
  refine ContinuousAt.continuousWithinAt ?_
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨V', hV', hz₀, σ', τ', -, -, hτ', hrec⟩ :=
    (frameBundle (X := X)).locTriv (projOFr (b z0))
  have hτc : ContinuousOn τ' (projOFr ⁻¹' V') := hτ'.continuousOn
  set N : Set Z := S ∩ (fun z => projOFr (b z)) ⁻¹' V'
  have hN : IsOpen N := hS.inter (hV'.preimage (continuous_projOFr.comp hb))
  have hmem : N ∈ 𝓝 z0 := hN.mem_nhds ⟨hz0, hz₀⟩
  have hform : ∀ z ∈ N, transO (a z) (b z) = (τ' (a z))⁻¹ * τ' (b z) := by
    intro z hz
    apply transO_unique (hab z hz.1)
    set y := projOFr (b z)
    have hy : projOFr (a z) = y := hab z hz.1
    have e1 : actOFr' (σ' y) (τ' (a z)) = a z := by
      have := hrec (a z) (by show projOFr (a z) ∈ V'; rw [hy]; exact hz.2)
      rw [show (frameBundle (X := X)).proj (a z) = y from hy] at this
      exact this
    calc actOFr' (a z) ((τ' (a z))⁻¹ * τ' (b z))
        = actOFr' (actOFr' (σ' y) (τ' (a z))) ((τ' (a z))⁻¹ * τ' (b z)) := by rw [e1]
      _ = actOFr' (σ' y) (τ' (b z)) := by rw [actOFr'_mul, mul_inv_cancel_left]
      _ = b z := hrec (b z) hz.2
  have h1 : ContinuousOn (fun z => τ' (a z)) N :=
    hτc.comp (ha.mono Set.inter_subset_left) fun z hz => by
      show projOFr (a z) ∈ V'
      rw [hab z hz.1]; exact hz.2
  have h2 : ContinuousOn (fun z => τ' (b z)) N := hτc.comp hb.continuousOn fun z hz => hz.2
  exact ((h1.inv.mul h2).congr hform).continuousAt hmem


/-! ### Time covectors of Lorentz frames -/

/-- The time covector of a frame: `P⁻ᵀ e₀`. -/
def tcov (P : M4) : R4 := (Pᵀ)⁻¹ *ᵥ Pi.single 0 1

lemma tr_mulVec_tcov {P : M4} (h : IsUnit P) : Pᵀ *ᵥ tcov P = Pi.single 0 1 := by
  rw [tcov, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' h)), Matrix.one_mulVec]

lemma eta_e0 : (ηR : M4) *ᵥ (Pi.single 0 1 : R4) = Pi.single 0 1 := by
  rw [GU.Iso77.ηR_eq, ηr]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]

/-- **The pairing of two time covectors is the `00` entry of the Lorentz transformation between the
frames.** -/
lemma lp_tcov {G P P' : M4} (_h : IsLF G P) (h' : IsLF G P') :
    lp G (tcov P) (tcov P') = (P⁻¹ * P') 0 0 := by
  have hv : G *ᵥ tcov P' = P' *ᵥ Pi.single 0 1 := by
    rw [h'.2, ← Matrix.mulVec_mulVec, tr_mulVec_tcov h'.1, ← Matrix.mulVec_mulVec, eta_e0]
  unfold lp
  rw [hv, tcov, Matrix.dotProduct_mulVec, ← Matrix.transpose_nonsing_inv, Matrix.mulVec_transpose,
    Matrix.vecMul_vecMul]
  simp [dotProduct, Matrix.vecMul, Pi.single_apply]

lemma timelike_tcov {G P : M4} (h : IsLF G P) : 0 < lp G (tcov P) (tcov P) := by
  rw [lp_tcov h h, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h.1)]
  simp

lemma isLorentz_frames {G P P' : M4} (h : IsLF G P) (h' : IsLF G P') : IsLorentz (P⁻¹ * P') := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp h.1
  unfold IsLorentz
  rw [transpose_mul, transpose_nonsing_inv]
  calc P⁻¹ * P' * ηR * (P'ᵀ * Pᵀ⁻¹) = P⁻¹ * (P' * ηR * P'ᵀ) * Pᵀ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P⁻¹ * (P * ηR * Pᵀ) * Pᵀ⁻¹ := by rw [← h'.2, h.2]
    _ = (P⁻¹ * P) * ηR * (Pᵀ * Pᵀ⁻¹) := by simp only [Matrix.mul_assoc]
    _ = ηR := by
      rw [Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hd)]
      simp

lemma tpF_congr {A B : M4} (e : A = B) : tpF A = tpF B := by rw [e]

/-- **Two Lorentz frames of the same metric differ by `lorM` of the transformation between them.** -/
theorem rawO_act {y : Y13o X} {P P' : M4} (h : IsLF (Gpt (y : Yobs X)) P)
    (h' : IsLF (Gpt (y : Yobs X)) P') :
    actOFr' (rawO y P h) (lorO (P⁻¹ * P') (isLorentz_frames h h')) = rawO y P' h' := by
  have hL := isLorentz_frames h h'
  apply Subtype.ext
  show (⟨(y : Yobs X), (tpF P).comp (matCLM (lorM (P⁻¹ * P')))⟩ : HomTotM X) = ⟨y, tpF P'⟩
  rw [tpF_of_unit h.1, tpFrame_mul h.1 hL.isUnit, ← tpF_of_unit (h.1.mul hL.isUnit),
    tpF_congr (show P * (P⁻¹ * P') = P' by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h.1),
        Matrix.one_mul])]

/-- Frames whose time covectors pair positively differ by an element of `SO₀`. -/
theorem lorO_frames_mem {G P P' : M4} (h : IsLF G P) (h' : IsLF G P')
    (hp : 0 < lp G (tcov P) (tcov P')) : lorO (P⁻¹ * P') (isLorentz_frames h h') ∈ SO0 :=
  lorO_mem_SO0 _ (by rw [← lp_tcov h h']; exact hp)

/-- Two covectors in one future cone pair positively. -/
lemma lp_pos_of_future {p : Ytilde X} {u v : R4} (hu : u ∈ future p) (hv : v ∈ future p) :
    0 < lp (Gpt (p.proj : Yobs X)) u v := by
  obtain ⟨Q, -, hG⟩ := p.proj.2
  have hr := timelike_rep p
  have h1 := (side_iff hG hr hu.1 hv.1 (by rw [lp_comm hG]; exact hu.2)).mp hv.2
  rw [lp_comm hG]; exact h1

/-! ### The reduction -/

/-- **The `SO₀`-reduction on the cover**: `(p, q)` such that `q` is in the `SO₀`-orbit of a Lorentz
frame whose time covector is future for `p`. -/
def redT (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Set (OFrT X) :=
  {z | ∃ P, ∃ h : IsLF (Gpt (piT z.1.1 : Yobs X)) P, tcov P ∈ future z.1.1 ∧
    ∃ g ∈ SO0, actOFr' (rawO (piT z.1.1) P h) g = z.1.2}

lemma redT_iff {z : OFrT X} {P : M4} (h : IsLF (Gpt (piT z.1.1 : Yobs X)) P) (hf : tcov P ∈ future z.1.1) :
    z ∈ redT X ↔ transO (rawO (piT z.1.1) P h) z.1.2 ∈ SO0 := by
  have hproj : projOFr (rawO (piT z.1.1) P h) = projOFr z.1.2 := z.2
  constructor
  · rintro ⟨P', h', hf', g, hg, hq⟩
    have hL := isLorentz_frames h h'
    have hm := lorO_frames_mem h h' (lp_pos_of_future hf hf')
    have : transO (rawO (piT z.1.1) P h) z.1.2 = lorO (P⁻¹ * P') hL * g := by
      apply transO_unique hproj
      rw [← actOFr'_mul, rawO_act h h', hq]
    rw [this]
    exact mul_mem hm hg
  · intro hm
    exact ⟨P, h, hf, _, hm, transO_spec hproj⟩

/-- The time flip. -/
def tflip : M4 := Matrix.diagonal ![-1, 1, 1, 1]

lemma tflip_mul_self : tflip * tflip = 1 := by
  rw [tflip, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; fin_cases i <;> simp

lemma isLF_tflip {G Q : M4} (h : IsLF G Q) : IsLF G (Q * tflip) := by
  refine ⟨h.1.mul (IsUnit.of_mul_eq_one _ tflip_mul_self), ?_⟩
  rw [h.2, transpose_mul]
  have : tflip * ηR * tflipᵀ = ηR := by
    rw [GU.Iso77.ηR_eq, ηr, tflip, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext i; fin_cases i <;> simp
  calc Q * ηR * Qᵀ = Q * (tflip * ηR * tflipᵀ) * Qᵀ := by rw [this]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma tcov_tflip {Q : M4} (h : IsUnit Q) : tcov (Q * tflip) = -tcov Q := by
  have hu := isUnit_transpose' (h.mul (IsUnit.of_mul_eq_one _ tflip_mul_self))
  apply (Matrix.mulVec_injective_of_isUnit hu)
  rw [tr_mulVec_tcov (h.mul (IsUnit.of_mul_eq_one _ tflip_mul_self)), Matrix.mulVec_neg,
    transpose_mul, ← Matrix.mulVec_mulVec, tr_mulVec_tcov h]
  ext i; fin_cases i <;> simp [tflip, Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]

/-- Every point of the cover has a Lorentz frame whose time covector is future. -/
lemma exists_future_frame (p : Ytilde X) :
    ∃ P, ∃ _ : IsLF (Gpt (p.proj : Yobs X)) P, tcov P ∈ future p := by
  obtain ⟨Q, hQ, hG⟩ := p.proj.2
  have hLF : IsLF (Gpt (p.proj : Yobs X)) Q := ⟨hQ, hG⟩
  have ht := timelike_tcov hLF
  rcases mem_futureCone_or (timelike_rep p) ht with h | h
  · exact ⟨Q, hLF, h⟩
  · refine ⟨Q * tflip, isLF_tflip hLF, ?_⟩
    rw [tcov_tflip hQ]
    refine ⟨by rw [lp_neg_left, lp_neg_right, neg_neg]; exact ht, ?_⟩
    have := h.2
    rw [lp_neg_right] at this
    rw [lp_neg_left]; linarith

/-! ### Local frames from a chart covector -/

/-- The chart-local Lorentz frame (in chart `I.1`) built from the covector `I.2`. -/
def hatP (I : TimeIdx X) (y : Y13o X) : M4 :=
  (quat I.2)⁻¹ * gaugeP (quat I.2 * chartG I.1 y * (quat I.2)ᵀ)

/-- The same frame in the preferred chart. -/
def locP (I : TimeIdx X) (y : Y13o X) : M4 :=
  (ccM ((Zt X).indexAt (baseX y)) I.1 (baseX y))⁻¹ * hatP I y

lemma transMat_eq (i : atlas (Fin 4 → ℝ) X) (x : X) : transMat i x = ccM ((Zt X).indexAt x) i x := rfl

lemma lp_chartG {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) : 0 < lp (chartG I.1 y) I.2 I.2 := by
  have h := hy.2
  rw [tb_eq hy.1 hy.1] at h
  have e : mat ((Zt X).coordChange I.1 I.1 (baseX y)) = 1 := ccM_self hy.1
  rwa [e, Matrix.transpose_one, Matrix.one_mulVec] at h

lemma chartG_eq {I : TimeIdx X} {y : Y13o X} {Q : M4} (hG : Gpt (y : Yobs X) = Q * ηR * Qᵀ) :
    chartG I.1 y = (transMat I.1 (baseX y) * Q) * ηR * (transMat I.1 (baseX y) * Q)ᵀ := by
  rw [chartG, hG, transpose_mul]; simp only [Matrix.mul_assoc]

lemma xi_ne {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) : I.2 ≠ 0 := by
  intro h
  have := lp_chartG hy
  rw [h] at this; simp [lp] at this

lemma conj_mem_gaugeSet {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) :
    quat I.2 * chartG I.1 y * (quat I.2)ᵀ ∈ gaugeSet := by
  obtain ⟨Q, hQ, hG⟩ := y.2
  have hJ : IsUnit (transMat I.1 (baseX y)) :=
    isUnit_ccM ((Zt X).mem_baseSet_at _) hy.1
  have hu := (isUnit_quat (xi_ne hy)).mul (hJ.mul hQ)
  have hr : quat I.2 * chartG I.1 y * (quat I.2)ᵀ =
      (quat I.2 * (transMat I.1 (baseX y) * Q)) * ηR * (quat I.2 * (transMat I.1 (baseX y) * Q))ᵀ := by
    rw [chartG_eq hG, transpose_mul (quat I.2)]; simp only [Matrix.mul_assoc]
  refine (mem_gaugeSet_iff hu hr).mpr ?_
  rw [quat_conj_zero]
  exact lp_chartG hy

lemma chartG_symm (I : TimeIdx X) (y : Y13o X) : (chartG I.1 y).IsSymm := by
  obtain ⟨Q, -, hG⟩ := y.2
  rw [chartG_eq hG]; exact symm_conj _

lemma isUnit_gauge_conj {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) :
    IsUnit (gaugeP (quat I.2 * chartG I.1 y * (quat I.2)ᵀ)) := by
  obtain ⟨Q, hQ, hG⟩ := y.2
  have hJ : IsUnit (transMat I.1 (baseX y)) := isUnit_ccM ((Zt X).mem_baseSet_at _) hy.1
  have hsym : (quat I.2 * chartG I.1 y * (quat I.2)ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (chartG_symm I y).eq, Matrix.mul_assoc]
  have h := gaugeP_eq hsym (conj_mem_gaugeSet hy)
  have hu := (isUnit_quat (xi_ne hy)).mul (hJ.mul hQ)
  refine isUnit_of_eta_eq hu (h.trans ?_)
  rw [chartG_eq hG, transpose_mul (quat I.2)]; simp only [Matrix.mul_assoc]

lemma hatP_eq {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) :
    hatP I y * ηR * (hatP I y)ᵀ = chartG I.1 y := by
  have hsym : (quat I.2 * chartG I.1 y * (quat I.2)ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (chartG_symm I y).eq, Matrix.mul_assoc]
  have hL := gaugeP_eq hsym (conj_mem_gaugeSet hy)
  set q := quat I.2
  set A := gaugeP (q * chartG I.1 y * qᵀ)
  have hd : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_quat (xi_ne hy))
  unfold hatP
  rw [transpose_mul, transpose_nonsing_inv]
  calc q⁻¹ * A * ηR * (Aᵀ * qᵀ⁻¹) = q⁻¹ * (A * ηR * Aᵀ) * qᵀ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = q⁻¹ * (q * chartG I.1 y * qᵀ) * qᵀ⁻¹ := by rw [hL]
    _ = (q⁻¹ * q) * chartG I.1 y * (qᵀ * qᵀ⁻¹) := by simp only [Matrix.mul_assoc]
    _ = chartG I.1 y := by
      rw [Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hd)]
      simp

lemma isUnit_hatP {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) : IsUnit (hatP I y) :=
  (Matrix.isUnit_nonsing_inv_iff.mpr (isUnit_quat (xi_ne hy))).mul (isUnit_gauge_conj hy)

/-- **The local frame is a Lorentz frame of the metric.** -/
lemma isLF_locP {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) : IsLF (Gpt (y : Yobs X)) (locP I y) := by
  have hJ : IsUnit (transMat I.1 (baseX y)) := isUnit_ccM ((Zt X).mem_baseSet_at _) hy.1
  have hd : IsUnit (transMat I.1 (baseX y)).det := (Matrix.isUnit_iff_isUnit_det _).mp hJ
  refine ⟨(Matrix.isUnit_nonsing_inv_iff.mpr hJ).mul (isUnit_hatP hy), ?_⟩
  unfold locP
  rw [← transMat_eq, transpose_mul, transpose_nonsing_inv]
  set J := transMat I.1 (baseX y)
  calc Gpt (y : Yobs X) = (J⁻¹ * J) * Gpt (y : Yobs X) * (Jᵀ * Jᵀ⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hd)]
        simp
    _ = J⁻¹ * chartG I.1 y * Jᵀ⁻¹ := by rw [chartG]; simp only [Matrix.mul_assoc]; rfl
    _ = J⁻¹ * (hatP I y * ηR * (hatP I y)ᵀ) * Jᵀ⁻¹ := by rw [hatP_eq hy]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma gaugeP_row0 (G : M4) (j : Fin 4) (hj : j ≠ 0) : gaugeP G 0 j = 0 := by
  fin_cases j <;> simp_all [gaugeP]

lemma gaugeP_00_pos {G : M4} (h : G ∈ gaugeSet) : 0 < gaugeP G 0 0 := by
  simp [gaugeP]; exact h.1

/-- **The time covector of the local frame is a positive multiple of the chart covector.** -/
lemma tcov_locP {I : TimeIdx X} {y : Y13o X} (hy : y ∈ tV I) :
    tcov (locP I y) = (gaugeP (quat I.2 * chartG I.1 y * (quat I.2)ᵀ) 0 0)⁻¹ • cov I (baseX y) := by
  have hu := (isLF_locP hy).1
  have hA := gaugeP_00_pos (conj_mem_gaugeSet hy)
  have hJ : IsUnit (transMat I.1 (baseX y)) := isUnit_ccM ((Zt X).mem_baseSet_at _) hy.1
  apply Matrix.mulVec_injective_of_isUnit (isUnit_transpose' hu)
  rw [tr_mulVec_tcov hu, Matrix.mulVec_smul]
  have hJJ : ((transMat I.1 (baseX y))ᵀ)⁻¹ *ᵥ ((transMat I.1 (baseX y))ᵀ *ᵥ I.2) = I.2 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' hJ)), Matrix.one_mulVec]
  have hq : (quat I.2)ᵀ *ᵥ (Pi.single 0 1 : R4) = I.2 := by
    ext i; fin_cases i <;> simp [quat, Matrix.mulVec, dotProduct, Pi.single_apply, Fin.sum_univ_four]
  have hq' : ((quat I.2)ᵀ)⁻¹ *ᵥ I.2 = Pi.single 0 1 := by
    have := congrArg (fun v => ((quat I.2)ᵀ)⁻¹ *ᵥ v) hq
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' (isUnit_quat (xi_ne hy)))), Matrix.one_mulVec] at this
    exact this.symm
  have hrow : ∀ G : M4, (gaugeP G)ᵀ *ᵥ (Pi.single 0 1 : R4) = gaugeP G 0 0 • Pi.single 0 1 := by
    intro G
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply, Fin.sum_univ_four, gaugeP]
  have h1 : (locP I y)ᵀ *ᵥ cov I (baseX y) =
      gaugeP (quat I.2 * chartG I.1 y * (quat I.2)ᵀ) 0 0 • (Pi.single 0 1 : R4) := by
    unfold locP hatP cov
    rw [← transMat_eq, transpose_mul, transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      transpose_nonsing_inv, transpose_nonsing_inv, hJJ, hq', hrow]
  rw [h1, smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
/-! ### Convexity, for general `X` -/

/-- **Future cones are convex**, for general `X`. -/
theorem convex_futureX (p : Ytilde X) : Convex ℝ (future p) := by
  obtain ⟨P, -, hG⟩ := p.proj.2
  have hr := timelike_rep p
  rintro v ⟨hv, hvr⟩ w ⟨hw, hwr⟩ a b ha hb hab
  set G := Gpt (p.proj : Yobs X) with hGdef
  have hvw : 0 < lp G v w :=
    (side_iff hG hr hw hv (by rw [lp_comm hG]; exact hwr)).mp hvr
  refine ⟨?_, ?_⟩
  · rw [lp_comb_left, lp_comb_right, lp_comb_right, lp_comm hG w v]
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      simpa using hw
    · have h1 : 0 < a * (a * lp G v v) := mul_pos h (mul_pos h hv)
      have h2 : 0 ≤ a * (b * lp G v w) := mul_nonneg ha (mul_nonneg hb hvw.le)
      have h3 : 0 ≤ b * (a * lp G v w) := mul_nonneg hb (mul_nonneg ha hvw.le)
      have h4 : 0 ≤ b * (b * lp G w w) := mul_nonneg hb (mul_nonneg hb hw.le)
      linarith
  · rw [lp_comb_left]
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      simpa using hwr
    · have h1 : 0 < a * lp G v (rep p) := mul_pos h hvr
      have h2 : 0 ≤ b * lp G w (rep p) := mul_nonneg hb hwr.le
      linarith


lemma smul_mem_future {p : Ytilde X} {v : R4} (hv : v ∈ future p) {c : ℝ} (hc : 0 < c) :
    c • v ∈ future p := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · have : lp (Gpt (p.proj : Yobs X)) (c • v) (c • v) = c * (c * lp (Gpt (p.proj : Yobs X)) v v) := by
      simp only [lp, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [this]; positivity
  · have : lp (Gpt (p.proj : Yobs X)) (c • v) (rep p) = c * lp (Gpt (p.proj : Yobs X)) v (rep p) := by
      simp [lp, smul_dotProduct]
    rw [this]; positivity

/-! ### Clopenness -/

open Classical in
/-- The local reference frame on `{z | piT z ∈ tV I}`. -/
def locF (I : TimeIdx X) (z : OFrT X) : OFr X :=
  if h : piT z.1.1 ∈ tV I then rawO (piT z.1.1) (locP I (piT z.1.1)) (isLF_locP h) else z.1.2

/-- The domain of the chart `I`, on the pulled-back frames. -/
def domT (I : TimeIdx X) : Set (OFrT X) := {z | piT z.1.1 ∈ tV I}

lemma continuous_piT_T : Continuous fun z : OFrT X => piT z.1.1 :=
  continuous_piT.comp (continuous_fst.comp continuous_subtype_val)

lemma isOpen_domT (I : TimeIdx X) : IsOpen (domT I) := (isOpen_tV I).preimage continuous_piT_T

lemma continuousOn_hatP (I : TimeIdx X) : ContinuousOn (fun z : OFrT X => hatP I (piT z.1.1)) (domT I) := by
  have hc : ContinuousOn (fun z : OFrT X => chartG I.1 (piT z.1.1)) (domT I) :=
    (continuousOn_chartG I.1).comp continuous_piT_T.continuousOn fun z hz => hz.1
  have hconj : ContinuousOn (fun z : OFrT X => quat I.2 * chartG I.1 (piT z.1.1) * (quat I.2)ᵀ) (domT I) :=
    (continuousOn_const.mul hc).mul continuousOn_const
  have hg := continuousOn_gaugeP.comp hconj fun z hz => conj_mem_gaugeSet hz
  exact continuousOn_const.mul hg

lemma continuousOn_locF (I : TimeIdx X) : ContinuousOn (locF I) (domT I) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have h := continuousOn_rawF (isOpen_domT I) (y := fun z : OFrT X => ((piT z.1.1 : Y13o X) : Yobs X))
    (continuous_subtype_val.comp continuous_piT_T) I.1 (fun z hz => hz.1) (continuousOn_hatP I)
    (fun z hz => isUnit_hatP hz)
  refine h.congr fun z hz => ?_
  show ((locF I z : OFr X) : HomTotM X) = _
  unfold locF
  split_ifs with h'
  · rfl
  · exact absurd hz h'

/-- The transition from the local reference frame. -/
def cT (I : TimeIdx X) (z : OFrT X) : O77 := transO (locF I z) z.1.2

lemma continuousOn_cT (I : TimeIdx X) : ContinuousOn (cT I) (domT I) :=
  continuousOn_transO (isOpen_domT I) (continuousOn_locF I) (continuous_snd.comp continuous_subtype_val)
    fun z hz => by
      unfold locF
      split_ifs with h'
      · exact z.2
      · exact absurd hz h'

/-- The sheet of the chart covector. -/
def sheetT (I : TimeIdx X) : Set (OFrT X) :=
  domT I ∩ {z | ((tildeCore X).localTriv I z.1.1).2 = false}

lemma isOpen_sheetT (I : TimeIdx X) : IsOpen (sheetT I) := by
  have hcont : ContinuousOn (fun z : OFrT X => ((tildeCore X).localTriv I z.1.1).2) (domT I) := by
    have h := ((tildeCore X).localTriv I).continuousOn
    refine continuous_snd.comp_continuousOn (h.comp (continuous_fst.comp continuous_subtype_val).continuousOn
      fun z hz => ?_)
    rw [Trivialization.mem_source]; exact hz
  exact hcont.isOpen_inter_preimage (isOpen_domT I) (isOpen_discrete {false})

/-- **On a sheet, membership in the reduction is `cT ∈ SO₀`.** -/
lemma mem_redT_iff_cT {I : TimeIdx X} {z : OFrT X} (hz : z ∈ sheetT I) : z ∈ redT X ↔ cT I z ∈ SO0 := by
  have hd : piT z.1.1 ∈ tV I := hz.1
  have hfut : cov I (baseX (piT z.1.1)) ∈ future z.1.1 :=
    (mem_future_iff_localTriv I z.1.1 hd).mpr hz.2
  have hf : tcov (locP I (piT z.1.1)) ∈ future z.1.1 := by
    rw [tcov_locP hd]
    exact smul_mem_future hfut (inv_pos.mpr (gaugeP_00_pos (conj_mem_gaugeSet hd)))
  rw [redT_iff (isLF_locP hd) hf]
  unfold cT locF
  split_ifs
  rfl

/-- Every point lies on some sheet. -/
lemma exists_sheetT (z : OFrT X) : ∃ I : TimeIdx X, z ∈ sheetT I := by
  set p := z.1.1
  have hc : cov ((Zt X).indexAt (baseX p.proj), rep p) (baseX p.proj) = rep p := by
    show (transMat _ _)ᵀ *ᵥ rep p = rep p
    rw [Acc_self, Matrix.transpose_one, Matrix.one_mulVec]
  have hd : p.proj ∈ tV ((Zt X).indexAt (baseX p.proj), rep p) := by
    refine ⟨(Zt X).mem_baseSet_at _, ?_⟩
    show 0 < lp _ (cov _ (baseX p.proj)) (cov _ (baseX p.proj))
    rw [hc]; exact timelike_rep p
  refine ⟨((Zt X).indexAt (baseX p.proj), rep p), hd, (mem_future_iff_localTriv _ p hd).mp ?_⟩
  rw [hc]
  exact ⟨timelike_rep p, timelike_rep p⟩

theorem isClopen_redT : IsClopen (redT X) := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨I, hI⟩ := exists_sheetT z
    have hc : cT I z ∉ (SO0 : Set O77) := fun h => hz ((mem_redT_iff_cT hI).mpr h)
    refine ⟨sheetT I ∩ cT I ⁻¹' (SO0 : Set O77)ᶜ, fun w hw hwr => hw.2 ((mem_redT_iff_cT hw.1).mp hwr),
      ((continuousOn_cT I).mono Set.inter_subset_left).isOpen_inter_preimage (isOpen_sheetT I)
        isClosed_connectedComponent.isOpen_compl, hI, hc⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨I, hI⟩ := exists_sheetT z
    refine ⟨sheetT I ∩ cT I ⁻¹' (SO0 : Set O77), fun w hw => (mem_redT_iff_cT hw.1).mpr hw.2,
      ((continuousOn_cT I).mono Set.inter_subset_left).isOpen_inter_preimage (isOpen_sheetT I)
        isOpen_SO0, hI, (mem_redT_iff_cT hI).mp hz⟩

/-- **Item 1: the pulled-back frame bundle over the cover has a clopen `SO₀`-reduction, for every `X`.**
It is `SO₀`-stable, meets every fibre and is one `SO₀`-coset per fibre. Compare
`no_SO0_reduction_univ` on `Y13`. -/
theorem redT_reduction :
    IsClopen (redT X) ∧
      (∀ z ∈ redT X, ∀ g ∈ SO0, actT z g ∈ redT X) ∧
      (∀ p : Ytilde X, ∃ z ∈ redT X, z.1.1 = p) ∧
      (∀ z ∈ redT X, ∀ z' ∈ redT X, z.1.1 = z'.1.1 → ∃ g ∈ SO0, actT z g = z') := by
  refine ⟨isClopen_redT, ?_, ?_, ?_⟩
  · rintro z ⟨P, h, hf, g, hg, hq⟩ g' hg'
    exact ⟨P, h, hf, g * g', mul_mem hg hg', by
      show actOFr' (rawO (piT z.1.1) P h) (g * g') = actOFr' z.1.2 g'
      rw [← actOFr'_mul, hq]⟩
  · intro p
    obtain ⟨P, h, hf⟩ := exists_future_frame p
    exact ⟨⟨(p, rawO p.proj P h), rfl⟩, ⟨P, h, hf, 1, one_mem _, actOFr'_one _⟩, rfl⟩
  · rintro ⟨⟨p, q⟩, hz⟩ hzr ⟨⟨p', q'⟩, hz'⟩ hzr' hpp
    obtain rfl : p = p' := hpp
    obtain ⟨P, h, hf, -⟩ := id hzr
    have h1 := (redT_iff (z := ⟨(p, q), hz⟩) h hf).mp hzr
    have h2 := (redT_iff (z := ⟨(p, q'), hz'⟩) h hf).mp hzr'
    refine ⟨(transO (rawO (piT p) P h) q)⁻¹ * transO (rawO (piT p) P h) q', mul_mem (inv_mem h1) h2, ?_⟩
    apply Subtype.ext
    show (p, actOFr' q _) = (p, q')
    congr 1
    calc actOFr' q ((transO (rawO (piT p) P h) q)⁻¹ * transO (rawO (piT p) P h) q')
        = actOFr' (actOFr' (rawO (piT p) P h) (transO (rawO (piT p) P h) q))
            ((transO (rawO (piT p) P h) q)⁻¹ * transO (rawO (piT p) P h) q') := by
          rw [transO_spec (a := rawO (piT p) P h) (b := q) hz]
      _ = actOFr' (rawO (piT p) P h) (transO (rawO (piT p) P h) q') := by
          rw [actOFr'_mul, mul_inv_cancel_left]
      _ = q' := transO_spec hz'

/-- **The instance over `ℝ⁴`**: the general reduction, in the form of `exists_SO0_reduction_cover`. -/
theorem redT_reduction_R4 :
    ∃ Q : Set (OFrT R4), IsClopen Q ∧
      (∀ z ∈ Q, ∀ g ∈ SO0, actT z g ∈ Q) ∧
      (∀ p : Ytilde R4, ∃ z ∈ Q, z.1.1 = p) ∧
      (∀ z ∈ Q, ∀ z' ∈ Q, z.1.1 = z'.1.1 → ∃ g ∈ SO0, actT z g = z') :=
  ⟨redT R4, redT_reduction⟩

lemma redT_nonempty (x : X) : (redT X).Nonempty := by
  obtain ⟨z, hz, -⟩ := redT_reduction.2.2.1 (pt (yO x 0) 0)
  exact ⟨z, hz⟩

end

end GU.Library
