import GU.Bundle.SO0Reduction

/-!
# Phase 5, item 4: the time-orientation double cover of `Y13`

A point of `Ytilde X` is a Lorentzian metric `y` together with a choice of future cone of timelike
covectors: `future p` is the cone of `p`, in the preferred coordinates at the base point. The cone and
the metric determine the point (`eq_of_future_eq`), every cone occurs (`future_pt`), and each timelike
covector lies in the cone of `u` or of `−u` (`mem_futureCone_or`). Here a cone is a class of the sign
relation `G(·, u) > 0`; that it is a connected component is not formalised. The sheets of the topology
are the cones: `mem_future_iff_localTriv`. Topologically
`Ytilde X` is built from a sign cocycle on `Y13o X`: the charts are pairs `I = (i, ξ)` of a chart of `X`
and a covector `ξ` constant in that chart, on the open set where `ξ` is timelike, and the transition is
the sign of the pairing `G(ξ_I, ξ_J)`. The sign is a cocycle by the reversed Cauchy-Schwarz inequality
(`eta_pos`, `lp_sign_cocycle`).

* **`isCoveringMap_tilde`**: `Ytilde X → Y13o X` is a covering map, with **exactly two sheets**
  (`ncard_fibre`).
* **`isManifold_tilde`**, **`isLocalDiffeomorph_tilde`**: `Ytilde X` is a smooth manifold via
  `LocalHomeoCharts`, and the projection is a local diffeomorphism.
* **`no_closed_lift`**: no lift of the metric loop `yO x` of `no_spinStructure_univ` to `Ytilde X` is
  closed, while lifts from every point over the base point exist (`exists_lift_yO`). So the cover has
  no global section (`no_section`) over `Y13o X` for nonempty `X`. (Informally, a trivial two-sheeted
  cover has a section, so this cover is not trivial.)

General `X`; no hypothesis beyond those of `Y13o X`. As for `Y`, `IsManifold` carries no Hausdorff or
second-countability claim; `t2_tilde` shows the cover is Hausdorff whenever `Y13o X` is, and
`t2_Ytilde` (`Y13Hausdorff.lean`) whenever `X` is.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### Pointwise Lorentz algebra -/

/-- The pairing of two covectors under a contravariant metric. -/
def lp (G : M4) (u v : R4) : ℝ := u ⬝ᵥ (G *ᵥ v)

lemma lp_conj (G A : M4) (u v : R4) : lp G (Aᵀ *ᵥ u) (Aᵀ *ᵥ v) = lp (A * G * Aᵀ) u v := by
  unfold lp
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.transpose_transpose,
    Matrix.dotProduct_mulVec _ Aᵀ v, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec u, Matrix.mul_assoc]

lemma lp_eta (a b : R4) :
    lp ηR a b = a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3 := by
  unfold lp
  rw [GU.Iso77.ηR_eq, ηr]
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal, Fin.sum_univ_four]
  ring

lemma eta_pos {a b : R4} (ha : 0 < lp ηR a a) (hb : 0 < lp ηR b b) (h0 : 0 < a 0) (h0' : 0 < b 0) :
    0 < lp ηR a b := by
  rw [lp_eta] at ha hb ⊢
  set S := a 1 * b 1 + a 2 * b 2 + a 3 * b 3 with hS
  have hCS : S ^ 2 ≤ (a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) * (b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) := by
    rw [hS]
    nlinarith [sq_nonneg (a 1 * b 2 - a 2 * b 1), sq_nonneg (a 1 * b 3 - a 3 * b 1),
      sq_nonneg (a 2 * b 3 - a 3 * b 2)]
  have ha' : a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 < a 0 ^ 2 := by nlinarith
  have hb' : b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 < b 0 ^ 2 := by nlinarith
  have hlt : S ^ 2 < (a 0 * b 0) ^ 2 := by
    calc S ^ 2 ≤ _ := hCS
      _ < a 0 ^ 2 * b 0 ^ 2 := by
        apply mul_lt_mul'' ha' hb' <;> positivity
      _ = _ := by ring
  have hp : 0 < a 0 * b 0 := mul_pos h0 h0'
  have := abs_lt_of_sq_lt_sq hlt hp.le
  have h2 := (abs_lt.mp this).2
  have : a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3 = a 0 * b 0 - S := by rw [hS]; ring
  rw [this]; linarith

lemma lp_neg_left (G : M4) (u v : R4) : lp G (-u) v = - lp G u v := by simp [lp]
lemma lp_neg_right (G : M4) (u v : R4) : lp G u (-v) = - lp G u v := by simp [lp, Matrix.mulVec_neg]

lemma eta_zero_ne {a : R4} (ha : 0 < lp ηR a a) : a 0 ≠ 0 := by
  rw [lp_eta] at ha
  intro h
  rw [h] at ha
  nlinarith [mul_self_nonneg (a 1), mul_self_nonneg (a 2), mul_self_nonneg (a 3)]

/-- The time sign of a covector: the sign of its time coordinate in a Lorentz frame `P`. -/
def tneg (P : M4) (u : R4) : Prop := (Pᵀ *ᵥ u) 0 < 0

lemma lp_frame {G P : M4} (h : G = P * ηR * Pᵀ) (u v : R4) : lp G u v = lp ηR (Pᵀ *ᵥ u) (Pᵀ *ᵥ v) := by
  rw [lp_conj, h]

/-- The pairing of two timelike covectors is negative iff their time signs differ. -/
lemma lp_neg_iff {G P : M4} (h : G = P * ηR * Pᵀ) {u v : R4} (hu : 0 < lp G u u) (hv : 0 < lp G v v) :
    lp G u v < 0 ↔ (tneg P u ↔ ¬ tneg P v) := by
  rw [lp_frame h] at hu hv ⊢
  set a := Pᵀ *ᵥ u
  set b := Pᵀ *ᵥ v
  have ha0 := eta_zero_ne hu
  have hb0 := eta_zero_ne hv
  unfold tneg
  change lp ηR a b < 0 ↔ (a 0 < 0 ↔ ¬ b 0 < 0)
  have hna : 0 < lp ηR (-a) (-a) := by rw [lp_neg_left, lp_neg_right]; simpa using hu
  have hnb : 0 < lp ηR (-b) (-b) := by rw [lp_neg_left, lp_neg_right]; simpa using hv
  rcases lt_or_gt_of_ne ha0 with h1 | h1 <;> rcases lt_or_gt_of_ne hb0 with h2 | h2
  · have := eta_pos hna hnb (by simpa using h1) (by simpa using h2)
    rw [lp_neg_left, lp_neg_right, neg_neg] at this
    simp [h1, h2, not_lt.mpr this.le]
  · have := eta_pos hna hv (by simpa using h1) h2
    rw [lp_neg_left] at this
    simp [h1, not_lt.mpr h2.le]
    linarith
  · have := eta_pos hu hnb h1 (by simpa using h2)
    rw [lp_neg_right] at this
    simp [h2, not_lt.mpr h1.le]
    linarith
  · have := eta_pos hu hv h1 h2
    simp [not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr this.le]

lemma lp_ne_zero {G P : M4} (h : G = P * ηR * Pᵀ) {u v : R4} (hu : 0 < lp G u u) (hv : 0 < lp G v v) :
    lp G u v ≠ 0 := by
  rw [lp_frame h] at hu hv ⊢
  intro h0
  have hna : 0 < lp ηR (-(Pᵀ *ᵥ u)) (-(Pᵀ *ᵥ u)) := by rw [lp_neg_left, lp_neg_right]; simpa using hu
  have hnb : 0 < lp ηR (-(Pᵀ *ᵥ v)) (-(Pᵀ *ᵥ v)) := by rw [lp_neg_left, lp_neg_right]; simpa using hv
  have ha0 := eta_zero_ne hu
  have hb0 := eta_zero_ne hv
  rcases lt_or_gt_of_ne ha0 with h1 | h1 <;> rcases lt_or_gt_of_ne hb0 with h2 | h2
  · have := eta_pos hna hnb (by simpa using h1) (by simpa using h2)
    rw [lp_neg_left, lp_neg_right, neg_neg, h0] at this; exact lt_irrefl _ this
  · have := eta_pos hna hv (by simpa using h1) h2
    rw [lp_neg_left, h0] at this; simp at this
  · have := eta_pos hu hnb h1 (by simpa using h2)
    rw [lp_neg_right, h0] at this; simp at this
  · have := eta_pos hu hv h1 h2
    rw [h0] at this; exact lt_irrefl _ this

/-- **Same side is transitive**: the sign of the pairing is a cocycle on timelike covectors. -/
lemma lp_sign_cocycle {G P : M4} (h : G = P * ηR * Pᵀ) {u v w : R4} (hu : 0 < lp G u u)
    (hv : 0 < lp G v v) (hw : 0 < lp G w w) :
    xor (decide (lp G u v < 0)) (decide (lp G v w < 0)) = decide (lp G u w < 0) := by
  have h1 := lp_neg_iff h hu hv
  have h2 := lp_neg_iff h hv hw
  have h3 := lp_neg_iff h hu hw
  by_cases p : lp G u v < 0 <;> by_cases q : lp G v w < 0 <;> by_cases r : lp G u w < 0 <;>
    simp [p, q, r] <;> (exfalso; tauto)

lemma lp_comm {G P : M4} (h : G = P * ηR * Pᵀ) (u v : R4) : lp G u v = lp G v u := by
  rw [lp_frame h u v, lp_frame h v u, lp_eta, lp_eta]
  ring

lemma continuous_lp {Z : Type*} [TopologicalSpace Z] {S : Set Z} {G : Z → M4} {u v : Z → R4}
    (hG : ContinuousOn G S) (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun z => lp (G z) (u z) (v z)) S := by
  have hc : Continuous fun t : M4 × R4 × R4 => lp t.1 t.2.1 t.2.2 :=
    (continuous_fst.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec (continuous_snd.comp continuous_snd))
  exact hc.comp_continuousOn (hG.prodMk (hu.prodMk hv))

lemma continuous_mat : Continuous (mat : ((Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) → M4) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [mat, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  exact (continuous_apply a).comp (ContinuousLinearMap.apply ℝ (Fin 4 → ℝ) _).continuous

/-- A sign of a nowhere-zero continuous function is continuous. -/
lemma continuousOn_decide_neg {Z : Type*} [TopologicalSpace Z] {S : Set Z} {g : Z → ℝ}
    (hg : ContinuousOn g S) (h0 : ∀ z ∈ S, g z ≠ 0) :
    ContinuousOn (fun z => decide (g z < 0)) S := by
  intro z hz
  rcases lt_or_gt_of_ne (h0 z hz) with h | h
  · have hev : ∀ᶠ w in 𝓝[S] z, g w < 0 := (hg z hz).eventually (gt_mem_nhds h)
    refine (continuousWithinAt_const : ContinuousWithinAt (fun _ => true) S z).congr_of_eventuallyEq
      (hev.mono fun w hw => by simp [hw]) (by simp [h])
  · have hev : ∀ᶠ w in 𝓝[S] z, 0 < g w := (hg z hz).eventually (lt_mem_nhds h)
    refine (continuousWithinAt_const : ContinuousWithinAt (fun _ => false) S z).congr_of_eventuallyEq
      (hev.mono fun w hw => by simp [not_lt.mpr hw.le]) (by simp [not_lt.mpr h.le])

/-! ### The cover -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The base point. -/
def baseX (y : Y13o X) : X := πY (y : Yobs X)

lemma continuous_baseX : Continuous (baseX : Y13o X → X) :=
  (FiberBundle.continuous_proj _ _).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- A chart of `X` and a covector constant in it. -/
abbrev TimeIdx (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X] :=
  (atlas (Fin 4 → ℝ) X) × R4

/-- The transition matrix from the preferred chart at `x` to the chart `i`. -/
def transMat (i : atlas (Fin 4 → ℝ) X) (x : X) : M4 :=
  mat ((Zt X).coordChange ((Zt X).indexAt x) i x)

/-- The covector of `I`, at `x`, in the preferred coordinates at `x`. -/
def cov (I : TimeIdx X) (x : X) : R4 := (transMat I.1 x)ᵀ *ᵥ I.2

lemma Acc_self (x : X) : transMat ((Zt X).indexAt x) x = 1 := by
  have h : (Zt X).coordChange ((Zt X).indexAt x) ((Zt X).indexAt x) x = ContinuousLinearMap.id ℝ _ := by
    ext w : 1
    exact (Zt X).coordChange_self _ x ((Zt X).mem_baseSet_at x) w
  rw [transMat, h]
  exact mat_id

lemma cov_index (x : X) (u : R4) : cov ((Zt X).indexAt x, u) x = u := by
  show (transMat ((Zt X).indexAt x) x)ᵀ *ᵥ u = u
  rw [Acc_self]; simp

/-- The pairing of two chart covectors at `y`. -/
def tb (I J : TimeIdx X) (y : Y13o X) : ℝ := lp (Gpt (y : Yobs X)) (cov I (baseX y)) (cov J (baseX y))

/-- The metric of `y` in the chart `i`. -/
def chartG (i : atlas (Fin 4 → ℝ) X) (y : Y13o X) : M4 :=
  transMat i (baseX y) * Gpt (y : Yobs X) * (transMat i (baseX y))ᵀ

lemma symMat_symAct (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (v : Fin 10 → ℝ) :
    symMat (symAct T v) = mat T * symMat v * (mat T)ᵀ := by
  have hs : (mat T * symMat v * (mat T)ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm v).eq, Matrix.mul_assoc]
  rw [symAct_apply]; exact symMat_symCoords _ hs

lemma continuousOn_chartG (i : atlas (Fin 4 → ℝ) X) :
    ContinuousOn (chartG i) {y : Y13o X | baseX y ∈ (Zt X).baseSet i} := by
  have hT := ((symCore (Zt X)).localTriv i).continuousOn
  have hsrc : Set.MapsTo (fun y : Y13o X => ((y : Yobs X) : Sym2TX X))
      {y : Y13o X | baseX y ∈ (Zt X).baseSet i} ((symCore (Zt X)).localTriv i).source := by
    intro y hy
    rw [Trivialization.mem_source]
    exact hy
  have hm : Continuous fun y : Y13o X => ((y : Yobs X) : Sym2TX X) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc := continuous_symMat.comp_continuousOn
    (continuous_snd.comp_continuousOn (hT.comp hm.continuousOn hsrc))
  refine hc.congr fun y _ => ?_
  exact (symMat_symAct _ _).symm

lemma tb_eq {I J : TimeIdx X} {y : Y13o X} (hi : baseX y ∈ (Zt X).baseSet I.1)
    (hj : baseX y ∈ (Zt X).baseSet J.1) :
    tb I J y = lp (chartG I.1 y) I.2
      ((mat ((Zt X).coordChange I.1 J.1 (baseX y)))ᵀ *ᵥ J.2) := by
  have h : transMat J.1 (baseX y) = mat ((Zt X).coordChange I.1 J.1 (baseX y)) * transMat I.1 (baseX y) := by
    unfold transMat
    rw [← mat_comp]
    congr 1
    ext w : 1
    exact ((Zt X).coordChange_comp _ _ _ (baseX y) ⟨⟨(Zt X).mem_baseSet_at _, hi⟩, hj⟩ w).symm
  unfold tb chartG
  rw [← lp_conj]
  show lp _ _ ((transMat J.1 (baseX y))ᵀ *ᵥ J.2) = _
  rw [h, transpose_mul, ← Matrix.mulVec_mulVec]
  rfl

lemma continuousOn_tb (I J : TimeIdx X) :
    ContinuousOn (tb I J) {y : Y13o X | baseX y ∈ (Zt X).baseSet I.1 ∩ (Zt X).baseSet J.1} := by
  have hA : ContinuousOn (fun y : Y13o X => (mat ((Zt X).coordChange I.1 J.1 (baseX y)))ᵀ *ᵥ J.2)
      {y : Y13o X | baseX y ∈ (Zt X).baseSet I.1 ∩ (Zt X).baseSet J.1} := by
    have h1 : Continuous fun M : M4 => Mᵀ *ᵥ J.2 :=
      continuous_id.matrix_transpose.matrix_mulVec continuous_const
    exact h1.comp_continuousOn (continuous_mat.comp_continuousOn
      (((Zt X).continuousOn_coordChange I.1 J.1).comp continuous_baseX.continuousOn fun _ h => h))
  refine (continuous_lp ((continuousOn_chartG I.1).mono fun y hy => hy.1) continuousOn_const hA).congr
    fun y hy => tb_eq hy.1 hy.2

/-- The chart domain of `I`: where its covector is timelike. -/
def tV (I : TimeIdx X) : Set (Y13o X) := {y | baseX y ∈ (Zt X).baseSet I.1 ∧ 0 < tb I I y}

lemma isOpen_tV (I : TimeIdx X) : IsOpen (tV I) := by
  have hS : IsOpen {y : Y13o X | baseX y ∈ (Zt X).baseSet I.1 ∩ (Zt X).baseSet I.1} :=
    (((Zt X).isOpen_baseSet I.1).inter ((Zt X).isOpen_baseSet I.1)).preimage continuous_baseX
  have := (continuousOn_tb I I).isOpen_inter_preimage hS (isOpen_Ioi (a := (0 : ℝ)))
  convert this using 1
  ext y
  simp [tV]

lemma exists_timelike (y : Y13o X) : ∃ ξ : R4, 0 < lp (Gpt (y : Yobs X)) ξ ξ := by
  obtain ⟨P, hP, hG⟩ := y.2
  have hPt : IsUnit Pᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hP
  refine ⟨(Pᵀ)⁻¹ *ᵥ Pi.single 0 1, ?_⟩
  have hc : Pᵀ *ᵥ ((Pᵀ)⁻¹ *ᵥ (Pi.single 0 1 : R4)) = Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hPt),
      Matrix.one_mulVec]
  rw [lp_frame hG, hc, lp_eta]
  simp

/-- The chart index at `y`. -/
def idxAt (y : Y13o X) : TimeIdx X := ((Zt X).indexAt (baseX y), (exists_timelike y).choose)

lemma cov_idxAt (y : Y13o X) : cov (idxAt y) (baseX y) = (exists_timelike y).choose :=
  cov_index _ _

lemma mem_tV_idxAt (y : Y13o X) : y ∈ tV (idxAt y) := by
  refine ⟨(Zt X).mem_baseSet_at _, ?_⟩
  unfold tb
  rw [cov_idxAt]
  exact (exists_timelike y).choose_spec

lemma tb_ne {I J : TimeIdx X} {y : Y13o X} (hI : y ∈ tV I) (hJ : y ∈ tV J) : tb I J y ≠ 0 := by
  obtain ⟨P, -, hG⟩ := y.2
  exact lp_ne_zero hG hI.2 hJ.2

lemma tb_cocycle {I J K : TimeIdx X} {y : Y13o X} (hI : y ∈ tV I) (hJ : y ∈ tV J) (hK : y ∈ tV K) :
    xor (decide (tb I J y < 0)) (decide (tb J K y < 0)) = decide (tb I K y < 0) := by
  obtain ⟨P, -, hG⟩ := y.2
  exact lp_sign_cocycle hG hI.2 hJ.2 hK.2

/-- **The sign cocycle of the double cover**. The fibre is `Bool`; `true` flips the sheet. -/
def tildeCore (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :
    FiberBundleCore (TimeIdx X) (Y13o X) Bool where
  baseSet := tV
  isOpen_baseSet := isOpen_tV
  indexAt := idxAt
  mem_baseSet_at := mem_tV_idxAt
  coordChange I J y v := xor v (decide (tb I J y < 0))
  coordChange_self I y hy v := by
    have : ¬ tb I I y < 0 := not_lt.mpr hy.2.le
    simp [this]
  continuousOn_coordChange I J := by
    have hs : ContinuousOn (fun y => decide (tb I J y < 0)) (tV I ∩ tV J) :=
      continuousOn_decide_neg ((continuousOn_tb I J).mono fun y hy => ⟨hy.1.1, hy.2.1⟩)
        fun y hy => tb_ne hy.1 hy.2
    have hx : Continuous fun b : Bool × Bool => xor b.1 b.2 := continuous_of_discreteTopology
    exact hx.comp_continuousOn ((continuous_snd.continuousOn).prodMk
      (hs.comp continuous_fst.continuousOn fun p hp => hp.1))
  coordChange_comp I J K y hy v := by
    have := tb_cocycle hy.1.1 hy.1.2 hy.2
    rw [Bool.xor_assoc, this]

/-- **The time-orientation double cover of `Y13`.** -/
abbrev Ytilde (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :=
  (tildeCore X).TotalSpace

/-- The covering projection. -/
def piT (p : Ytilde X) : Y13o X := p.proj

/-- **`Ytilde X → Y13o X` is a covering map.** -/
theorem isCoveringMap_tilde : IsCoveringMap (piT : Ytilde X → Y13o X) :=
  FiberBundle.isCoveringMap (F := Bool) (E := (tildeCore X).Fiber)

lemma continuous_piT : Continuous (piT : Ytilde X → Y13o X) := isCoveringMap_tilde.continuous

/-- **Two sheets**: every fibre has exactly two points. -/
theorem ncard_fibre (y : Y13o X) : (piT ⁻¹' {y} : Set (Ytilde X)).ncard = 2 := by
  have h : (piT ⁻¹' {y} : Set (Ytilde X)) = {⟨y, false⟩, ⟨y, true⟩} := by
    ext ⟨z, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, piT]
    constructor
    · rintro rfl
      cases b <;> simp
    · rintro (h | h) <;> exact (congrArg TotalSpace.proj h)
  rw [h, Set.ncard_pair]
  intro h
  simpa using congrArg TotalSpace.snd (eq_of_heq (by simpa using h) : (⟨y, false⟩ : Ytilde X) = ⟨y, true⟩)

/-! ### Future cones: the points of the cover are metrics with a choice of cone -/

/-- `−c` on the sheet `true`. -/
def flipIf (b : Bool) (c : R4) : R4 := if b then -c else c

lemma lp_flipIf_self (G : M4) (b : Bool) (c : R4) : lp G (flipIf b c) (flipIf b c) = lp G c c := by
  cases b <;> simp [flipIf, lp_neg_left, lp_neg_right]

/-- The covector of a point of the cover: the chart covector, flipped on the sheet `true`. -/
def rep (p : Ytilde X) : R4 := flipIf p.2 (cov (idxAt p.proj) (baseX p.proj))

/-- The cone of timelike covectors on the same side as `u`. -/
def futureCone (y : Y13o X) (u : R4) : Set R4 :=
  {v | 0 < lp (Gpt (y : Yobs X)) v v ∧ 0 < lp (Gpt (y : Yobs X)) v u}

/-- **The future cone of a point of the cover.** -/
def future (p : Ytilde X) : Set R4 := futureCone p.proj (rep p)

lemma timelike_rep (p : Ytilde X) :
    0 < lp (Gpt (p.proj : Yobs X)) (rep p) (rep p) := by
  have h : 0 < tb (idxAt p.proj) (idxAt p.proj) p.proj := (mem_tV_idxAt p.proj).2
  exact lt_of_lt_of_eq h (lp_flipIf_self _ _ _).symm

/-- The point of the cover over `y` on the side of the timelike covector `u`. -/
def pt (y : Y13o X) (u : R4) : Ytilde X :=
  ⟨y, decide (lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) u < 0)⟩

lemma piT_pt (y : Y13o X) (u : R4) : piT (pt y u) = y := rfl

/-- The covector of `pt y u` is on the side of `u`. -/
lemma lp_rep_pt {y : Y13o X} {u : R4} (hu : 0 < lp (Gpt (y : Yobs X)) u u) :
    0 < lp (Gpt (y : Yobs X)) (rep (pt y u)) u := by
  obtain ⟨P, -, hG⟩ := y.2
  have hc : 0 < lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov (idxAt y) (baseX y)) :=
    (mem_tV_idxAt y).2
  have hne := lp_ne_zero hG hc hu
  show 0 < lp _ (flipIf (decide (lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) u < 0))
    (cov (idxAt y) (baseX y))) u
  by_cases h : lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) u < 0
  · simp only [h, decide_true, flipIf, ite_true]
    rw [lp_neg_left]; linarith
  · simp only [h, decide_false, flipIf, Bool.false_eq_true, ite_false]
    exact lt_of_le_of_ne (not_lt.mp h) hne.symm

/-- Being on the same side as `a` or as `b` agrees, when `a` and `b` are on the same side. -/
lemma side_iff {G P : M4} (hG : G = P * ηR * Pᵀ) {a b v : R4} (ha : 0 < lp G a a) (hb : 0 < lp G b b)
    (hv : 0 < lp G v v) (hab : 0 < lp G a b) : 0 < lp G v a ↔ 0 < lp G v b := by
  have h := lp_sign_cocycle hG hv ha hb
  have hab' : ¬ lp G a b < 0 := not_lt.mpr hab.le
  have ne1 := lp_ne_zero hG hv ha
  have ne2 := lp_ne_zero hG hv hb
  simp only [hab', decide_false, Bool.xor_false, decide_eq_decide] at h
  constructor
  · intro h1
    refine lt_of_le_of_ne (not_lt.mp fun h2 => ?_) ne2.symm
    exact absurd (h.mpr h2) (not_lt.mpr h1.le)
  · intro h1
    refine lt_of_le_of_ne (not_lt.mp fun h2 => ?_) ne1.symm
    exact absurd (h.mp h2) (not_lt.mpr h1.le)

/-- **Every future cone occurs**: over `y`, each timelike covector `u` gives a point with cone `u`. -/
theorem future_pt {y : Y13o X} {u : R4} (hu : 0 < lp (Gpt (y : Yobs X)) u u) :
    future (pt y u) = futureCone y u := by
  obtain ⟨P, -, hG⟩ := y.2
  have hr : 0 < lp (Gpt (y : Yobs X)) (rep (pt y u)) (rep (pt y u)) := timelike_rep (pt y u)
  have hab := lp_rep_pt hu
  ext v
  show (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right fun hv => side_iff hG hr hu hv hab

/-- **A point of the cover is determined by its metric and its future cone.** -/
theorem eq_of_future_eq {p q : Ytilde X} (hp : p.proj = q.proj) (hf : future p = future q) : p = q := by
  obtain ⟨y, b⟩ := p
  obtain ⟨y', b'⟩ := q
  obtain rfl : y = y' := hp
  have hr := timelike_rep (⟨y, b⟩ : Ytilde X)
  have hmem : rep (⟨y, b⟩ : Ytilde X) ∈ future (⟨y, b⟩ : Ytilde X) := ⟨hr, hr⟩
  rw [hf] at hmem
  have hpos : 0 < lp (Gpt (y : Yobs X)) (rep (⟨y, b⟩ : Ytilde X)) (rep (⟨y, b'⟩ : Ytilde X)) := hmem.2
  have hc : 0 < lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov (idxAt y) (baseX y)) :=
    (mem_tV_idxAt y).2
  cases b <;> cases b'
  · rfl
  · exfalso
    have : 0 < lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (-cov (idxAt y) (baseX y)) := by
      simpa [rep, flipIf] using hpos
    rw [lp_neg_right] at this; linarith
  · exfalso
    have : 0 < lp (Gpt (y : Yobs X)) (-cov (idxAt y) (baseX y)) (cov (idxAt y) (baseX y)) := by
      simpa [rep, flipIf] using hpos
    rw [lp_neg_left] at this; linarith
  · rfl

/-- Points on opposite sides differ. -/
lemma pt_ne {y : Y13o X} {u v : R4} (hu : 0 < lp (Gpt (y : Yobs X)) u u)
    (hv : 0 < lp (Gpt (y : Yobs X)) v v) (h : lp (Gpt (y : Yobs X)) u v < 0) : pt y u ≠ pt y v := by
  intro he
  obtain ⟨P, -, hG⟩ := y.2
  have h1 := lp_rep_pt hu
  have h2 := lp_rep_pt hv
  rw [← he] at h2
  have hr := timelike_rep (pt y u)
  have h4 : 0 < lp (Gpt (y : Yobs X)) v u := by
    rw [← side_iff hG hr hu hv h1]
    rwa [lp_comm hG]
  rw [lp_comm hG] at h4
  linarith

/-- Each point over `y` is `pt y u` or `pt y (−u)`. -/
lemma eq_pt_or (p : Ytilde X) {u : R4} (hu : 0 < lp (Gpt (p.proj : Yobs X)) u u) :
    p = pt p.proj u ∨ p = pt p.proj (-u) := by
  obtain ⟨y, b⟩ := p
  obtain ⟨P, -, hG⟩ := y.2
  have hc : 0 < lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov (idxAt y) (baseX y)) :=
    (mem_tV_idxAt y).2
  have hne := lp_ne_zero hG hc hu
  by_cases h : lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) u < 0
  · have h' : ¬ lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (-u) < 0 := by
      rw [lp_neg_right]; linarith
    cases b
    · right; simp [pt, h']
    · left; simp [pt, h]
  · have h' : lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (-u) < 0 := by
      rw [lp_neg_right]
      have := lt_of_le_of_ne (not_lt.mp h) hne.symm
      linarith
    cases b
    · left; simp [pt, h]
    · right; simp [pt, h']

/-- **Exactly two cones**: each timelike covector lies in the cone of `u` or of `−u`. -/
lemma mem_futureCone_or {y : Y13o X} {u v : R4} (hu : 0 < lp (Gpt (y : Yobs X)) u u)
    (hv : 0 < lp (Gpt (y : Yobs X)) v v) : v ∈ futureCone y u ∨ v ∈ futureCone y (-u) := by
  obtain ⟨P, -, hG⟩ := y.2
  rcases lt_or_gt_of_ne (lp_ne_zero hG hv hu) with h | h
  · exact Or.inr ⟨hv, by rw [lp_neg_right]; linarith⟩
  · exact Or.inl ⟨hv, h⟩

/-- The two cones are disjoint. -/
lemma futureCone_disjoint (y : Y13o X) (u : R4) : Disjoint (futureCone y u) (futureCone y (-u)) := by
  refine Set.disjoint_left.mpr fun v h1 h2 => ?_
  have h3 := h2.2
  rw [lp_neg_right] at h3
  linarith [h1.2]

/-- The local trivialisation at `I` reads the side of the covector of `I`. -/
lemma localTriv_snd_cov (I : TimeIdx X) (p : Ytilde X) (hp : p.proj ∈ tV I) :
    ((tildeCore X).localTriv I p).2 =
      decide (lp (Gpt (p.proj : Yobs X)) (rep p) (cov I (baseX p.proj)) < 0) := by
  rw [FiberBundleCore.localTriv_apply]
  obtain ⟨y, b⟩ := p
  obtain ⟨P, -, hG⟩ := y.2
  show xor b (decide (tb (idxAt y) I y < 0)) =
    decide (lp _ (flipIf b (cov (idxAt y) (baseX y))) (cov I (baseX y)) < 0)
  have hc : 0 < lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov (idxAt y) (baseX y)) :=
    (mem_tV_idxAt y).2
  have hne := lp_ne_zero hG hc hp.2
  unfold tb
  cases b
  · simp [flipIf]
  · simp only [flipIf, ite_true, Bool.true_xor, lp_neg_left]
    by_cases h : lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov I (baseX y)) < 0
    · have h' : ¬ -lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov I (baseX y)) < 0 := by linarith
      simp [h, h']
    · have h1 := lt_of_le_of_ne (not_lt.mp h) hne.symm
      have h' : -lp (Gpt (y : Yobs X)) (cov (idxAt y) (baseX y)) (cov I (baseX y)) < 0 := by linarith
      simp [h, h']

/-- **The sheets are the cones**: over the chart `I`, the sheet `false` is where the covector of `I`
is future. -/
theorem mem_future_iff_localTriv (I : TimeIdx X) (p : Ytilde X) (hp : p.proj ∈ tV I) :
    cov I (baseX p.proj) ∈ future p ↔ ((tildeCore X).localTriv I p).2 = false := by
  obtain ⟨P, -, hG⟩ := p.proj.2
  have hc : 0 < lp (Gpt (p.proj : Yobs X)) (cov I (baseX p.proj)) (cov I (baseX p.proj)) := hp.2
  have hne := lp_ne_zero hG (timelike_rep p) hc
  rw [localTriv_snd_cov I p hp, decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨-, h⟩
    rw [lp_comm hG] at h
    exact h.le
  · intro h
    refine ⟨hc, ?_⟩
    rw [lp_comm hG]
    exact lt_of_le_of_ne h hne.symm

/-! ### Paths in one fibre -/

/-- In one fibre, the point on the side of a continuous timelike covector moves continuously. -/
theorem continuous_pt_fibre {Z : Type*} [TopologicalSpace Z] {x : X} {y : Z → Y13o X} {u : Z → R4}
    (hy : Continuous y) (hx : ∀ z, baseX (y z) = x)
    (hG : Continuous fun z => Gpt (y z : Yobs X)) (hu : Continuous u)
    (ht : ∀ z, 0 < lp (Gpt (y z : Yobs X)) (u z) (u z)) :
    Continuous fun z => pt (y z) (u z) := by
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hy.continuousAt, ?_⟩
  set I₀ := idxAt (y z₀) with hI₀
  set c₀ := cov I₀ x with hc₀
  have hmem : ∀ᶠ z in 𝓝 z₀, y z ∈ tV I₀ :=
    hy.continuousAt.eventually ((isOpen_tV I₀).mem_nhds (mem_tV_idxAt (y z₀)))
  have hg : Continuous fun z => lp (Gpt (y z : Yobs X)) (u z) c₀ := by
    have := continuous_lp (S := Set.univ) hG.continuousOn hu.continuousOn
      (continuousOn_const (c := c₀))
    exact continuousOn_univ.mp this
  have hc₀t : 0 < lp (Gpt (y z₀ : Yobs X)) c₀ c₀ := by
    have := (mem_tV_idxAt (y z₀)).2
    unfold tb at this
    rwa [hx z₀] at this
  have hne : lp (Gpt (y z₀ : Yobs X)) (u z₀) c₀ ≠ 0 := by
    obtain ⟨P, -, hGP⟩ := (y z₀).2
    exact lp_ne_zero hGP (ht z₀) hc₀t
  have hdec := (continuousOn_decide_neg (S := {z | lp (Gpt (y z : Yobs X)) (u z) c₀ ≠ 0})
    hg.continuousOn fun z hz => hz).continuousAt
    ((isOpen_ne_fun hg continuous_const).mem_nhds hne)
  refine hdec.congr ?_
  filter_upwards [hmem] with z hz
  show _ = (FiberBundleCore.localTriv (tildeCore X) (idxAt (y z₀)) (pt (y z) (u z))).2
  rw [FiberBundleCore.localTriv_apply]
  show _ = xor (decide (lp _ (cov (idxAt (y z)) (baseX (y z))) (u z) < 0))
    (decide (tb (idxAt (y z)) I₀ (y z) < 0))
  obtain ⟨P, -, hGP⟩ := (y z).2
  have hcz : 0 < lp (Gpt (y z : Yobs X)) (cov (idxAt (y z)) (baseX (y z))) (cov (idxAt (y z)) (baseX (y z))) :=
    (mem_tV_idxAt (y z)).2
  have hI : 0 < lp (Gpt (y z : Yobs X)) c₀ c₀ := by
    have := hz.2
    unfold tb at this
    rwa [hx z] at this
  have hco := lp_sign_cocycle hGP (ht z) hcz hI
  have e1 : tb (idxAt (y z)) I₀ (y z) =
      lp (Gpt (y z : Yobs X)) (cov (idxAt (y z)) (baseX (y z))) c₀ := by
    unfold tb
    rw [hx z]
  rw [e1, lp_comm hGP (cov (idxAt (y z)) (baseX (y z))) (u z), hco]

/-! ### The metric loop does not lift to a closed loop -/

/-- The metric loop of `no_spinStructure_univ`, in `Y13`. -/
def yO (x : X) (θ : ℝ) : Y13o X := ⟨yLoop x θ, Rθ θ, isUnit_Rθ θ, Gpt_yLoop x θ⟩

lemma projOFr_pLoop (x : X) (θ : ℝ) : projOFr (pLoop x θ) = yO x θ := rfl

lemma continuous_yO (x : X) : Continuous (yO x) := (continuous_yLoop x).subtype_mk _

lemma yO_pi (x : X) : yO x Real.pi = yO x 0 := Subtype.ext (yLoop_pi x)

lemma baseX_yO (x : X) (θ : ℝ) : baseX (yO x θ) = x := rfl

/-- The timelike axis rotating with the metric. -/
def uLoop (θ : ℝ) : R4 := ![Real.cos θ, Real.sin θ, 0, 0]

lemma continuous_uLoop : Continuous uLoop := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [uLoop] <;> fun_prop

lemma Rθ_transpose_uLoop (θ : ℝ) : (Rθ θ)ᵀ *ᵥ uLoop θ = Pi.single 0 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i
  fin_cases i <;> simp [Rθ, uLoop, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> nlinarith

lemma Gpt_yO (x : X) (θ : ℝ) : Gpt (yO x θ : Yobs X) = Rθ θ * ηR * (Rθ θ)ᵀ := Gpt_yLoop x θ

lemma timelike_uLoop (x : X) (θ : ℝ) : 0 < lp (Gpt (yO x θ : Yobs X)) (uLoop θ) (uLoop θ) := by
  rw [lp_frame (Gpt_yO x θ), Rθ_transpose_uLoop, lp_eta]
  simp

lemma timelike_neg_uLoop (x : X) (θ : ℝ) : 0 < lp (Gpt (yO x θ : Yobs X)) (-uLoop θ) (-uLoop θ) := by
  rw [lp_neg_left, lp_neg_right, neg_neg]
  exact timelike_uLoop x θ

lemma continuous_Gpt_yO (x : X) : Continuous fun θ => Gpt (yO x θ : Yobs X) := by
  have h : (fun θ => Gpt (yO x θ : Yobs X)) = fun θ => Rθ θ * ηR * (Rθ θ)ᵀ := funext (Gpt_yO x)
  rw [h]
  exact (continuous_Rθ.matrix_mul continuous_const).matrix_mul continuous_Rθ.matrix_transpose

/-- The lift through the side of the rotating axis. -/
lemma continuous_lift_pos (x : X) : Continuous fun θ => pt (yO x θ) (uLoop θ) :=
  continuous_pt_fibre (continuous_yO x) (baseX_yO x) (continuous_Gpt_yO x) continuous_uLoop
    (timelike_uLoop x)

lemma continuous_lift_neg (x : X) : Continuous fun θ => pt (yO x θ) (-uLoop θ) :=
  continuous_pt_fibre (continuous_yO x) (baseX_yO x) (continuous_Gpt_yO x) continuous_uLoop.neg
    (timelike_neg_uLoop x)

/-- At the end of the loop the axis has turned to its negative. -/
lemma uLoop_pi : uLoop Real.pi = -uLoop 0 := by
  ext i; fin_cases i <;> simp [uLoop]

/-- **The metric loop lifts as a path.** -/
theorem exists_lift_yO (x : X) (p₀ : Ytilde X) (hp₀ : piT p₀ = yO x 0) :
    ∃ l : ℝ → Ytilde X, Continuous l ∧ (∀ θ, piT (l θ) = yO x θ) ∧ l 0 = p₀ := by
  obtain ⟨y, b⟩ := p₀
  obtain rfl : y = yO x 0 := hp₀
  rcases eq_pt_or (⟨yO x 0, b⟩ : Ytilde X) (timelike_uLoop x 0) with h | h
  · exact ⟨_, continuous_lift_pos x, fun _ => rfl, h.symm⟩
  · exact ⟨_, continuous_lift_neg x, fun _ => rfl, h.symm⟩

lemma lift_pos_ne (x : X) : pt (yO x Real.pi) (uLoop Real.pi) ≠ pt (yO x 0) (uLoop 0) := by
  have hu0 := timelike_uLoop x 0
  rw [yO_pi]
  refine pt_ne (by rw [uLoop_pi, lp_neg_left, lp_neg_right, neg_neg]; exact hu0) hu0 ?_
  rw [uLoop_pi, lp_neg_left]
  linarith

lemma lift_neg_ne (x : X) : pt (yO x Real.pi) (-uLoop Real.pi) ≠ pt (yO x 0) (-uLoop 0) := by
  have hu0 := timelike_uLoop x 0
  rw [yO_pi]
  refine pt_ne (by rw [uLoop_pi, neg_neg]; exact hu0) (timelike_neg_uLoop x 0) ?_
  rw [uLoop_pi, neg_neg, lp_neg_right]
  linarith

/-- **No lift of the metric loop to the cover is closed.** The loop `yO x` on `[0, π]` is closed
(`yO_pi`), and it is the base of the path `pLoop` of `no_spinStructure_univ` (`projOFr_pLoop`). -/
theorem no_closed_lift (x : X) (l : ℝ → Ytilde X) (hl : Continuous l)
    (hp : ∀ θ, piT (l θ) = yO x θ) : l Real.pi ≠ l 0 := by
  have hb : (l 0).proj = yO x 0 := hp 0
  have key : ∀ s : ℝ → Ytilde X, Continuous s → (∀ θ, piT (s θ) = yO x θ) → s 0 = l 0 → l = s :=
    fun s hs hsp h0 => isCoveringMap_tilde.eq_of_comp_eq hl hs
      (funext fun θ => (hp θ).trans (hsp θ).symm) 0 h0.symm
  rcases eq_pt_or (l 0) (u := uLoop 0) (by rw [hb]; exact timelike_uLoop x 0) with h | h
  · rw [hb] at h
    have e := key _ (continuous_lift_pos x) (fun _ => rfl) h.symm
    rw [e]
    exact lift_pos_ne x
  · rw [hb] at h
    have e := key _ (continuous_lift_neg x) (fun _ => rfl) h.symm
    rw [e]
    exact lift_neg_ne x

/-- **The cover has no global section**, for nonempty `X`. -/
theorem no_section (x : X) (s : Y13o X → Ytilde X) (hs : Continuous s) (hp : ∀ y, piT (s y) = y) :
    False := by
  refine no_closed_lift x (s ∘ yO x) (hs.comp (continuous_yO x)) (fun θ => hp _) ?_
  show s (yO x Real.pi) = s (yO x 0)
  rw [yO_pi]

/-- The projection is surjective. -/
lemma piT_surjective : Function.Surjective (piT : Ytilde X → Y13o X) :=
  fun y => ⟨pt y 0, rfl⟩

/-- The cover is nonempty for nonempty `X`. -/
lemma nonempty_tilde (x : X) : Nonempty (Ytilde X) := ⟨pt (yO x 0) 0⟩

/-- The cover is Hausdorff when `Y13o X` is. -/
instance t2_tilde [T2Space (Y13o X)] : T2Space (Ytilde X) := by
  refine ⟨fun p q hne => ?_⟩
  by_cases h : piT p = piT q
  · obtain ⟨s, t, hs, ht, hp, hq, hd⟩ := isCoveringMap_tilde.isSeparatedMap p q h hne
    exact ⟨s, t, hs, ht, hp, hq, hd⟩
  · obtain ⟨s, t, hs, ht, hp, hq, hd⟩ := t2_separation h
    exact ⟨piT ⁻¹' s, piT ⁻¹' t, hs.preimage continuous_piT, ht.preimage continuous_piT, hp, hq,
      hd.preimage _⟩

/-! ### The cover is a smooth manifold -/

/-- The projection is a local homeomorphism. -/
theorem isLocalHomeomorph_piT : IsLocalHomeomorph (piT : Ytilde X → Y13o X) :=
  isCoveringMap_tilde.isLocalHomeomorph

/-- The model of `Y13`. -/
abbrev EY := (Fin 4 → ℝ) × (Fin 10 → ℝ)

/-- The charts of `Y13`, with its product model as a normed space. -/
@[instance_reducible] def chartY13 : ChartedSpace EY (Y13o X) :=
  inferInstanceAs (ChartedSpace (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) (Y13o X))

attribute [local instance] chartY13

theorem isManifold_Y13_self : IsManifold 𝓘(ℝ, EY) ∞ (Y13o X) := by
  have h : IsManifold ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
      ∞ (Y13o X) := inferInstance
  rw [modelWithCornersSelf_prod]
  exact h

attribute [local instance] isManifold_Y13_self

/-- The charts of `Ytilde X`, pulled back from `Y13`. -/
@[instance_reducible] def chartTilde : ChartedSpace EY (Ytilde X) :=
  pullCharted EY isLocalHomeomorph_piT

/-- **`Ytilde X` is a smooth manifold**, with the model `ℝ⁴ × ℝ¹⁰` of `Y13`. -/
theorem isManifold_tilde :
    letI := chartTilde (X := X)
    IsManifold 𝓘(ℝ, EY) ∞ (Ytilde X) :=
  isManifold_pull (E := EY) isLocalHomeomorph_piT

/-- **The projection is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_tilde :
    letI := chartTilde (X := X)
    IsLocalDiffeomorph 𝓘(ℝ, EY) 𝓘(ℝ, EY) ∞ (piT : Ytilde X → Y13o X) :=
  isLocalDiffeomorph_pull (E := EY) isLocalHomeomorph_piT

end

end GU.Library
