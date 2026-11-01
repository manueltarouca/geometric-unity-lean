import GU.Bundle.TimeCover

/-!
# Phase 5, items 5 and 6: `SO₀`-reduction and spin structure on the double cover, over `ℝ⁴`

Over `X = ℝ⁴`:

* **`exists_future_covector`**: a continuous future timelike covector `g` on all of `Ytilde ℝ⁴`, by a
  partition of unity, since the future cones are convex (`convex_future`). This uses that `Ytilde ℝ⁴`
  is Hausdorff (`t2_tilde`, with `t2_Y13_R4`), `σ`-compact (`sigmaCompact_tilde_R4`) and locally compact.
* **`quat`**: the matrix with rows `1·g, i·g, j·g, k·g` (quaternion products) is invertible for `g ≠ 0`, with
  first row `g`, continuous in `g` (informally, the parallelisation of `S³`).
* **`exists_frame_tilde`**: hence a **global frame** `F` of the chimeric bundle over `Ytilde ℝ⁴`:
  conjugate by `quat g`, so that `G₀₀ > 0`, and apply the Lorentzian Cholesky factor `gaugeP`.
* **`exists_SO0_reduction_cover`** (item 5): the pulled-back frame bundle `OFrT` has a clopen
  `SO₀`-reduction, meeting every fibre in exactly one coset.
* **`deck_not_SO0`**: it does not descend: the frames of the two sheets over the base point of the metric
  loop are not in one `SO₀`-orbit. This is `no_SO0_reduction_univ` seen on the cover.
* **`coverSpin`** (item 6): a `Spin⁺(7,7)` structure over the whole cover. `Φ_eq_iff` shows `Φ` is
  two-to-one, and `range_coverSpin` that its image is the reduction.

The frame `F` is not fully explicit: `g` comes from the partition of unity. The fibre of the cover is
expected to be homotopy equivalent to `S³` (informal, not used). General `X`: see `TimeReflection.lean`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### Over `ℝ⁴` the chart is unique -/

lemma cov_R4 (I : TimeIdx R4) (x : R4) : cov I x = I.2 := by
  have h : I.1 = (Zt R4).indexAt x := by
    apply Subtype.ext
    have h1 := I.1.2
    have h2 := ((Zt R4).indexAt x).2
    simp only [chartedSpaceSelf_atlas] at h1 h2
    exact h1.trans h2.symm
  obtain ⟨i, ξ⟩ := I
  obtain rfl : i = (Zt R4).indexAt x := h
  exact cov_index x ξ

lemma continuous_Gpt_R4 : Continuous fun y : Y13o R4 => Gpt (y : Yobs R4) := by
  let a : HomTotM R4 := pLoop (0 : R4) 0
  have h := (continuousOn_gaugeMetric a).comp_continuous (f := fun y : Y13o R4 => (y : Yobs R4))
    continuous_subtype_val (fun y => chartDom_R4 a _)
  refine h.congr fun y => ?_
  exact gaugeMetric_R4 a _

/-- The side function on `Y13(ℝ⁴)`: in `pt`, the covector and the pairing vary continuously. -/
theorem continuous_pt_R4 {Z : Type*} [TopologicalSpace Z] {y : Z → Y13o R4} {u : Z → R4}
    (hy : Continuous y) (hu : Continuous u) (ht : ∀ z, 0 < lp (Gpt (y z : Yobs R4)) (u z) (u z)) :
    Continuous fun z => pt (y z) (u z) := by
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hy.continuousAt, ?_⟩
  set I₀ := idxAt (y z₀) with hI₀
  set c₀ := I₀.2 with hc₀
  have hG : Continuous fun z => Gpt (y z : Yobs R4) := continuous_Gpt_R4.comp hy
  have hcov : ∀ x : R4, cov I₀ x = c₀ := fun x => cov_R4 I₀ x
  have hmem : ∀ᶠ z in 𝓝 z₀, y z ∈ tV I₀ :=
    hy.continuousAt.eventually ((isOpen_tV I₀).mem_nhds (mem_tV_idxAt (y z₀)))
  have hg : Continuous fun z => lp (Gpt (y z : Yobs R4)) (u z) c₀ := by
    have := continuous_lp (S := Set.univ) hG.continuousOn hu.continuousOn
      (continuousOn_const (c := c₀))
    exact continuousOn_univ.mp this
  have hc₀t : 0 < lp (Gpt (y z₀ : Yobs R4)) c₀ c₀ := by
    have := (mem_tV_idxAt (y z₀)).2
    unfold tb at this
    rwa [hcov] at this
  have hne : lp (Gpt (y z₀ : Yobs R4)) (u z₀) c₀ ≠ 0 := by
    obtain ⟨P, -, hGP⟩ := (y z₀).2
    exact lp_ne_zero hGP (ht z₀) hc₀t
  have hdec := (continuousOn_decide_neg (S := {z | lp (Gpt (y z : Yobs R4)) (u z) c₀ ≠ 0})
    hg.continuousOn fun z hz => hz).continuousAt
    ((isOpen_ne_fun hg continuous_const).mem_nhds hne)
  refine hdec.congr ?_
  filter_upwards [hmem] with z hz
  show _ = (FiberBundleCore.localTriv (tildeCore R4) (idxAt (y z₀)) (pt (y z) (u z))).2
  rw [FiberBundleCore.localTriv_apply]
  show _ = xor (decide (lp _ (cov (idxAt (y z)) (baseX (y z))) (u z) < 0))
    (decide (tb (idxAt (y z)) I₀ (y z) < 0))
  obtain ⟨P, -, hGP⟩ := (y z).2
  have hcz : 0 < lp (Gpt (y z : Yobs R4)) (cov (idxAt (y z)) (baseX (y z))) (cov (idxAt (y z)) (baseX (y z))) :=
    (mem_tV_idxAt (y z)).2
  have hI : 0 < lp (Gpt (y z : Yobs R4)) c₀ c₀ := by
    have := hz.2
    unfold tb at this
    rwa [hcov] at this
  have hco := lp_sign_cocycle hGP (ht z) hcz hI
  have e1 : tb (idxAt (y z)) I₀ (y z) =
      lp (Gpt (y z : Yobs R4)) (cov (idxAt (y z)) (baseX (y z))) c₀ := by
    unfold tb
    rw [hcov]
  rw [e1, lp_comm hGP (cov (idxAt (y z)) (baseX (y z))) (u z), hco]

/-! ### Topology of the cover over `ℝ⁴` -/

instance t2_Y13_R4 : T2Space (Y13o R4) := by
  have hc : Continuous fun y : Y13o R4 => (baseX y, Gpt (y : Yobs R4)) :=
    continuous_baseX.prodMk continuous_Gpt_R4
  refine T2Space.of_injective_continuous ?_ hc
  rintro y y' h
  have h1 : baseX y = baseX y' := congrArg Prod.fst h
  have h2 : Gpt (y : Yobs R4) = Gpt (y' : Yobs R4) := congrArg Prod.snd h
  obtain ⟨Q, hQ, hG⟩ := y.2
  rw [eq_mkY y hQ hG, eq_mkY y' hQ (h2 ▸ hG)]
  show mkY (baseX y) Q hQ = mkY (baseX y') Q hQ
  rw [h1]

/-- A parametrisation of `Ytilde ℝ⁴`. -/
def parT (z : R4 × {Q : M4 // IsUnit Q} × Bool) : Ytilde R4 :=
  pt (mkY z.1 z.2.1.1 z.2.1.2) (flipIf z.2.2 ((z.2.1.1ᵀ)⁻¹ *ᵥ Pi.single 0 1))

lemma isUnit_transpose' {Q : M4} (hQ : IsUnit Q) : IsUnit Qᵀ := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
  exact hQ

lemma lp_invTr {Q : M4} (hQ : IsUnit Q) :
    lp (Q * ηR * Qᵀ) ((Qᵀ)⁻¹ *ᵥ Pi.single 0 1) ((Qᵀ)⁻¹ *ᵥ Pi.single 0 1) = 1 := by
  have hc : Qᵀ *ᵥ ((Qᵀ)⁻¹ *ᵥ (Pi.single 0 1 : R4)) = Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose' hQ)), Matrix.one_mulVec]
  rw [lp_frame rfl, hc, lp_eta]
  simp

lemma continuous_mkSym' {Z : Type*} [TopologicalSpace Z] {x : Z → R4} {s : Z → Fin 10 → ℝ}
    (hx : Continuous x) (hs : Continuous s) :
    Continuous fun z => (⟨x z, s z⟩ : Sym2TX R4) := by
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hx.continuousAt, ?_⟩
  have h : ∀ z, ((trivializationAt (Fin 10 → ℝ) (symCore (Zt R4)).Fiber (x z₀))
      (⟨x z, s z⟩ : Sym2TX R4)).2 = s z := fun z =>
    (symCore (Zt R4)).coordChange_self ((symCore (Zt R4)).indexAt (x z)) (x z)
      ((symCore (Zt R4)).mem_baseSet_at _) (s z)
  simp only [h]
  exact hs.continuousAt

lemma continuous_mkY' {Z : Type*} [TopologicalSpace Z] {x : Z → R4} {Q : Z → M4}
    (hx : Continuous x) (hQ : Continuous Q) (hu : ∀ z, IsUnit (Q z)) :
    Continuous fun z => mkY (x z) (Q z) (hu z) := by
  have hG : Continuous fun z => Q z * ηR * (Q z)ᵀ :=
    (hQ.matrix_mul continuous_const).matrix_mul hQ.matrix_transpose
  have hs : Continuous fun z => symCoords (Q z * ηR * (Q z)ᵀ) :=
    continuous_pi fun k => (continuous_apply_apply _ _).comp hG
  exact ((continuous_mkSym' hx hs).subtype_mk _).subtype_mk _

lemma continuous_parT : Continuous parT := by
  have hxc : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool => z.1 := continuous_fst
  have hQc : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool => z.2.1.1 :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hinv : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool => (z.2.1.1ᵀ)⁻¹ := by
    have := continuousOn_inv_of_unit (A := Set.univ) (hQc.matrix_transpose.continuousOn)
      (fun z _ => isUnit_transpose' z.2.1.2)
    exact continuousOn_univ.mp this
  have hflip : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool =>
      flipIf z.2.2 ((z.2.1.1ᵀ)⁻¹ *ᵥ Pi.single 0 1) := by
    have hb : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool => z.2.2 :=
      continuous_snd.comp continuous_snd
    have hv : Continuous fun z : R4 × {Q : M4 // IsUnit Q} × Bool => (z.2.1.1ᵀ)⁻¹ *ᵥ (Pi.single 0 1 : R4) :=
      hinv.matrix_mulVec continuous_const
    have hF : Continuous fun t : Bool × R4 => flipIf t.1 t.2 := by
      refine continuous_prod_of_discrete_left.mpr fun b => ?_
      cases b
      · exact continuous_id
      · exact continuous_neg
    exact hF.comp (hb.prodMk hv)
  refine continuous_pt_R4 (continuous_mkY' hxc hQc fun z => z.2.1.2) hflip fun z => ?_
  rw [Gpt_mkY, lp_flipIf_self]
  rw [lp_invTr z.2.1.2]
  exact one_pos

lemma surjective_parT : Function.Surjective parT := by
  intro p
  obtain ⟨Q, hQ, hG⟩ := p.proj.2
  have hy : p.proj = mkY (baseX p.proj) Q hQ := eq_mkY p.proj hQ hG
  have hu : 0 < lp (Gpt (p.proj : Yobs R4)) ((Qᵀ)⁻¹ *ᵥ Pi.single 0 1) ((Qᵀ)⁻¹ *ᵥ Pi.single 0 1) := by
    rw [hG, lp_invTr hQ]; exact one_pos
  rcases eq_pt_or p hu with h | h
  · refine ⟨(baseX p.proj, ⟨Q, hQ⟩, false), ?_⟩
    rw [h]
    show pt (mkY (baseX p.proj) Q hQ) _ = pt p.proj _
    rw [← hy]; rfl
  · refine ⟨(baseX p.proj, ⟨Q, hQ⟩, true), ?_⟩
    rw [h]
    show pt (mkY (baseX p.proj) Q hQ) _ = pt p.proj _
    rw [← hy]; rfl

instance : SecondCountableTopology M4 := inferInstanceAs (SecondCountableTopology (Fin 4 → Fin 4 → ℝ))

instance : LocallyCompactSpace M4 := inferInstanceAs (LocallyCompactSpace (Fin 4 → Fin 4 → ℝ))

instance : LocallyCompactSpace {Q : M4 // IsUnit Q} := by
  have hO : IsOpen {Q : M4 | IsUnit Q} := by
    have : {Q : M4 | IsUnit Q} = (fun Q : M4 => Q.det) ⁻¹' {0}ᶜ := by
      ext Q
      simp [Matrix.isUnit_iff_isUnit_det]
    rw [this]
    exact isOpen_compl_singleton.preimage continuous_id.matrix_det
  exact hO.locallyCompactSpace

instance : SecondCountableTopology {Q : M4 // IsUnit Q} :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance : SigmaCompactSpace {Q : M4 // IsUnit Q} :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-- **`Ytilde ℝ⁴` is `σ`-compact.** -/
instance sigmaCompact_tilde_R4 : SigmaCompactSpace (Ytilde R4) := by
  rw [← isSigmaCompact_univ_iff, ← surjective_parT.range_eq]
  exact isSigmaCompact_range continuous_parT

instance locallyCompact_tilde_R4 : LocallyCompactSpace (Ytilde R4) :=
  letI := chartTilde (X := R4)
  ChartedSpace.locallyCompactSpace EY (Ytilde R4)

/-! ### A global future covector -/

lemma lp_comb_left (G : M4) (v w u : R4) (a b : ℝ) :
    lp G (a • v + b • w) u = a * lp G v u + b * lp G w u := by
  simp [lp, add_dotProduct, smul_dotProduct]

lemma lp_comb_right (G : M4) (u v w : R4) (a b : ℝ) :
    lp G u (a • v + b • w) = a * lp G u v + b * lp G u w := by
  simp [lp, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]

/-- **Future cones are convex.** -/
theorem convex_future (p : Ytilde R4) : Convex ℝ (future p) := by
  obtain ⟨P, -, hG⟩ := p.proj.2
  have hr := timelike_rep p
  rintro v ⟨hv, hvr⟩ w ⟨hw, hwr⟩ a b ha hb hab
  set G := Gpt (p.proj : Yobs R4) with hGdef
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

/-- The local trivialisation at `I` reads the side of `I`. -/
lemma localTriv_snd (I : TimeIdx R4) (p : Ytilde R4) (hp : p.proj ∈ tV I) :
    ((tildeCore R4).localTriv I p).2 = decide (lp (Gpt (p.proj : Yobs R4)) (rep p) I.2 < 0) := by
  rw [localTriv_snd_cov I p hp, cov_R4]

/-- **The covector of a point stays future nearby.** -/
lemma eventually_mem_future (p₀ : Ytilde R4) : ∃ c : R4, ∀ᶠ p in 𝓝 p₀, c ∈ future p := by
  refine ⟨rep p₀, ?_⟩
  set I₀ : TimeIdx R4 := ((Zt R4).indexAt (baseX p₀.proj), rep p₀) with hI
  have hc := timelike_rep p₀
  have hmem : p₀.proj ∈ tV I₀ := by
    refine ⟨(Zt R4).mem_baseSet_at _, ?_⟩
    unfold tb
    rw [cov_R4 I₀]
    exact hc
  have hsrc : p₀ ∈ ((tildeCore R4).localTriv I₀).source := by
    rw [Trivialization.mem_source]; exact hmem
  have hcont := (((tildeCore R4).localTriv I₀).continuousOn.continuousAt
    (((tildeCore R4).localTriv I₀).open_source.mem_nhds hsrc)).snd
  have hval : ((tildeCore R4).localTriv I₀ p₀).2 = false := by
    rw [localTriv_snd I₀ p₀ hmem]
    simp [I₀, not_lt.mpr hc.le]
  have hev : ∀ᶠ p in 𝓝 p₀, ((tildeCore R4).localTriv I₀ p).2 = false := by
    filter_upwards [hcont.preimage_mem_nhds ((isOpen_discrete ({false} : Set Bool)).mem_nhds
      (Set.mem_singleton_iff.mpr hval))] with p hp
    exact hp
  have hbase : ∀ᶠ p in 𝓝 p₀, p.proj ∈ tV I₀ :=
    continuous_piT.continuousAt.eventually ((isOpen_tV I₀).mem_nhds hmem)
  filter_upwards [hev, hbase] with p h1 h2
  rw [localTriv_snd I₀ p h2] at h1
  obtain ⟨P, -, hG⟩ := p.proj.2
  have ht : 0 < lp (Gpt (p.proj : Yobs R4)) (rep p₀) (rep p₀) := by
    have := h2.2; unfold tb at this; rwa [cov_R4 I₀] at this
  have hne := lp_ne_zero hG (timelike_rep p) ht
  have hpos : 0 < lp (Gpt (p.proj : Yobs R4)) (rep p) (rep p₀) :=
    lt_of_le_of_ne (not_lt.mp (by simpa [I₀] using h1)) hne.symm
  exact ⟨ht, by rw [lp_comm hG]; exact hpos⟩

/-- **A continuous future timelike covector on the whole cover.** -/
theorem exists_future_covector : ∃ g : C(Ytilde R4, R4), ∀ p, g p ∈ future p :=
  exists_continuous_forall_mem_convex_of_local_const convex_future eventually_mem_future

/-! ### The quaternion trivialisation -/

/-- **The quaternion matrix of `g`**: rows `1·g, i·g, j·g, k·g`; first row `g`, rows orthogonal of norm `|g|`. -/
def quat (g : R4) : M4 :=
  !![g 0, g 1, g 2, g 3;
     -g 1, g 0, -g 3, g 2;
     -g 2, g 3, g 0, -g 1;
     -g 3, -g 2, g 1, g 0]

lemma quat_mul_transpose (g : R4) :
    quat g * (quat g)ᵀ = (g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2) • (1 : M4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma continuous_quat : Continuous quat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [quat] <;> fun_prop

lemma isUnit_quat {g : R4} (hg : g ≠ 0) : IsUnit (quat g) := by
  have hn : g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2 ≠ 0 := by
    intro h
    apply hg
    have h0 : g 0 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h1 : g 1 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h2 : g 2 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h3 : g 3 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    ext i; fin_cases i <;> simp [h0, h1, h2, h3]
  have hm : quat g * ((g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2)⁻¹ • (quat g)ᵀ) = 1 := by
    rw [Matrix.mul_smul, quat_mul_transpose, smul_smul, inv_mul_cancel₀ hn, one_smul]
  exact IsUnit.of_mul_eq_one _ hm

/-- The first diagonal entry after conjugating by `quat g` is the norm of `g`. -/
lemma quat_conj_zero (G : M4) (g : R4) : (quat g * G * (quat g)ᵀ) 0 0 = lp G g g := by
  simp [lp, quat, Matrix.mul_apply, Fin.sum_univ_four, dotProduct, Matrix.mulVec, Matrix.vecMul]
  ring

/-- If `P ηR Pᵀ = Q ηR Qᵀ` with `Q` invertible, then `P` is invertible. -/
lemma isUnit_of_eta_eq {P Q : M4} (hQ : IsUnit Q) (h : P * ηR * Pᵀ = Q * ηR * Qᵀ) : IsUnit P := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have he : (ηR : M4).det = -1 := by
    rw [GU.Iso77.ηR_eq]; simp [ηr, Matrix.det_diagonal, Fin.prod_univ_four]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, he] at hd
  have hQd : Q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hQ).ne_zero
  have : Q.det * Q.det = 0 := by linarith
  exact hQd (mul_self_eq_zero.mp this)

/-! ### The global Lorentz frame and the global frame of `C` over the cover -/

/-- A continuous future covector on the cover, fixed once. -/
def gF : C(Ytilde R4, R4) := exists_future_covector.choose

lemma gF_future (p : Ytilde R4) : gF p ∈ future p := exists_future_covector.choose_spec p

lemma gF_ne (p : Ytilde R4) : gF p ≠ 0 := by
  intro h
  have := (gF_future p).1
  rw [h] at this
  simp [lp] at this

/-- The metric of `p`, conjugated so that `dx⁰` is timelike. -/
def conjG (p : Ytilde R4) : M4 := quat (gF p) * Gpt (p.proj : Yobs R4) * (quat (gF p))ᵀ

lemma conjG_mem (p : Ytilde R4) : conjG p ∈ gaugeSet := by
  obtain ⟨Q, hQ, hG⟩ := p.proj.2
  have hu := (isUnit_quat (gF_ne p)).mul hQ
  have h : conjG p = (quat (gF p) * Q) * ηR * (quat (gF p) * Q)ᵀ := by
    unfold conjG; rw [hG, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  refine (mem_gaugeSet_iff hu h).mpr ?_
  unfold conjG
  rw [quat_conj_zero]
  exact (gF_future p).1

lemma conjG_symm (p : Ytilde R4) : (conjG p).IsSymm := by
  obtain ⟨Q, -, hG⟩ := p.proj.2
  unfold conjG Matrix.IsSymm
  have hs : (Gpt (p.proj : Yobs R4))ᵀ = Gpt (p.proj : Yobs R4) := symMat_isSymm _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]

/-- **The Lorentz frame over the cover.** -/
def Pf (p : Ytilde R4) : M4 := (quat (gF p))⁻¹ * gaugeP (conjG p)

lemma Pf_eq (p : Ytilde R4) : Pf p * ηR * (Pf p)ᵀ = Gpt (p.proj : Yobs R4) := by
  have hu := isUnit_quat (gF_ne p)
  have hd : IsUnit (quat (gF p)).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hL := gaugeP_eq (conjG_symm p) (conjG_mem p)
  unfold Pf
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc (quat (gF p))⁻¹ * gaugeP (conjG p) * ηR * ((gaugeP (conjG p))ᵀ * ((quat (gF p))ᵀ)⁻¹)
      = (quat (gF p))⁻¹ * (gaugeP (conjG p) * ηR * (gaugeP (conjG p))ᵀ) * ((quat (gF p))ᵀ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (quat (gF p))⁻¹ * conjG p * ((quat (gF p))ᵀ)⁻¹ := by rw [hL]
    _ = _ := by
        unfold conjG
        have h1 : (quat (gF p))⁻¹ * quat (gF p) = 1 := Matrix.nonsing_inv_mul _ hd
        have h2 : (quat (gF p))ᵀ * ((quat (gF p))ᵀ)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hd)
        calc (quat (gF p))⁻¹ * (quat (gF p) * Gpt (p.proj : Yobs R4) * (quat (gF p))ᵀ) * ((quat (gF p))ᵀ)⁻¹
            = ((quat (gF p))⁻¹ * quat (gF p)) * Gpt (p.proj : Yobs R4) *
                ((quat (gF p))ᵀ * ((quat (gF p))ᵀ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [h1, h2]; simp

lemma isUnit_Pf (p : Ytilde R4) : IsUnit (Pf p) := by
  obtain ⟨Q, hQ, hG⟩ := p.proj.2
  exact isUnit_of_eta_eq hQ ((Pf_eq p).trans hG)

lemma continuous_Pf : Continuous Pf := by
  have hg : Continuous fun p : Ytilde R4 => quat (gF p) := continuous_quat.comp gF.continuous
  have hG : Continuous fun p : Ytilde R4 => Gpt (p.proj : Yobs R4) :=
    continuous_Gpt_R4.comp continuous_piT
  have hc : Continuous conjG := (hg.matrix_mul hG).matrix_mul hg.matrix_transpose
  have hL : Continuous fun p => gaugeP (conjG p) :=
    continuousOn_gaugeP.comp_continuous hc conjG_mem
  have hi : Continuous fun p : Ytilde R4 => (quat (gF p))⁻¹ :=
    continuousOn_univ.mp (continuousOn_inv_of_unit (A := Set.univ) hg.continuousOn
      fun p _ => isUnit_quat (gF_ne p))
  exact hi.matrix_mul hL

/-- The base point of the frame bundle charts. -/
def a₀ : HomTotM R4 := pLoop (0 : R4) 0

/-- The frame with Lorentz matrix `P`, in the chart at `a₀`. -/
def frameAt (y : Yobs R4) (P : M4) : HomTotM R4 :=
  (chartAt HomModel a₀).symm (pairHM (cYp a₀ y) (tpF P))

lemma frameAt_mem (y : Yobs R4) {P : M4} (hu : IsUnit P) (hG : Gpt y = P * ηR * Pᵀ) :
    frameAt y P ∈ OFr R4 := by
  have hdom : y ∈ chartDom a₀ := chartDom_R4 a₀ y
  have hT := pair_mem_target a₀ hdom (tpF P)
  show Fframe ((chartAt HomModel a₀).symm _) = ⟨η77, ηSig_mem 7 7⟩
  rw [Fframe_chart a₀ hT]
  apply Subtype.ext
  set s := (cYp a₀ y).2
  set h := tpF P
  show (symP 14 (bil (Gchim s) (homMat.symm h) (homMat.symm h)) : Mat 14) = η77
  have hb : bil (Gchim s) (homMat.symm h) (homMat.symm h) = η77 := by
    funext i j
    rw [bil_homMat_entry]
    have hS : symMat s = P * ηR * Pᵀ := by
      rw [← hG, ← gaugeMetric_R4 a₀ y]
      rfl
    show Bmod (symMat s) (tpF P _) (tpF P _) = _
    rw [hS, tpF_of_unit hu, tpFrame_apply, tpFrame_apply, TP_isometry, Bη_Φ_eq, Bm_singles]
  rw [hb, symP_of_mem (ηSig_mem 7 7)]

lemma proj_frameAt (y : Yobs R4) (P : M4) : (frameAt y P).proj = y := by
  have hy : y ∈ chartDom a₀ := chartDom_R4 a₀ y
  have hT := pair_mem_target a₀ hy (tpF P)
  have hsrc := (chartAt HomModel a₀).map_target hT
  have h1 := chart_fst a₀ _ hsrc
  have h2 : (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a₀ (frameAt y P)).1) = cYp a₀ y := by
    show (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a₀
      ((chartAt HomModel a₀).symm (pairHM (cYp a₀ y) (tpF P)))).1) = _
    rw [(chartAt HomModel a₀).right_inv hT]; rfl
  exact (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a₀.proj).injOn
    (proj_mem_chart_source a₀ _ hsrc) hy.2 (h1.symm.trans h2)

/-- **The global frame of the chimeric bundle over the cover.** -/
def Ff (p : Ytilde R4) : OFr R4 :=
  ⟨frameAt (p.proj : Yobs R4) (Pf p), frameAt_mem _ (isUnit_Pf p) (Pf_eq p).symm⟩

lemma proj_Ff (p : Ytilde R4) : projOFr (Ff p) = piT p :=
  Subtype.ext (proj_frameAt _ _)

lemma continuous_Ff : Continuous Ff := by
  refine Continuous.subtype_mk ?_ _
  have hy : Continuous fun p : Ytilde R4 => (p.proj : Yobs R4) :=
    continuous_subtype_val.comp continuous_piT
  have hc : Continuous fun p : Ytilde R4 => cYp a₀ (p.proj : Yobs R4) :=
    (continuousOn_cYp a₀).comp_continuous hy fun _ => chartDom_R4 a₀ _
  have hF : Continuous fun p : Ytilde R4 => tpF (Pf p) :=
    continuousOn_univ.mp (continuousOn_tpF (A := Set.univ) continuous_Pf.continuousOn
      fun p _ => isUnit_Pf p)
  have hpair : Continuous fun p : Ytilde R4 => pairHM (cYp a₀ (p.proj : Yobs R4)) (tpF (Pf p)) :=
    hc.prodMk hF
  exact (chartAt HomModel a₀).continuousOn_symm.comp_continuous hpair
    fun p => pair_mem_target a₀ (chartDom_R4 a₀ _) _

/-- **A global frame of the chimeric bundle over the whole cover of `Y13(ℝ⁴)`.** -/
theorem exists_frame_tilde :
    ∃ F : Ytilde R4 → OFr R4, Continuous F ∧ ∀ p, projOFr (F p) = piT p :=
  ⟨Ff, continuous_Ff, proj_Ff⟩

/-! ### Item 5: the reduction of the pulled-back frame bundle -/

section General

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **The frame bundle pulled back to the cover.** -/
def OFrT (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Type :=
  {z : Ytilde X × OFr X // piT z.1 = projOFr z.2}

instance : TopologicalSpace (OFrT X) := instTopologicalSpaceSubtype

/-- The action on the pulled-back frames. -/
def actT (z : OFrT X) (g : O77) : OFrT X :=
  ⟨(z.1.1, actOFr' z.1.2 g), by rw [projOFr_act]; exact z.2⟩

lemma actT_mul (z : OFrT X) (g h : O77) : actT (actT z g) h = actT z (g * h) := by
  apply Subtype.ext
  show (z.1.1, actOFr' (actOFr' z.1.2 g) h) = (z.1.1, actOFr' z.1.2 (g * h))
  rw [actOFr'_mul]

end General

/-- The transition from the global frame. -/
def trF (z : OFrT R4) : O77 :=
  (exists_act_eq (Ff z.1.1) z.1.2 ((proj_Ff _).trans z.2)).choose

lemma trF_spec (z : OFrT R4) : actOFr' (Ff z.1.1) (trF z) = z.1.2 :=
  (exists_act_eq (Ff z.1.1) z.1.2 ((proj_Ff _).trans z.2)).choose_spec

lemma trF_unique (z : OFrT R4) {g : O77} (h : actOFr' (Ff z.1.1) g = z.1.2) : trF z = g :=
  actOFr'_cancel ((trF_spec z).trans h.symm)

lemma continuous_trF : Continuous trF := by
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  let _ := regCharted (Fframe_regular (X := R4))
  have _ := isManifold_regularLevel (Fframe_regular (X := R4))
  obtain ⟨V', hV', hz₀, σ', τ', -, -, hτ', hrec⟩ :=
    (frameBundle (X := R4)).locTriv (projOFr z₀.1.2)
  have hτc : ContinuousOn τ' (projOFr ⁻¹' V') := hτ'.continuousOn
  have hq : Continuous fun z : OFrT R4 => z.1.2 := continuous_snd.comp continuous_subtype_val
  have hp : Continuous fun z : OFrT R4 => Ff z.1.1 :=
    continuous_Ff.comp (continuous_fst.comp continuous_subtype_val)
  set N : Set (OFrT R4) := {z | projOFr z.1.2 ∈ V'}
  have hN : IsOpen N := hV'.preimage (continuous_projOFr.comp hq)
  have hmem : N ∈ 𝓝 z₀ := hN.mem_nhds hz₀
  have hform : ∀ z ∈ N, trF z = (τ' (Ff z.1.1))⁻¹ * τ' z.1.2 := by
    intro z hz
    apply trF_unique
    set y := projOFr z.1.2
    have hy : projOFr (Ff z.1.1) = y := (proj_Ff _).trans z.2
    have e1 : actOFr' (σ' y) (τ' (Ff z.1.1)) = Ff z.1.1 := by
      have := hrec (Ff z.1.1) (by show projOFr (Ff z.1.1) ∈ V'; rw [hy]; exact hz)
      rw [show (frameBundle (X := R4)).proj (Ff z.1.1) = y from hy] at this
      exact this
    calc actOFr' (Ff z.1.1) ((τ' (Ff z.1.1))⁻¹ * τ' z.1.2)
        = actOFr' (actOFr' (σ' y) (τ' (Ff z.1.1))) ((τ' (Ff z.1.1))⁻¹ * τ' z.1.2) := by rw [e1]
      _ = actOFr' (σ' y) (τ' z.1.2) := by rw [actOFr'_mul, mul_inv_cancel_left]
      _ = z.1.2 := hrec z.1.2 hz
  have h1 : ContinuousOn (fun z : OFrT R4 => τ' (Ff z.1.1)) N :=
    hτc.comp hp.continuousOn fun z hz => by
      show projOFr (Ff z.1.1) ∈ V'
      rw [(proj_Ff _).trans z.2]; exact hz
  have h2 : ContinuousOn (fun z : OFrT R4 => τ' z.1.2) N :=
    hτc.comp hq.continuousOn fun z hz => hz
  have hc : ContinuousOn (fun z : OFrT R4 => (τ' (Ff z.1.1))⁻¹ * τ' z.1.2) N := h1.inv.mul h2
  exact (hc.congr hform).continuousAt hmem

lemma trF_act (z : OFrT R4) (g : O77) : trF (actT z g) = trF z * g := by
  apply trF_unique
  show actOFr' (Ff z.1.1) (trF z * g) = actOFr' z.1.2 g
  rw [← actOFr'_mul, trF_spec]

/-- The reduction: frames in the `SO₀`-orbit of the global frame. -/
def QT : Set (OFrT R4) := trF ⁻¹' (SO0 : Subgroup O77)

/-- **Item 5: over `ℝ⁴`, the frame bundle pulled back to the cover has a clopen `SO₀`-reduction.** It
meets every fibre in exactly one `SO₀`-coset. Compare `no_SO0_reduction_univ` on `Y13` itself. -/
theorem QT_reduction :
    IsClopen QT ∧
      (∀ z ∈ QT, ∀ g ∈ SO0, actT z g ∈ QT) ∧
      (∀ p : Ytilde R4, ∃ z ∈ QT, z.1.1 = p) ∧
      (∀ z ∈ QT, ∀ z' ∈ QT, z.1.1 = z'.1.1 → ∃ g ∈ SO0, actT z g = z') := by
  have hact := trF_act
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨isClosed_connectedComponent.preimage continuous_trF,
      isOpen_SO0.preimage continuous_trF⟩
  · intro z hz g hg
    show trF (actT z g) ∈ (SO0 : Subgroup O77)
    rw [hact]
    exact mul_mem hz hg
  · intro p
    let z : OFrT R4 := ⟨(p, Ff p), (proj_Ff p).symm⟩
    refine ⟨z, ?_, rfl⟩
    have : trF z = 1 := trF_unique z (actOFr'_one _)
    show trF z ∈ (SO0 : Subgroup O77)
    rw [this]; exact one_mem _
  · rintro ⟨⟨p, q⟩, hz⟩ hzQ ⟨⟨p', q'⟩, hz'⟩ hzQ' hpp
    obtain rfl : p = p' := hpp
    set z : OFrT R4 := ⟨(p, q), hz⟩
    set z' : OFrT R4 := ⟨(p, q'), hz'⟩
    refine ⟨(trF z)⁻¹ * trF z', mul_mem (inv_mem hzQ) hzQ', ?_⟩
    apply Subtype.ext
    show (p, actOFr' q _) = (p, q')
    congr 1
    have e1 : actOFr' (Ff p) (trF z) = q := trF_spec z
    have e2 : actOFr' (Ff p) (trF z') = q' := trF_spec z'
    rw [← e1, actOFr'_mul, mul_inv_cancel_left]
    exact e2

/-- The existential form. -/
theorem exists_SO0_reduction_cover :
    ∃ Q : Set (OFrT R4), IsClopen Q ∧
      (∀ z ∈ Q, ∀ g ∈ SO0, actT z g ∈ Q) ∧
      (∀ p : Ytilde R4, ∃ z ∈ Q, z.1.1 = p) ∧
      (∀ z ∈ Q, ∀ z' ∈ Q, z.1.1 = z'.1.1 → ∃ g ∈ SO0, actT z g = z') :=
  ⟨QT, QT_reduction⟩

/-- **The reduction does not descend to `Y13`**: over the base point of the metric loop, the frames of
the two sheets are not in one `SO₀`-orbit. -/
theorem deck_not_SO0 (x : R4) {h : O77} (hh : h ∈ SO0) :
    actOFr' (Ff (pt (yO x 0) (-uLoop 0))) h ≠ Ff (pt (yO x 0) (uLoop 0)) := by
  intro he
  have hzp : ∀ θ, piT (pt (yO x θ) (uLoop θ)) = projOFr (pLoop x θ) := fun _ => rfl
  let z : ℝ → OFrT R4 := fun θ => ⟨(pt (yO x θ) (uLoop θ), pLoop x θ), hzp θ⟩
  have hzc : Continuous z :=
    ((continuous_lift_pos x).prodMk (continuous_pLoop x)).subtype_mk _
  let b : O77 := (trF (z 0))⁻¹
  have hact := trF_act
  have hf : Continuous fun θ => trF (actT (z θ) b) := by
    refine continuous_trF.comp (Continuous.subtype_mk ?_ _)
    exact (continuous_fst.comp (continuous_subtype_val.comp hzc)).prodMk
      (continuous_actOFr'.comp ((continuous_snd.comp (continuous_subtype_val.comp hzc)).prodMk
        continuous_const))
  have hcl : IsClopen ((fun θ => trF (actT (z θ) b)) ⁻¹' ((SO0 : Subgroup O77) : Set O77)) :=
    ⟨isClosed_connectedComponent.preimage hf, isOpen_SO0.preimage hf⟩
  have h0 : (0 : ℝ) ∈ (fun θ => trF (actT (z θ) b)) ⁻¹' ((SO0 : Subgroup O77) : Set O77) := by
    show trF (actT (z 0) b) ∈ (SO0 : Subgroup O77)
    rw [hact, mul_inv_cancel]
    exact one_mem _
  have huniv := hcl.eq_univ ⟨0, h0⟩
  have hpi : Real.pi ∈ (fun θ => trF (actT (z θ) b)) ⁻¹' ((SO0 : Subgroup O77) : Set O77) := by
    rw [huniv]; exact Set.mem_univ _
  set c := trF (actT (z Real.pi) b) with hc
  have hcSO : c ∈ SO0 := hpi
  have hspec : actOFr' (Ff (pt (yO x Real.pi) (uLoop Real.pi))) c =
      actOFr' (pLoop x Real.pi) b := trF_spec (actT (z Real.pi) b)
  have hpt : pt (yO x Real.pi) (uLoop Real.pi) = pt (yO x 0) (-uLoop 0) := by
    rw [yO_pi, uLoop_pi]
  have h1 : actOFr' (Ff (pt (yO x 0) (uLoop 0))) (trF (z 0)) = pLoop x 0 := trF_spec (z 0)
  rw [hpt] at hspec
  set t := trF (z 0) with ht
  set A := Ff (pt (yO x 0) (-uLoop 0))
  set B := Ff (pt (yO x 0) (uLoop 0))
  have hcalc : actOFr' A c = actOFr' A (h * t * gHol * t⁻¹) := by
    calc actOFr' A c = actOFr' (pLoop x Real.pi) t⁻¹ := hspec
      _ = actOFr' (actOFr' (pLoop x 0) gHol) t⁻¹ := by rw [pLoop_pi]
      _ = actOFr' (actOFr' (actOFr' B t) gHol) t⁻¹ := by rw [h1]
      _ = actOFr' (actOFr' (actOFr' (actOFr' A h) t) gHol) t⁻¹ := by rw [he]
      _ = _ := by simp only [actOFr'_mul]
  have hg : c = h * t * gHol * t⁻¹ := actOFr'_cancel hcalc
  have hconj : t * gHol * t⁻¹ = h⁻¹ * c := by rw [hg]; group
  refine gHol_not_mem_SO0 (conj_mem_SO0 t⁻¹ ?_)
  rw [inv_inv, hconj]
  exact mul_mem (inv_mem hh) hcSO

/-! ### Item 6: the spin structure on the cover -/

section General

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **A spin structure on the frames pulled back to the cover**: `SpinStructure` with base `Ytilde X` in
place of an open subset of `Y13`. An instance over `ℝ⁴` is `coverSpin`. The general lemmas of
`SpinStructure` (`Φ_eq_iff`, `isCoveringMap_Φ`) are not ported; for `coverSpin` the first is
`coverSpin_Φ_eq_iff`. -/
structure CoverSpin (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] where
  P : Type
  top : TopologicalSpace P
  projS : P → Ytilde X
  actS : P → Spin77 → P
  Φ : P → OFrT X
  act_one : ∀ p, actS p 1 = p
  act_mul : ∀ p s t, actS (actS p s) t = actS p (s * t)
  proj_act : ∀ p t, projS (actS p t) = projS p
  continuous_act : Continuous fun pt : P × Spin77 => actS pt.1 pt.2
  ι : Type
  e : ι → Trivialization Spin77 projS
  cover : ∀ b, ∃ i, b ∈ (e i).baseSet
  e_act : ∀ i, ∀ p ∈ (e i).source, ∀ t, e i (actS p t) = ((e i p).1, (e i p).2 * t)
  continuous_Φ : Continuous Φ
  proj_Φ : ∀ p, (Φ p).1.1 = projS p
  Φ_act : ∀ p t, Φ (actS p t) = actT (Φ p) (spinToO77 t)

end General

/-- The trivial principal bundle. -/
def prodTriv {B : Type*} [TopologicalSpace B] :
    Trivialization Spin77 (Prod.fst : B × Spin77 → B) where
  toOpenPartialHomeomorph := (Homeomorph.refl _).toOpenPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

/-- **Item 6: a `Spin⁺(7,7)` structure over the whole cover of `Y13(ℝ⁴)`**, the trivial bundle with the
map given by the global frame. -/
def coverSpin : CoverSpin R4 where
  P := Ytilde R4 × Spin77
  top := inferInstance
  projS := Prod.fst
  actS p t := (p.1, p.2 * t)
  Φ p := ⟨(p.1, actOFr' (Ff p.1) (spinToO77 p.2)), by rw [projOFr_act]; exact (proj_Ff _).symm⟩
  act_one p := by simp
  act_mul p s t := by simp [mul_assoc]
  proj_act _ _ := rfl
  continuous_act := by
    exact (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul continuous_snd)
  ι := Unit
  e _ := prodTriv
  cover _ := ⟨(), Set.mem_univ _⟩
  e_act _ _ _ _ := rfl
  continuous_Φ := by
    refine Continuous.subtype_mk (continuous_fst.prodMk ?_) _
    exact continuous_actOFr'.comp ((continuous_Ff.comp continuous_fst).prodMk
      (continuous_spinToO77.comp continuous_snd))
  proj_Φ _ := rfl
  Φ_act p t := by
    apply Subtype.ext
    show (p.1, actOFr' (Ff p.1) (spinToO77 (p.2 * t))) = (p.1, actOFr' (actOFr' (Ff p.1) (spinToO77 p.2)) (spinToO77 t))
    rw [map_mul, actOFr'_mul]

/-- **The map to the frames is two-to-one.** -/
theorem coverSpin_Φ_eq_iff (a b : Ytilde R4 × Spin77) :
    coverSpin.Φ a = coverSpin.Φ b ↔ a.1 = b.1 ∧ (b.2 = a.2 ∨ b.2 = a.2 * negOne) := by
  constructor
  · intro h
    have h1 : a.1 = b.1 := congrArg (fun z : OFrT R4 => z.1.1) h
    refine ⟨h1, ?_⟩
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p = p' := h1
    have h2 : actOFr' (Ff p) (spinToO77 s) = actOFr' (Ff p) (spinToO77 t) :=
      congrArg (fun z : OFrT R4 => z.1.2) h
    have h3 : spinToO77 s = spinToO77 t := actOFr'_cancel h2
    have h4 : spinToO77 (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, h3, inv_mul_cancel]
    rcases (spinToO77_eq_one_iff _).mp h4 with h5 | h5
    · left
      show t = s
      calc t = s * (s⁻¹ * t) := by group
        _ = s := by rw [h5, mul_one]
    · right
      show t = s * negOne
      calc t = s * (s⁻¹ * t) := by group
        _ = _ := by rw [h5]
  · rintro ⟨h1, h2⟩
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p = p' := h1
    apply Subtype.ext
    show (p, actOFr' (Ff p) (spinToO77 s)) = (p, actOFr' (Ff p) (spinToO77 t))
    rcases h2 with rfl | rfl
    · rfl
    · rw [map_mul, spinToO77_negOne, mul_one]

/-- **The image of the map is the reduction `QT`.** -/
theorem range_coverSpin : Set.range coverSpin.Φ = QT := by
  ext z
  constructor
  · rintro ⟨⟨p, t⟩, rfl⟩
    show trF _ ∈ (SO0 : Subgroup O77)
    rw [trF_unique (z := coverSpin.Φ (p, t)) (g := spinToO77 t) rfl]
    exact spinToO77_mem t
  · intro hz
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨trF z, hz⟩
    refine ⟨(z.1.1, t), Subtype.ext ?_⟩
    show (z.1.1, actOFr' (Ff z.1.1) (spinToO77 t)) = z.1
    rw [show spinToO77 t = trF z from congrArg Subtype.val ht, trF_spec]

end

end GU.Library
