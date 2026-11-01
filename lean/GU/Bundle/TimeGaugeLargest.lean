import GU.Bundle.SpinLargest

/-!
# Phase 4, item 4: `{G₀₀ > 0}` is the largest natural subset

Fix `X = ℝ⁴`. `HGauge` is the set of invertible `P` fixing the covector `dx⁰` up to scale (first row
`λ e₀ᵀ`), acting fibrewise on metrics by `G ↦ P G Pᵀ`; `G = g⁻¹` is contravariant, so
`timeGaugeLocus = {G₀₀ > 0}` says `dx⁰` is timelike. **`gauge_largest_iff`**: this locus is open,
`HGauge`-invariant, carries a global frame and a spin structure, and contains every
`HGauge`-invariant open subset of `Y13` carrying either.

**How much this says.** `HGauge` is the pointwise (linearised) symmetry of a time coordinate; this is
weaker than, hence covers, invariance under `x⁰`-preserving diffeomorphisms. It has three orbits per
fibre (the sign of `G₀₀`; informal, not formalised), so an invariant open set is fibrewise `∅`,
`{G₀₀ > 0}`, `{G₀₀ < 0}`, `{G₀₀ ≠ 0}` or everything. So "largest" is largely by elimination, and the
real content is, informally: **no open set containing the orbit `{G₀₀ < 0}` of a fibre carries a spin structure.**
The result is relative to the choice of covector: the "`∂₀` timelike" locus would need the first-column
group instead. Without an invariance requirement no largest open subset exists
(`no_largest_spinStructure`); a coordinate-free base (the double cover of `Y13`) is not addressed.

Proof: a point of `W` with `G₀₀ ≤ 0` gives one with `G₀₀ < 0` (`W` open), where `dx⁰` is spacelike. A
Lorentz reflection (`exists_reflection`, the `η`-reflection in `r − (0,0,ρ,0)`) writes `G = Q ηR Qᵀ`
with first row of `Q` equal to `(0,0,ρ,0)`, which `Rθ` fixes, so the loop `Q Rθ ηR Rθᵀ Qᵀ` stays in the
`HGauge`-orbit, hence in `W`, and its frame holonomy is `gHol ∉ SO₀`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### The path argument, for any frame path with holonomy `gHol` -/

/-- **A frame path over `W` with holonomy `gHol` excludes spin-lift data over `W`.** -/
theorem no_spinLiftData_of_path (D : SpinLiftData X) {p : ℝ → OFr X} (hp : Continuous p)
    (hW : ∀ θ, projOFr (p θ) ∈ D.W) (hπ : p Real.pi = actOFr' (p 0) gHol) : False := by
  obtain ⟨i, hi⟩ := D.cover (projOFr (p 0)) (hW 0)
  have hry : projOFr (p 0) = projOFr (D.σ i (projOFr (p 0))) := (D.proj_σ i _ hi).symm
  obtain ⟨h, hh⟩ := exists_act_eq _ _ hry
  have hf : Continuous fun θ => actOFr' (p θ) h :=
    continuous_actOFr'.comp (hp.prodMk continuous_const)
  have hstay := D.path_stays hf (fun θ => by rw [projOFr_act]; exact hW θ)
    (by rw [hh]; exact D.σ_mem_range i hi) Real.pi
  have hact : actOFr' (p Real.pi) h = actOFr' (D.σ i (projOFr (p 0))) (h⁻¹ * gHol * h) := by
    rw [hπ, ← hh, actOFr'_mul, actOFr'_mul]
    congr 1; group
  rw [hact] at hstay
  exact gHol_not_mem_SO0 (conj_mem_SO0 h (D.mem_SO0_of_act_mem i hi hstay))

/-! ### A Lorentz reflection -/

/-- A spacelike vector can be moved to `(0, 0, ρ, 0)` by a transformation preserving `ηR`. -/
lemma exists_reflection {r : Fin 4 → ℝ} (hr : etaF r r < 0) :
    ∃ (A : M4) (ρ : ℝ), Aᵀ * ηR * A = ηR ∧ A *ᵥ r = ![0, 0, ρ, 0] := by
  set R := Real.sqrt (-etaF r r)
  have hR : R * R = -etaF r r := Real.mul_self_sqrt (by linarith)
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨ρ, hρ2, hne⟩ : ∃ ρ : ℝ, ρ * ρ = R * R ∧ r 2 ≠ ρ := by
    by_cases h : r 2 = R
    · exact ⟨-R, by ring, by rw [h]; linarith⟩
    · exact ⟨R, rfl, h⟩
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ2; nlinarith
  -- `v = r - t`, `w = η v`, `n = v·w`
  let v : Fin 4 → ℝ := ![r 0, r 1, r 2 - ρ, r 3]
  let w : Fin 4 → ℝ := ![r 0, -r 1, -(r 2 - ρ), -r 3]
  set n : ℝ := r 0 * r 0 - r 1 * r 1 - (r 2 - ρ) * (r 2 - ρ) - r 3 * r 3 with hn
  have hrr : r 0 * r 0 - r 1 * r 1 - r 2 * r 2 - r 3 * r 3 = -(ρ * ρ) := by
    have : etaF r r = -(R * R) := by linarith
    rw [hρ2]; exact this
  have hnv : n = 2 * ρ * (r 2 - ρ) := by rw [hn]; nlinarith
  have hn0 : n ≠ 0 := by
    rw [hnv]; exact mul_ne_zero (mul_ne_zero two_ne_zero hρ0) (sub_ne_zero.mpr hne)
  let A : M4 := 1 - (2 / n) • Matrix.vecMulVec v w
  refine ⟨A, ρ, ?_, ?_⟩
  · rw [GU.Iso77.ηR_eq, ηr]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;>
      simp [A, v, w, Matrix.vecMulVec_apply, Matrix.one_apply] <;> field_simp <;> rw [hn] <;> ring
  · funext k
    have hkey : r 0 * r 0 - r 1 * r 1 - r 2 * (r 2 - ρ) - r 3 * r 3 = n / 2 := by
      rw [hnv]; nlinarith
    have hA : (A *ᵥ r) k = r k - (2 / n) * (v k *
        (r 0 * r 0 - r 1 * r 1 - r 2 * (r 2 - ρ) - r 3 * r 3)) := by
      show ((1 - (2 / n) • Matrix.vecMulVec v w) *ᵥ r) k = _
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four, Matrix.vecMulVec_apply]
      simp [w]
      first | exact Or.inl trivial | (left; ring) | ring
    rw [hA, hkey]
    have e : (2 / n) * (v k * (n / 2)) = v k := by field_simp
    rw [e]
    fin_cases k <;> simp [v]

/-! ### The loop through a general metric -/

/-- The metric `Q Rθ ηR Rθᵀ Qᵀ`. -/
def GQ (Q : M4) (θ : ℝ) : M4 := (Q * Rθ θ) * ηR * (Q * Rθ θ)ᵀ

lemma GQ_symm (Q : M4) (θ : ℝ) : (GQ Q θ).IsSymm := by
  unfold Matrix.IsSymm GQ
  generalize Q * Rθ θ = A
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  congr 2
  rw [GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose]

lemma isUnit_QR {Q : M4} (hQ : IsUnit Q) (θ : ℝ) : IsUnit (Q * Rθ θ) := hQ.mul (isUnit_Rθ θ)

lemma GQ_pi (Q : M4) : GQ Q Real.pi = GQ Q 0 := by
  have h : Rθ Real.pi * ηR * (Rθ Real.pi)ᵀ = Rθ 0 * ηR * (Rθ 0)ᵀ := by
    have h0 : Gθ 0 = ηR := by rw [Gθ, Rθ_zero]; simp
    have hp : Gθ Real.pi = ηR := by
      rw [Gθ, Rθ_pi, GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1; funext i; fin_cases i <;> simp
    exact hp.trans h0.symm
  unfold GQ
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc Q * Rθ Real.pi * ηR * ((Rθ Real.pi)ᵀ * Qᵀ) = Q * (Rθ Real.pi * ηR * (Rθ Real.pi)ᵀ) * Qᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Rθ 0 * ηR * (Rθ 0)ᵀ) * Qᵀ := by rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The frame `TP_{Q Rθ} ∘ Φ` along the loop. -/
def hQ (Q : M4) (θ : ℝ) : HomF := tpF (Q * Rθ θ)

lemma continuous_QR (Q : M4) : Continuous fun θ => Q * Rθ θ :=
  continuous_const.matrix_mul continuous_Rθ

lemma continuous_hQ {Q : M4} (hU : IsUnit Q) : Continuous (hQ Q) := by
  rw [← continuousOn_univ]
  exact continuousOn_tpF (continuous_QR Q).continuousOn fun θ _ => isUnit_QR hU θ

/-- `TP` is multiplicative. -/
lemma TP_mul_apply {P P' : M4} (hP : IsUnit P) (hP' : IsUnit P') (hPP : IsUnit (P * P')) (u : CFib) :
    TP (P * P') hPP u = TP P hP (TP P' hP' u) := by
  have hsym : (P' * symMat u.1 * P'ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      (symMat_isSymm _).eq, Matrix.mul_assoc]
  refine Prod.ext ?_ ?_
  · show symCoords (P * P' * symMat u.1 * (P * P')ᵀ) =
      symCoords (P * symMat (symCoords (P' * symMat u.1 * P'ᵀ)) * Pᵀ)
    rw [symMat_symCoords _ hsym, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  · show u.2.comp (toCLM (P * P')⁻¹) = (u.2.comp (toCLM P'⁻¹)).comp (toCLM P⁻¹)
    refine ContinuousLinearMap.ext fun w => ?_
    show u.2 ((P * P')⁻¹ *ᵥ w) = u.2 (P'⁻¹ *ᵥ (P⁻¹ *ᵥ w))
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev]

/-- **The holonomy of the general loop is `gHol`.** -/
lemma hQ_pi {Q : M4} (hU : IsUnit Q) : hQ Q Real.pi = (hQ Q 0).comp (matCLM gHolM) := by
  refine ContinuousLinearMap.ext fun v => ?_
  show tpF (Q * Rθ Real.pi) v = tpF (Q * Rθ 0) (matCLM gHolM v)
  rw [tpF_of_unit (isUnit_QR hU _), tpF_of_unit (isUnit_QR hU _), tpFrame_apply, tpFrame_apply,
    TP_mul_apply hU (isUnit_Rθ _), TP_mul_apply hU (isUnit_Rθ _), TP_Rθ_zero]
  have := congrArg (fun h : HomF => h v) hLoop_pi
  have e : TP (Rθ Real.pi) (isUnit_Rθ _) (ΦL v) = TP (Rθ 0) (isUnit_Rθ 0) (ΦL (matCLM gHolM v)) := this
  rw [e, TP_Rθ_zero]

/-! ### The action of the gauge group on `Y13(ℝ⁴)` -/

/-- **The matrices fixing `dx⁰` up to scale.** -/
def HGauge (P : M4) : Prop := IsUnit P ∧ ∃ l : ℝ, l ≠ 0 ∧ ∀ j, P 0 j = if j = 0 then l else 0

lemma mk_symm (P : M4) : (P * ηR * Pᵀ).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  congr 2
  rw [GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose]

lemma mem_Y13o_of {y : Yobs R4} {P : M4} (hP : IsUnit P) (h : Gpt y = P * ηR * Pᵀ) :
    y ∈ Y13o R4 := by
  show ∃ P' : M4, IsUnit P' ∧ Gpt y = P' * ηR * P'ᵀ
  exact ⟨P, hP, h⟩

lemma exists_Q (y : Y13o R4) : ∃ Q : M4, IsUnit Q ∧ Gpt (y : Yobs R4) = Q * ηR * Qᵀ := y.2

/-- The point of `Y` over `x` with metric `P ηR Pᵀ`. -/
def mkY0 (x : R4) (P : M4) (hP : IsUnit P) : Yobs R4 :=
  ⟨(⟨x, symCoords (P * ηR * Pᵀ)⟩ : Sym2TX R4), by
    show (symMat (symCoords (P * ηR * Pᵀ))).det < 0
    rw [symMat_symCoords _ (mk_symm P), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hd : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hP).ne_zero
    have he : (ηR : M4).det = -1 := by
      rw [GU.Iso77.ηR_eq]; simp [ηr, Matrix.det_diagonal, Fin.prod_univ_four]
    rw [he]; nlinarith [mul_self_pos.mpr hd]⟩

/-- The point of `Y13` over `x` with metric `P ηR Pᵀ`. -/
def mkY (x : R4) (P : M4) (hP : IsUnit P) : Y13o R4 :=
  ⟨mkY0 x P hP, mem_Y13o_of hP (symMat_symCoords _ (mk_symm P))⟩

lemma Gpt_mkY (x : R4) (P : M4) (hP : IsUnit P) : Gpt (mkY x P hP : Yobs R4) = P * ηR * Pᵀ :=
  symMat_symCoords _ (mk_symm P)

/-- A point of `Y13` is determined by its base point and metric. -/
lemma mkY_eq_of {x : R4} {P P' : M4} (hP : IsUnit P) (hP' : IsUnit P')
    (h : P * ηR * Pᵀ = P' * ηR * P'ᵀ) : mkY x P hP = mkY x P' hP' := by
  apply Subtype.ext; apply Subtype.ext
  show (⟨x, symCoords (P * ηR * Pᵀ)⟩ : Sym2TX R4) = ⟨x, symCoords (P' * ηR * P'ᵀ)⟩
  rw [h]

lemma eq_mkY (y : Y13o R4) {Q : M4} (hQ : IsUnit Q) (h : Gpt (y : Yobs R4) = Q * ηR * Qᵀ) :
    y = mkY (((y : Yobs R4) : Sym2TX R4).proj) Q hQ := by
  apply Subtype.ext; apply Subtype.ext
  have hs : symCoords (Q * ηR * Qᵀ) = ((y : Yobs R4) : Sym2TX R4).2 := by
    rw [← h]; exact symCoords_symMat _
  show ((y : Yobs R4) : Sym2TX R4) = (⟨((y : Yobs R4) : Sym2TX R4).proj, symCoords (Q * ηR * Qᵀ)⟩ : Sym2TX R4)
  rw [hs]

/-- The action `G ↦ P G Pᵀ`, fibrewise. -/
def gaugeAct (P : M4) (hP : IsUnit P) (y : Y13o R4) : Y13o R4 :=
  mkY (((y : Yobs R4) : Sym2TX R4).proj) (P * (exists_Q y).choose) (hP.mul (exists_Q y).choose_spec.1)

lemma Gpt_gaugeAct (P : M4) (hP : IsUnit P) (y : Y13o R4) :
    Gpt (gaugeAct P hP y : Yobs R4) = P * Gpt (y : Yobs R4) * Pᵀ := by
  rw [gaugeAct, Gpt_mkY]
  have e := (exists_Q y).choose_spec.2
  have h : ∀ Q' : M4, P * Q' * ηR * (P * Q')ᵀ = P * (Q' * ηR * Q'ᵀ) * Pᵀ := fun Q' => by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  exact (h _).trans (by rw [← e])

/-- `HGauge`-invariance of a subset of `Y13`. -/
def HInvariant (W : Set (Y13o R4)) : Prop :=
  ∀ y ∈ W, ∀ P (h : HGauge P), gaugeAct P h.1 y ∈ W

/-- `(P G Pᵀ)₀₀ = l² G₀₀`. -/
lemma gaugeAct_G00 {P : M4} (h : HGauge P) (y : Y13o R4) {l : ℝ}
    (hl : ∀ j, P 0 j = if j = 0 then l else 0) :
    Gpt (gaugeAct P h.1 y : Yobs R4) 0 0 = l * l * Gpt (y : Yobs R4) 0 0 := by
  rw [Gpt_gaugeAct, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, hl]
  simp; ring

/-- The locus `G₀₀ > 0`. -/
def timeGaugeLocus : Set (Y13o R4) := {y | 0 < Gpt (y : Yobs R4) 0 0}

lemma hInvariant_timeGaugeLocus : HInvariant timeGaugeLocus := by
  rintro y hy P h
  obtain ⟨l, hl0, hl⟩ := h.2
  show 0 < Gpt (gaugeAct P h.1 y : Yobs R4) 0 0
  rw [gaugeAct_G00 h y hl]
  have := mul_self_pos.mpr hl0
  exact mul_pos this hy

/-! ### Frames along the general loop -/

/-- The loop in `Y13`. -/
def yQ (x : R4) (Q : M4) (hQ' : IsUnit Q) (θ : ℝ) : Y13o R4 := mkY x (Q * Rθ θ) (isUnit_QR hQ' θ)

lemma continuous_yQ (x : R4) (Q : M4) (hU : IsUnit Q) : Continuous (yQ x Q hU) := by
  have hG : Continuous fun θ => (Q * Rθ θ) * ηR * (Q * Rθ θ)ᵀ :=
    ((continuous_QR Q).matrix_mul continuous_const).matrix_mul (continuous_QR Q).matrix_transpose
  have hs : Continuous fun θ => symCoords ((Q * Rθ θ) * ηR * (Q * Rθ θ)ᵀ) :=
    continuous_pi fun k => (continuous_apply_apply _ _).comp hG
  have h1 := (FiberBundle.continuous_totalSpaceMk (Fin 10 → ℝ) (symCore (Zt R4)).Fiber x).comp hs
  exact (h1.subtype_mk _).subtype_mk _

/-- The trivialisation of `C` depends only on the point of `X`. -/
lemma Tz_congr {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] (y0 z z' : Yobs X)
    (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet)
    (hz' : z' ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) (h : πY z = πY z') (u : CFib) :
    Tz y0 z hz u = Tz y0 z' hz' u := by
  refine Prod.ext ((Tz_fst' y0 z hz u).trans ?_) ((Tz_snd' y0 z hz u).trans ?_)
  · rw [Tz_fst' y0 z' hz' u]
    exact congrArg (fun b => ((trivializationAt (Fin 10 → ℝ) (symCore (Zt X)).Fiber (πY y0))
      ⟨b, u.1⟩).2) h
  · rw [Tz_snd' y0 z' hz' u]
    exact congrArg (fun b => ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ)
        (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ) (πY y0))
        ⟨b, u.2⟩).2) h

/-- The frame path. -/
def qQ (x : R4) (Q : M4) (hU : IsUnit Q) (θ : ℝ) : HomTotM R4 := ⟨(yQ x Q hU θ : Yobs R4), hQ Q θ⟩

lemma qQ_mem (x : R4) (Q : M4) (hU : IsUnit Q) (θ : ℝ) : qQ x Q hU θ ∈ AFr R4 := by
  have h := tpFrame_mem (yQ x Q hU θ : Yobs R4) (Q * Rθ θ) (isUnit_QR hU θ) (Gpt_mkY x _ _)
  show (⟨_, tpF (Q * Rθ θ)⟩ : HomTotM R4) ∈ AFr R4
  rw [tpF_of_unit (isUnit_QR hU θ)]; exact h

lemma yQ_mem_baseSet (x : R4) (Q : M4) (hU : IsUnit Q) (θ θ₀ : ℝ) :
    (yQ x Q hU θ : Yobs R4) ∈ (trivializationAt CFib (Cb (X := R4)) (yQ x Q hU θ₀ : Yobs R4)).baseSet := by
  rw [Cb_baseSet]
  exact (Zt R4).mem_baseSet_at x

lemma piY_yQ (x : R4) (Q : M4) (hU : IsUnit Q) (θ : ℝ) : πY (yQ x Q hU θ : Yobs R4) = x := rfl

lemma Tz_yQ (x : R4) (Q : M4) (hU : IsUnit Q) (θ θ₀ : ℝ) (u : CFib) :
    Tz (yQ x Q hU θ₀ : Yobs R4) (yQ x Q hU θ : Yobs R4) (yQ_mem_baseSet x Q hU θ θ₀) u =
      Tz (yQ x Q hU θ₀ : Yobs R4) (yQ x Q hU θ₀ : Yobs R4) (yQ_mem_baseSet x Q hU θ₀ θ₀) u :=
  Tz_congr _ _ _ _ _ ((piY_yQ x Q hU θ).trans (piY_yQ x Q hU θ₀).symm) u

lemma triv_qQ (x : R4) (Q : M4) (hU : IsUnit Q) (θ θ₀ : ℝ) :
    ((trivializationAt HomF (HomCb (X := R4)) (yQ x Q hU θ₀ : Yobs R4)) (qQ x Q hU θ)).2 =
      ((Tz (yQ x Q hU θ₀ : Yobs R4) (yQ x Q hU θ₀ : Yobs R4) (yQ_mem_baseSet x Q hU θ₀ θ₀) :
        CFib ≃L[ℝ] CFib) : CFib →L[ℝ] CFib).comp (hQ Q θ) := by
  rw [triv_apply (yQ x Q hU θ₀ : Yobs R4) (qQ x Q hU θ) (yQ_mem_baseSet x Q hU θ θ₀)]
  refine ContinuousLinearMap.ext fun v => ?_
  exact Tz_yQ x Q hU θ θ₀ (hQ Q θ v)

lemma continuous_qQ (x : R4) (Q : M4) (hU : IsUnit Q) : Continuous (qQ x Q hU) := by
  refine continuous_iff_continuousAt.mpr fun θ₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  have hy : Continuous fun θ => (yQ x Q hU θ : Yobs R4) :=
    continuous_subtype_val.comp (continuous_yQ x Q hU)
  refine ⟨hy.continuousAt, ?_⟩
  have hform : (fun θ => ((trivializationAt HomF (HomCb (X := R4)) (yQ x Q hU θ₀ : Yobs R4))
      (qQ x Q hU θ)).2) = fun θ =>
      ((Tz (yQ x Q hU θ₀ : Yobs R4) (yQ x Q hU θ₀ : Yobs R4) (yQ_mem_baseSet x Q hU θ₀ θ₀) :
        CFib ≃L[ℝ] CFib) : CFib →L[ℝ] CFib).comp (hQ Q θ) :=
    funext fun θ => triv_qQ x Q hU θ θ₀
  have hc : Continuous fun θ =>
      ((Tz (yQ x Q hU θ₀ : Yobs R4) (yQ x Q hU θ₀ : Yobs R4) (yQ_mem_baseSet x Q hU θ₀ θ₀) :
        CFib ≃L[ℝ] CFib) : CFib →L[ℝ] CFib).comp (hQ Q θ) :=
    continuous_const.clm_comp (continuous_hQ hU)
  have : ContinuousAt (fun θ => ((trivializationAt HomF (HomCb (X := R4)) (yQ x Q hU θ₀ : Yobs R4))
      (qQ x Q hU θ)).2) θ₀ := by rw [hform]; exact hc.continuousAt
  exact this

/-- The frame path in the frame bundle. -/
def pQ (x : R4) (Q : M4) (hU : IsUnit Q) (θ : ℝ) : OFr R4 := ⟨qQ x Q hU θ, (qQ_mem x Q hU θ).1⟩

lemma pQ_pi (x : R4) (Q : M4) (hU : IsUnit Q) :
    pQ x Q hU Real.pi = actOFr' (pQ x Q hU 0) gHol := by
  apply Subtype.ext
  have hy : (yQ x Q hU Real.pi : Yobs R4) = (yQ x Q hU 0 : Yobs R4) :=
    congrArg Subtype.val (mkY_eq_of _ _ (GQ_pi Q))
  exact mk_eq_of hy (hQ_pi hU)

/-! ### The theorem -/

/-- A point of an open `W` with `G₀₀ ≤ 0` gives one with `G₀₀ < 0`. -/
lemma exists_neg_point {W : Set (Y13o R4)} (hW : IsOpen W) {y : Y13o R4} (hy : y ∈ W)
    (hle : Gpt (y : Yobs R4) 0 0 ≤ 0) : ∃ y' ∈ W, Gpt (y' : Yobs R4) 0 0 < 0 := by
  set x := ((y : Yobs R4) : Sym2TX R4).proj
  set s : Fin 10 → ℝ := ((y : Yobs R4) : Sym2TX R4).2
  have hV : IsOpen (Subtype.val '' (Subtype.val '' W : Set (Yobs R4)) : Set (Sym2TX R4)) :=
    (Yobs R4).2.isOpenMap_subtype_val _ ((Y13o R4).2.isOpenMap_subtype_val _ hW)
  let g : ℝ → (Fin 10 → ℝ) := fun ε => s - ε • (Pi.single 0 1 : Fin 10 → ℝ)
  have hg : Continuous g := continuous_const.sub (continuous_id.smul continuous_const)
  have hg0 : g 0 = s := by simp [g]
  let f : ℝ → Sym2TX R4 := fun ε => ⟨x, g ε⟩
  have hf : Continuous f := (FiberBundle.continuous_totalSpaceMk (Fin 10 → ℝ)
    (symCore (Zt R4)).Fiber x).comp hg
  have h0 : f 0 ∈ Subtype.val '' (Subtype.val '' W : Set (Yobs R4)) := by
    refine ⟨(y : Yobs R4), ⟨y, hy, rfl⟩, ?_⟩
    show ((y : Yobs R4) : Sym2TX R4) = ⟨x, g 0⟩
    rw [hg0]
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f ε ∈ Subtype.val '' (Subtype.val '' W : Set (Yobs R4)) :=
    nhdsWithin_le_nhds ((hV.preimage hf).mem_nhds h0)
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨_, ⟨y', hy'W, rfl⟩, hy'f⟩ := hε
  refine ⟨y', hy'W, ?_⟩
  have e : Gpt (y' : Yobs R4) 0 0 = Gpt (y : Yobs R4) 0 0 - ε := by
    show symMat ((y' : Yobs R4) : Sym2TX R4).2 0 0 = _
    rw [hy'f]
    show g ε (symIdx 0 0) = s (symIdx 0 0) - ε
    simp [g, symIdx]
  rw [e]
  have : (0 : ℝ) < ε := hεpos
  linarith

lemma conj_metric {Q R : M4} (hQ : IsUnit Q) :
    (Q * R * Q⁻¹) * (Q * ηR * Qᵀ) * (Q * R * Q⁻¹)ᵀ = (Q * R) * ηR * (Q * R)ᵀ := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : Qᵀ * (Q⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [Matrix.transpose_mul (Q * R), Matrix.transpose_mul Q R]
  calc Q * R * Q⁻¹ * (Q * ηR * Qᵀ) * ((Q⁻¹)ᵀ * (Rᵀ * Qᵀ))
      = Q * R * (Q⁻¹ * Q) * ηR * (Qᵀ * (Q⁻¹)ᵀ) * (Rᵀ * Qᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- **An `HGauge`-invariant open set with a spin structure lies in `{G₀₀ > 0}`.** -/
theorem gauge_largest (S : SpinStructure R4) (hinv : HInvariant S.W) : S.W ⊆ timeGaugeLocus := by
  intro y hy
  by_contra hcon
  have hle : Gpt (y : Yobs R4) 0 0 ≤ 0 := not_lt.mp hcon
  obtain ⟨y', hy'W, hneg⟩ := exists_neg_point S.isOpen_W hy hle
  obtain ⟨Q0, hQ0, hG0⟩ := exists_Q y'
  set x := ((y' : Yobs R4) : Sym2TX R4).proj
  -- the first row of `Q0` is spacelike
  let r : Fin 4 → ℝ := fun k => Q0 0 k
  have hr : etaF r r < 0 := by
    have e := dot_G_eq hG0 ![1, 0, 0, 0] ![1, 0, 0, 0]
    have e1 : Q0ᵀ *ᵥ (![1, 0, 0, 0] : Fin 4 → ℝ) = r := by
      funext k; simp [r, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    rw [e1] at e
    rw [← e]
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_four] using hneg
  obtain ⟨A, ρ, hA, hAr⟩ := exists_reflection hr
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have he : (ηR : M4).det = -1 := by
      rw [GU.Iso77.ηR_eq]; simp [ηr, Matrix.det_diagonal, Fin.prod_univ_four]
    have := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_mul, h0, he] at this
    simp at this
  -- the adapted factorisation
  set Q := Q0 * Aᵀ
  have hQu : IsUnit Q := hQ0.mul ((Matrix.isUnit_transpose _).mpr hAu)
  have hGQ : Q * ηR * Qᵀ = Q0 * ηR * Q0ᵀ := by
    show Q0 * Aᵀ * ηR * (Q0 * Aᵀ)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Q0 * Aᵀ * ηR * (A * Q0ᵀ) = Q0 * (Aᵀ * ηR * A) * Q0ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA]
  have hrow : ∀ j, Q 0 j = (![0, 0, ρ, 0] : Fin 4 → ℝ) j := by
    intro j
    rw [← hAr]
    show (Q0 * Aᵀ) 0 j = _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, r]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  -- the loop stays in the orbit
  have hQinvR : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hQu)
  have hQRinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQu)
  have hPg : ∀ θ, HGauge (Q * Rθ θ * Q⁻¹) := by
    intro θ
    refine ⟨((isUnit_QR hQu θ).mul (Matrix.isUnit_nonsing_inv_iff.mpr hQu)), 1, one_ne_zero, ?_⟩
    have hrowR : ∀ j, (Q * Rθ θ) 0 j = Q 0 j := by
      intro j
      rw [Matrix.mul_apply, Fin.sum_univ_four, hrow 0, hrow 1, hrow 2, hrow 3]
      fin_cases j <;> simp [Rθ, hrow]
    intro j
    have : (Q * Rθ θ * Q⁻¹) 0 j = (Q * Q⁻¹) 0 j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hrowR]
    rw [this, hQRinv, Matrix.one_apply]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg (Ne.symm hj), if_neg hj]
  have hyQ : ∀ θ, yQ x Q hQu θ ∈ S.W := by
    intro θ
    have h1 := hinv y' hy'W _ (hPg θ)
    convert h1 using 1
    have hM : Gpt (gaugeAct _ (hPg θ).1 y' : Yobs R4) = (Q * Rθ θ) * ηR * (Q * Rθ θ)ᵀ := by
      rw [Gpt_gaugeAct, hG0, ← hGQ]
      exact conj_metric hQu
    exact (eq_mkY _ (isUnit_QR hQu θ) hM).symm
  -- the holonomy contradiction
  exact no_spinLiftData_of_path S.toData (p := pQ x Q hQu)
    ((continuous_qQ x Q hQu).subtype_mk _) (fun θ => hyQ θ) (pQ_pi x Q hQu)

/-- **An `HGauge`-invariant open set with a global frame lies in `{G₀₀ > 0}`.** -/
theorem gauge_largest_frame (W : Set (Y13o R4)) (hW : IsOpen W) (hinv : HInvariant W)
    (σ : Y13o R4 → OFr R4) (hσ : ContinuousOn σ W) (hp : ∀ y ∈ W, projOFr (σ y) = y) :
    W ⊆ timeGaugeLocus :=
  gauge_largest (SpinLiftData.ofSection W hW σ hσ hp).toStructure hinv

/-- The gauge locus of the base chart is `{G₀₀ > 0}`. -/
lemma gaugeW_R4 (a : HomTotM R4) : gaugeW a = timeGaugeLocus := by
  refine Set.ext fun y => ?_
  obtain ⟨P, hP, hG⟩ := exists_Q y
  show (((y : Yobs R4) ∈ chartDom a) ∧ gaugeMetric a y ∈ gaugeSet) ↔ _
  rw [gaugeMetric_R4, mem_gaugeSet_iff hP hG]
  exact ⟨fun h => h.2, fun h => ⟨chartDom_R4 a y, h⟩⟩

/-- **`{G₀₀ > 0}` carries a global frame.** -/
theorem exists_frame_timeGaugeLocus :
    ∃ σ : Y13o R4 → OFr R4, ContinuousOn σ timeGaugeLocus ∧
      ∀ y ∈ timeGaugeLocus, projOFr (σ y) = y := by
  have h := gaugeW_R4 (pLoop (0 : R4) 0 : HomTotM R4)
  refine ⟨σG (pLoop (0 : R4) 0 : HomTotM R4), ?_, fun y hy => ?_⟩
  · rw [← h]; exact continuousOn_σG _
  · rw [← h] at hy; exact proj_σG _ hy

/-- **`{G₀₀ > 0}` is the largest `HGauge`-invariant open subset of `Y13(ℝ⁴)` with a global frame, and
with a spin structure.** -/
theorem gauge_largest_iff :
    HInvariant timeGaugeLocus ∧ IsOpen timeGaugeLocus ∧
      (∃ σ : Y13o R4 → OFr R4, ContinuousOn σ timeGaugeLocus ∧
        ∀ y ∈ timeGaugeLocus, projOFr (σ y) = y) ∧
      (∃ S : SpinStructure R4, S.W = timeGaugeLocus) ∧
      (∀ S : SpinStructure R4, HInvariant S.W → S.W ⊆ timeGaugeLocus) ∧
      (∀ (W : Set (Y13o R4)) (σ : Y13o R4 → OFr R4), IsOpen W → HInvariant W → ContinuousOn σ W →
        (∀ y ∈ W, projOFr (σ y) = y) → W ⊆ timeGaugeLocus) := by
  obtain ⟨D, hD⟩ := exists_spinLiftData_R4
  refine ⟨hInvariant_timeGaugeLocus, ?_, exists_frame_timeGaugeLocus, ⟨D.toStructure, hD⟩,
    gauge_largest, fun W σ hW hi hσ hp => gauge_largest_frame W hW hi σ hσ hp⟩
  have : IsOpen D.W := D.isOpen_W
  rw [hD] at this
  exact this

end

end GU.Library
