import GU.Bundle.FrameActionSmooth

/-!
# Local orthonormal frames (towards local triviality)

**`contDiffOn_Gchim_omega`**: the chimeric Gram matrix is *analytic* (`C^ω`) on the nondegenerate
locus: it is rational in the metric (entrywise toolkit `EntCDn`, any smoothness order).
**`exists_local_frames`**: an analytic symmetric family `H(b)` with `H(b₀) = η` has analytic local
frames `N(b)` (`N(b)ᵀ H(b) N(b) = η`), by the implicit function theorem on
`S ↦ sym((1+ηS)ᵀ H (1+ηS))` (S-derivative `2·id`). Analyticity is a workaround: Mathlib's implicit
function is regular only at the base point, and `C^ω` at a point spreads to a neighbourhood
(`ContDiffAt.contDiffOn`); `Gchim` is rational, so this suffices here. With `H = q₀ᵀ G q₀` this gives
smooth local orthonormal frames `q₀ N(b)` (`bil_mulM`).

**`exists_local_section`**: smooth local sections of the orthonormal frame bundle `OFr` in the base
chart coordinates of a frame `q₀` (`σ e ∈ OFr`, base coordinate `e`, i.e. `proj (σ e) = chartY⁻¹ e`).
Composing with the base chart gives a section over `Yobs` (a short corollary, not yet stated);
smoothness is into the ambient `HomTotM`.
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Chimeric
open scoped ContDiff

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Entrywise `C^n` matrix families. -/
def EntCDn (n : ℕ∞ω) {ι : Type*} (S : Set B) (M : B → Matrix ι ι ℝ) : Prop :=
  ∀ i j, ContDiffOn ℝ n (fun b => M b i j) S

variable {n : ℕ∞ω} {S : Set B} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma EntCDn.const (A : Matrix ι ι ℝ) : EntCDn n S (fun _ => A) := fun _ _ => contDiffOn_const

lemma EntCDn.mul {M N : B → Matrix ι ι ℝ} (hM : EntCDn n S M) (hN : EntCDn n S N) :
    EntCDn n S (fun b => M b * N b) := fun i j => by
  simp only [mul_apply]
  exact ContDiffOn.sum fun k _ => (hM i k).mul (hN k j)

lemma EntCDn.det {M : B → Matrix ι ι ℝ} (hM : EntCDn n S M) :
    ContDiffOn ℝ n (fun b => (M b).det) S := by
  simp only [det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hM _ _)

lemma EntCDn.updateRow {M : B → Matrix ι ι ℝ} (hM : EntCDn n S M) (j : ι) (v : ι → ℝ) :
    EntCDn n S (fun b => (M b).updateRow j v) := fun a c => by
  by_cases h : a = j
  · subst h; simp only [updateRow_self]; exact contDiffOn_const
  · simp only [updateRow_ne h]; exact hM a c

lemma EntCDn.inv {M : B → Matrix ι ι ℝ} (hM : EntCDn n S M) (hdet : ∀ b ∈ S, (M b).det ≠ 0) :
    EntCDn n S (fun b => (M b)⁻¹) := fun i j => by
  simp only [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', adjugate_apply]
  exact (hM.det.inv hdet).mul (hM.updateRow j (Pi.single i 1)).det

lemma EntCDn.trace {M : B → Matrix ι ι ℝ} (hM : EntCDn n S M) :
    ContDiffOn ℝ n (fun b => (M b).trace) S := by
  simp only [Matrix.trace, diag]
  exact ContDiffOn.sum fun i _ => hM i i

lemma EntCDn.dot_mulVec {M : B → Matrix ι ι ℝ} (hM : EntCDn n S M) (p q : ι → ℝ) :
    ContDiffOn ℝ n (fun b => p ⬝ᵥ (M b *ᵥ q)) S := by
  simp only [dotProduct, mulVec]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul
    (ContDiffOn.sum fun k _ => (hM i k).mul contDiffOn_const)

/-- **`Gchim` is analytic on the nondegenerate locus.** -/
theorem contDiffOn_Gchim_omega : ContDiffOn ℝ ω Gchim nondeg := by
  have hG : EntCDn ω nondeg (fun s : Fin 10 → ℝ => symMat s) := fun i j =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) (symIdx i j)).contDiff).contDiffOn
  have hI : EntCDn ω nondeg (fun s : Fin 10 → ℝ => (symMat s)⁻¹) := hG.inv fun _ h => h
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  show ContDiffOn ℝ ω (fun s => Bmod (symMat s) (uΦ i) (uΦ j)) nondeg
  simp only [Bmod, chimY]
  exact ((EntCDn.trace (((hI.mul (EntCDn.const _)).mul hI).mul (EntCDn.const _))).sub
    ((EntCDn.trace (hI.mul (EntCDn.const _))).mul (EntCDn.trace (hI.mul (EntCDn.const _))))).add
    (hG.dot_mulVec _ _)

/-! ### Local frames by the implicit function theorem -/

/-- `(G, M) ↦ Mᵀ G M`, a polynomial map. -/
noncomputable def bilFull (z : Mat 14 × Mat 14) : Mat 14 := bil z.1 z.2 z.2

lemma contDiff_bilFull {n : ℕ∞ω} : ContDiff ℝ n bilFull := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [bilFull, bil_apply]
  have hc : ∀ (a b : Fin 14), ContDiff ℝ n (fun z : Mat 14 × Mat 14 => z.1 a b) := fun a b =>
    (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) a b).comp contDiff_fst
  have hd : ∀ (a b : Fin 14), ContDiff ℝ n (fun z : Mat 14 × Mat 14 => z.2 a b) := fun a b =>
    (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) a b).comp contDiff_snd
  exact ContDiff.sum fun k _ => ContDiff.sum fun l _ => ((hd k i).mul (hc k l)).mul (hd l j)

variable [FiniteDimensional ℝ B]

/-- `S ↦ 1 + η S`. -/
noncomputable def Nf (η : Mat 14) (S : symS 14) : Mat 14 :=
  Matrix.of.symm (1 + Matrix.of η * Matrix.of (S : Mat 14))

lemma contDiff_Nf {n : ℕ∞ω} (η : Mat 14) : ContDiff ℝ n (Nf η) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Nf, Matrix.of_symm_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  refine contDiff_const.add (ContDiff.sum fun k _ => contDiff_const.mul ?_)
  exact (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) k j).comp (symS 14).subtypeL.contDiff

/-- The linear part `S ↦ η S` of `Nf`. -/
noncomputable def Lη (η : Mat 14) : symS 14 →L[ℝ] Mat 14 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S => Matrix.of.symm (Matrix.of η * Matrix.of (S : Mat 14))
      map_add' := fun S T => by
        apply Matrix.of.injective
        simp only [Equiv.apply_symm_apply, Submodule.coe_add]
        show Matrix.of η * (Matrix.of (S : Mat 14) + Matrix.of (T : Mat 14)) = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun r S => by
        apply Matrix.of.injective
        simp only [Equiv.apply_symm_apply, Submodule.coe_smul, RingHom.id_apply]
        show Matrix.of η * (r • Matrix.of (S : Mat 14)) = _
        rw [Matrix.mul_smul]; rfl }

lemma Nf_eq (η : Mat 14) (S : symS 14) : Nf η S = Matrix.of.symm 1 + Lη η S := by
  apply Matrix.of.injective; rfl

lemma hasFDerivAt_Nf (η : Mat 14) (S : symS 14) : HasFDerivAt (Nf η) (Lη η) S := by
  have : Nf η = fun S => Matrix.of.symm 1 + Lη η S := funext (Nf_eq η)
  rw [this]
  exact (Lη η).hasFDerivAt.const_add _

/-- **The S-derivative at the base point is `2 · id`.** -/
lemma deriv_orthF_Nf (η : Mat 14) (hη : η ∈ symS 14) (hηη : Matrix.of η * Matrix.of η = 1)
    (S : symS 14) :
    fderiv ℝ (orthF η) (Nf η 0) (Lη η S) = (2 : ℝ) • S := by
  rw [fderiv_orthF]
  have he : (Matrix.of η)ᵀ = Matrix.of η := mat_symm_of_mem hη
  have hs : (Matrix.of (S : Mat 14))ᵀ = Matrix.of (S : Mat 14) := mat_symm_of_mem S.2
  have hN : Matrix.of (Nf η 0) = 1 := by
    rw [Nf_eq]; simp [Lη]
  have hL : Matrix.of (Lη η S) = Matrix.of η * Matrix.of (S : Mat 14) := rfl
  have h1 : Matrix.of (bil η (Nf η 0) (Lη η S)) = Matrix.of (S : Mat 14) := by
    rw [bil_eq_mat, hN, hL, Matrix.transpose_one, Matrix.one_mul, ← Matrix.mul_assoc, hηη,
      Matrix.one_mul]
  have h2 : Matrix.of (bil η (Lη η S) (Nf η 0)) = Matrix.of (S : Mat 14) := by
    rw [bil_eq_mat, hN, hL, Matrix.mul_one, Matrix.transpose_mul, hs, he, Matrix.mul_assoc, hηη,
      Matrix.mul_one]
  have hsum : bil η (Nf η 0) (Lη η S) + bil η (Lη η S) (Nf η 0) = (((2 : ℝ) • S : symS 14) : Mat 14) := by
    apply Matrix.of.injective
    rw [← Matrix.of_add_of, h1, h2, Submodule.coe_smul, two_smul, Matrix.of_add_of]
  apply Subtype.ext
  show (symP 14 (bil η (Nf η 0) (Lη η S) + bil η (Lη η S) (Nf η 0)) : Mat 14) = _
  rw [hsum, symP_of_mem ((2 : ℝ) • S).2]

lemma orthF_Nf_zero (η : Mat 14) (hη : η ∈ symS 14) : orthF η (Nf η 0) = ⟨η, hη⟩ := by
  apply Subtype.ext
  show (symP 14 (bil η (Nf η 0) (Nf η 0)) : Mat 14) = η
  have hN : Matrix.of (Nf η 0) = 1 := by rw [Nf_eq]; simp [Lη]
  have hb : bil η (Nf η 0) (Nf η 0) = η := by
    apply Matrix.of.injective
    rw [bil_eq_mat, hN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [hb, symP_of_mem hη]

/-- **Local orthonormal frames** for an analytic symmetric metric family with `H(b₀) = η`:
there are analytic `N(b)` near `b₀` with `N(b)ᵀ H(b) N(b) = η`. -/
theorem exists_local_frames (H : B → Mat 14) (b0 : B) (hH : ContDiffAt ℝ ω H b0)
    (hsym : ∀ b, H b ∈ symS 14) (η : Mat 14) (hη : η ∈ symS 14)
    (hηη : Matrix.of η * Matrix.of η = 1) (h0 : H b0 = η) :
    ∃ U ∈ nhds b0, ∃ N : B → Mat 14, ContDiffOn ℝ ω N U ∧ ∀ b ∈ U, bil (H b) (N b) (N b) = η := by
  set f : B × symS 14 → symS 14 := fun p => orthF (H p.1) (Nf η p.2) with hfdef
  have cdf : ContDiffAt ℝ ω f (b0, 0) := by
    have hpair : ContDiffAt ℝ ω (fun p : B × symS 14 => (H p.1, Nf η p.2)) (b0, 0) :=
      (hH.comp _ contDiffAt_fst).prodMk ((contDiff_Nf η).contDiffAt.comp _ contDiffAt_snd)
    have hfeq : f = ⇑(symP 14) ∘ bilFull ∘ (fun p : B × symS 14 => (H p.1, Nf η p.2)) := rfl
    rw [hfeq]
    exact (symP 14).contDiff.contDiffAt.comp _ (contDiff_bilFull.contDiffAt.comp _ hpair)
  -- the partial derivative in `S`
  have hf : HasFDerivAt f (fderiv ℝ f (b0, 0)) (b0, 0) :=
    (cdf.differentiableAt (by simp)).hasFDerivAt
  have hinc : HasFDerivAt (fun S : symS 14 => (b0, S)) (ContinuousLinearMap.inr ℝ B (symS 14)) 0 :=
    (hasFDerivAt_const b0 0).prodMk (hasFDerivAt_id 0)
  have h1 := hf.comp (0 : symS 14) hinc
  have hO : HasFDerivAt (orthF η) (fderiv ℝ (orthF η) (Nf η 0)) (Nf η 0) :=
    ((orthF_contDiff η).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 := hO.comp (0 : symS 14) (hasFDerivAt_Nf η 0)
  have hfun : (f ∘ fun S : symS 14 => (b0, S)) = orthF η ∘ Nf η := by
    funext S; simp only [Function.comp_apply, hfdef, h0]
  rw [hfun] at h1
  have hD : fderiv ℝ f (b0, 0) ∘L ContinuousLinearMap.inr ℝ B (symS 14) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (symS 14) := by
    rw [h1.unique h2]
    refine ContinuousLinearMap.ext fun S => ?_
    rw [ContinuousLinearMap.comp_apply, deriv_orthF_Nf η hη hηη S]; rfl
  have if₂ : (fderiv ℝ f (b0, 0) ∘L ContinuousLinearMap.inr ℝ B (symS 14)).IsInvertible := by
    rw [hD]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ (symS 14) 2 two_ne_zero).toContinuousLinearEquiv, ?_⟩
    ext S; rfl
  have pn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hψ := cdf.contDiffAt_implicitFunction pn if₂
  obtain ⟨U1, hU1, hon⟩ := hψ.contDiffOn (m := ω) le_rfl (by simp)
  have hev := cdf.eventually_apply_implicitFunction pn if₂
  refine ⟨U1 ∩ {b | f (b, cdf.implicitFunction pn if₂ b) = f (b0, 0)},
    Filter.inter_mem hU1 hev, Nf η ∘ cdf.implicitFunction pn if₂,
    (contDiff_Nf η).comp_contDiffOn (hon.mono Set.inter_subset_left), ?_⟩
  rintro b ⟨-, hb⟩
  have hb' : orthF (H b) (Nf η (cdf.implicitFunction pn if₂ b)) = ⟨η, hη⟩ := by
    have := hb
    simp only [Set.mem_setOf_eq, hfdef, h0] at this
    rw [this, orthF_Nf_zero η hη]
  exact bil_of_orthF_eq (hsym b) hη hb'

/-! ### Local sections of the orthonormal frame bundle (chart coordinates) -/

section Section

open Bundle
open scoped Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- Chart-target membership of `HomTotM` only depends on the base coordinate. -/
lemma mem_chart_target_iff (a : HomTotM X) (e : (Fin 4 → ℝ) × (Fin 10 → ℝ)) (h h' : HomF) :
    ((e, h) : HomModel) ∈ (chartAt HomModel a).target ↔ ((e, h') : HomModel) ∈ (chartAt HomModel a).target := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a]
  simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.prod_target,
    OpenPartialHomeomorph.refl_target, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_preimage, OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id,
    Trivialization.target_eq, Set.mem_prod, Set.mem_univ, and_true]
  exact Iff.rfl

/-- Pairing into the total-space model. -/
def pairHM (e : (Fin 4 → ℝ) × (Fin 10 → ℝ)) (h : HomF) : HomModel := (e, h)

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **Smooth local sections of the orthonormal frame bundle** (in the base coordinate of the chart
at a frame `q₀`): near `e₀ = (chart q₀).1` there is a smooth `σ` with values in `OFr` whose base
coordinate is `e`. -/
theorem exists_local_section (q0 : HomTotM X) (hq0 : q0 ∈ OFr X) :
    ∃ U ∈ nhds (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 q0).1),
      ∃ σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X,
        ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U ∧
        ∀ e ∈ U, σ e ∈ OFr X ∧ (chartAt HomModel q0 (σ e)).1 = e ∧
          σ e ∈ (chartAt HomModel q0).source := by
  set c := chartAt HomModel q0
  set p0 := c q0
  set e0 : (Fin 4 → ℝ) × (Fin 10 → ℝ) := (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p0.1)
  set M0 := homMat.symm (p0.2 : HomF)
  have hp0 : p0 ∈ c.target := c.map_source (mem_chart_source _ q0)
  have hq0' : c.symm p0 = q0 := c.left_inv (mem_chart_source _ q0)
  -- the frame condition at the base point
  have hF0 : bil (Gchim e0.2) M0 M0 = η77 := by
    have h1 : Fframe (c.symm p0) = ⟨η77, ηSig_mem 7 7⟩ := by rw [hq0']; exact hq0
    rw [Fframe_chart q0 hp0] at h1
    exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h1
  have hnd : e0.2 ∈ nondeg := chart_target_nondeg q0 hp0
  set H : (Fin 4 → ℝ) × (Fin 10 → ℝ) → Mat 14 := fun e => bil (Gchim e.2) M0 M0
  have hH : ContDiffAt ℝ ω H e0 := by
    have hG : ContDiffAt ℝ ω (fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) => Gchim e.2) e0 :=
      (contDiffOn_Gchim_omega.contDiffAt (isOpen_nondeg.mem_nhds hnd)).comp _ contDiffAt_snd
    have : H = bilFull ∘ fun e => (Gchim e.2, M0) := rfl
    rw [this]
    exact contDiff_bilFull.contDiffAt.comp _ (hG.prodMk contDiffAt_const)
  obtain ⟨U1, hU1, N, hN, hNe⟩ := exists_local_frames H e0 hH (fun e => bil_mem _ (Gchim_mem _) _)
    η77 (ηSig_mem 7 7) (ηSig_sq 7 7) hF0
  set ν : (Fin 4 → ℝ) × (Fin 10 → ℝ) → HomF := fun e => homMat (mulM M0 (N e))
  set T : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ)) := {e | pairHM e (p0.2 : HomF) ∈ c.target}
  have hT : T ∈ nhds e0 := by
    have hc : Continuous fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) => pairHM e (p0.2 : HomF) :=
      continuous_id.prodMk continuous_const
    exact (c.open_target.preimage hc).mem_nhds hp0
  have hTν : ∀ e ∈ T, pairHM e (ν e) ∈ c.target := fun e he =>
    (mem_chart_target_iff q0 e _ _).mp he
  refine ⟨U1 ∩ T, Filter.inter_mem hU1 hT, fun e => c.symm (pairHM e (ν e)), ?_, ?_⟩
  · have hpair : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞
        (fun e => pairHM e (ν e)) (U1 ∩ T) := by
      have h : ContDiffOn ℝ ∞ (fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) =>
          ((e, ν e) : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF)) (U1 ∩ T) := by
        refine contDiffOn_id.prodMk ?_
        have hm : ContDiffOn ℝ ∞ (fun e => mulM M0 (N e)) (U1 ∩ T) := by
          have hN' : ContDiffOn ℝ ∞ N (U1 ∩ T) :=
            ((hN.of_le (by exact le_top)) : ContDiffOn ℝ ∞ N U1).mono Set.inter_subset_left
          have : (fun e => mulM M0 (N e)) = fun e => mulCL 14 M0 (N e) := by
            funext e; exact mulM_eq _ _
          rw [this]
          exact ((mulCL 14 M0).contDiff.comp_contDiffOn hN')
        have hL : ContDiff ℝ ∞ (fun M : Mat 14 => homMat M) := by
          have : (fun M : Mat 14 => homMat M) = fun M => (ΦL : R14 →L[ℝ] CFib).comp (matL M) :=
            funext fun M => ContinuousLinearMap.ext fun x => rfl
          rw [this]
          exact contDiff_const.clm_comp matL.contDiff
        exact hL.comp_contDiffOn hm
      exact (show ContDiffOn ℝ ∞ (fun e => pairHM e (ν e)) (U1 ∩ T) from h).contMDiffOn
    exact (contMDiffOn_chart_symm (x := q0)).comp hpair fun e he => hTν e he.2
  · rintro e ⟨he1, he2⟩
    have hmem := hTν e he2
    refine ⟨?_, ?_, c.map_target hmem⟩
    · show Fframe (c.symm (pairHM e (ν e))) = ⟨η77, ηSig_mem 7 7⟩
      rw [Fframe_chart q0 hmem]
      apply Subtype.ext
      show (symP 14 (bil (Gchim e.2) (homMat.symm (ν e)) (homMat.symm (ν e))) : Mat 14) = η77
      have hb : bil (Gchim e.2) (homMat.symm (ν e)) (homMat.symm (ν e)) = η77 := by
        rw [show homMat.symm (ν e) = mulM M0 (N e) from homMat.symm_apply_apply _]
        apply Matrix.of.injective
        rw [bil_mulM]
        have := congrArg Matrix.of (hNe e he1)
        rw [bil_eq_mat] at this
        exact this
      rw [hb, symP_of_mem (ηSig_mem 7 7)]
    · rw [c.right_inv hmem]; rfl

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- The base coordinate of the total-space chart is the base chart of the projection. -/
lemma chart_fst (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    (chartAt HomModel a q).1 = chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj q.proj := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hq ⊢
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff] at hq
  show chartAt _ a.proj ((trivializationAt HomF (HomCb (X := X)) a.proj) q).1 = _
  rw [Trivialization.coe_fst _ hq.1]

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
lemma proj_mem_chart_source (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    q.proj ∈ (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).source := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hq
  simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    OpenPartialHomeomorph.prod_source, Set.mem_prod, OpenPartialHomeomorph.refl_source,
    Set.mem_univ, and_true] at hq
  have := hq.2
  rwa [Trivialization.coe_coe, Trivialization.coe_fst _ hq.1] at this

set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **Local sections of the orthonormal frame bundle over `Y`**: around the base point of any
orthonormal frame there is `s = σ ∘ chartY` on a neighbourhood `V`, with `σ` smooth on the chart
image (`exists_local_section`), `s y ∈ OFr` and `proj (s y) = y`. (Stating `ContMDiffOn` of `s`
directly needs the `ModelProd`/product-model instance conversion; it is `σ` composed with the
smooth chart.) -/
theorem exists_local_section_Y (q0 : HomTotM X) (hq0 : q0 ∈ OFr X) :
    ∃ V ∈ nhds q0.proj, ∃ U : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ)),
      ∃ σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X,
        ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U ∧
        ∀ y ∈ V, chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj y ∈ U ∧
          σ (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj y) ∈ OFr X ∧
          (σ (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj y)).proj = y := by
  obtain ⟨U, hU, σ, hσ, hσp⟩ := exists_local_section q0 hq0
  set cY := chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) q0.proj
  have he0 : (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 q0).1) = cY q0.proj :=
    chart_fst q0 q0 (mem_chart_source _ q0)
  rw [he0] at hU
  refine ⟨cY.source ∩ cY ⁻¹' U, Filter.inter_mem (cY.open_source.mem_nhds (mem_chart_source _ _))
      ((cY.continuousAt (mem_chart_source _ _)).preimage_mem_nhds hU), U, σ, hσ, ?_⟩
  rintro y ⟨hys, hyU⟩
  obtain ⟨hO, hfst, hsrc⟩ := hσp (cY y) hyU
  refine ⟨hyU, hO, ?_⟩
  have h1 := chart_fst q0 _ hsrc
  rw [hfst] at h1
  exact cY.injOn (proj_mem_chart_source q0 _ hsrc) hys h1.symm

end Section

end GU.Library
