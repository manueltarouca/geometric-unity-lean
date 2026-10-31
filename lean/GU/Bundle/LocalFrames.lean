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

end GU.Library
