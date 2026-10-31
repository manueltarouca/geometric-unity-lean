import GU.Bundle.OrthoLie
import GU.Library.FrameFamily

/-!
# The chimeric Gram matrix is smooth on the Lorentzian (nondegenerate) locus (L4e step 3)

`Gchim s i j = Bmod (symMat s) (Φ eᵢ) (Φ eⱼ)` is the chimeric metric at the point `s ∈ ℝ¹⁰` of the
fibre of `Y`, in the frame `Φ eᵢ` of `CFib`. It is symmetric (`Gchim_mem`) and `C^∞` on
`{s | det (symMat s) ≠ 0}` (`contDiffOn_Gchim`), which contains the Lorentzian fibre (the points
of `Y`). Matrix
entries are handled entrywise (`EntCD`): determinants and adjugates are polynomial, and
`G⁻¹ = det⁻¹ · adj G`. So `Gchim` satisfies the hypotheses of `isManifold_frames` over a chart;
the chart domain is the Lorentzian fibre, not all nondegenerate points (those include (2,2)
points, which also admit (7,7)-orthonormal frames but are not in `Y`).
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Chimeric
open scoped ContDiff Manifold

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Entrywise smoothness of a matrix family on `S`. -/
def EntCD {n : Type*} (S : Set B) (M : B → Matrix n n ℝ) : Prop :=
  ∀ i j, ContDiffOn ℝ ∞ (fun b => M b i j) S

variable {S : Set B} {n : Type*} [Fintype n] [DecidableEq n]

lemma EntCD.const (A : Matrix n n ℝ) : EntCD S (fun _ => A) := fun _ _ => contDiffOn_const

lemma EntCD.mul {M N : B → Matrix n n ℝ} (hM : EntCD S M) (hN : EntCD S N) :
    EntCD S (fun b => M b * N b) := fun i j => by
  simp only [mul_apply]
  exact ContDiffOn.sum fun k _ => (hM i k).mul (hN k j)

lemma EntCD.det {M : B → Matrix n n ℝ} (hM : EntCD S M) :
    ContDiffOn ℝ ∞ (fun b => (M b).det) S := by
  simp only [det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hM _ _

lemma EntCD.updateRow {M : B → Matrix n n ℝ} (hM : EntCD S M) (j : n) (v : n → ℝ) :
    EntCD S (fun b => (M b).updateRow j v) := fun a c => by
  by_cases h : a = j
  · subst h; simp only [updateRow_self]; exact contDiffOn_const
  · simp only [updateRow_ne h]; exact hM a c

lemma EntCD.inv {M : B → Matrix n n ℝ} (hM : EntCD S M) (hdet : ∀ b ∈ S, (M b).det ≠ 0) :
    EntCD S (fun b => (M b)⁻¹) := fun i j => by
  simp only [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', adjugate_apply]
  exact (hM.det.inv hdet).mul (hM.updateRow j (Pi.single i 1)).det

lemma EntCD.trace {M : B → Matrix n n ℝ} (hM : EntCD S M) :
    ContDiffOn ℝ ∞ (fun b => (M b).trace) S := by
  simp only [Matrix.trace, diag]
  exact ContDiffOn.sum fun i _ => hM i i

lemma EntCD.dot_mulVec {M : B → Matrix n n ℝ} (hM : EntCD S M) (p q : n → ℝ) :
    ContDiffOn ℝ ∞ (fun b => p ⬝ᵥ (M b *ᵥ q)) S := by
  simp only [dotProduct, mulVec]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul
    (ContDiffOn.sum fun k _ => (hM i k).mul contDiffOn_const)

/-! ### The chimeric Gram matrix -/

/-- The frame `Φ eᵢ` of `CFib`. -/
noncomputable def uΦ (i : Fin 14) : CFib := ΦL (Pi.single i 1)

/-- **The chimeric Gram matrix** at the fibre point `s` of `Y`. -/
noncomputable def Gchim (s : Fin 10 → ℝ) : Mat 14 := fun i j => Bmod (symMat s) (uΦ i) (uΦ j)

lemma symMat_entry_contDiff (i j : Fin 4) :
    ContDiff ℝ ∞ (fun s : Fin 10 → ℝ => symMat s i j) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) (symIdx i j)).contDiff

/-- The nondegenerate locus. -/
def nondeg : Set (Fin 10 → ℝ) := {s | (symMat s).det ≠ 0}

lemma isOpen_nondeg : IsOpen nondeg := by
  have : ContDiffOn ℝ ∞ (fun s : Fin 10 → ℝ => (symMat s).det) Set.univ :=
    EntCD.det (S := Set.univ) fun i j => (symMat_entry_contDiff i j).contDiffOn
  have h := this.continuousOn.isOpen_inter_preimage isOpen_univ (isOpen_compl_singleton (x := (0 : ℝ)))
  rw [Set.univ_inter] at h
  exact h

/-- **`Gchim` is smooth on the nondegenerate locus.** -/
theorem contDiffOn_Gchim : ContDiffOn ℝ ∞ Gchim nondeg := by
  have hG : EntCD nondeg (fun s : Fin 10 → ℝ => symMat s) := fun i j =>
    (symMat_entry_contDiff i j).contDiffOn
  have hI : EntCD nondeg (fun s : Fin 10 → ℝ => (symMat s)⁻¹) := hG.inv fun _ h => h
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  show ContDiffOn ℝ ∞ (fun s => Bmod (symMat s) (uΦ i) (uΦ j)) nondeg
  simp only [Bmod, chimY]
  refine ((EntCD.trace (((hI.mul (EntCD.const _)).mul hI).mul (EntCD.const _))).sub
    ((EntCD.trace (hI.mul (EntCD.const _))).mul (EntCD.trace (hI.mul (EntCD.const _))))).add
    (hG.dot_mulVec _ _)

lemma symMat_transpose (s : Fin 10 → ℝ) : (symMat s)ᵀ = symMat s := by
  ext i j; simp [symMat, symIdx_symm]

lemma Bmod_comm_of_symm (s : Fin 10 → ℝ) (u v : CFib) :
    Bmod (symMat s) u v = Bmod (symMat s) v u := by
  simp only [Bmod, chimY]
  set Gi := (symMat s)⁻¹
  have h1 : ∀ A Bm : Matrix (Fin 4) (Fin 4) ℝ, trace (Gi * A * Gi * Bm) = trace (Gi * Bm * Gi * A) :=
    fun A Bm => by rw [Matrix.mul_assoc (Gi * A), trace_mul_comm, ← Matrix.mul_assoc]
  have h3 : ∀ a b : Fin 4 → ℝ, a ⬝ᵥ (symMat s *ᵥ b) = b ⬝ᵥ (symMat s *ᵥ a) := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, symMat_transpose, dotProduct_comm]
  rw [h1, h3]; ring

/-- `Gchim s` is symmetric. -/
lemma Gchim_mem (s : Fin 10 → ℝ) : Gchim s ∈ symS 14 := fun _ _ => Bmod_comm_of_symm s _ _

/-! ### Chimeric orthonormal frames over a chart of `Y` -/

/-- The chart-level metric family on `ℝ⁴ × ℝ¹⁰`: `G(x, s) = Gchim s`. -/
noncomputable def Gchart (p : (Fin 4 → ℝ) × (Fin 10 → ℝ)) : Mat 14 := Gchim p.2

/-- The chart-level domain: points of `Y` (Lorentzian fibre, `det < 0`). -/
def chartU : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ)) := Prod.snd ⁻¹' LorFiber

lemma LorFiber_sub_nondeg : LorFiber ⊆ nondeg := fun _ h => ne_of_lt h

lemma isOpen_chartU : IsOpen chartU := isOpen_LorFiber.preimage continuous_snd

lemma contDiffOn_Gchart : ContDiffOn ℝ ∞ Gchart chartU :=
  (contDiffOn_Gchim.mono LorFiber_sub_nondeg).comp contDiff_snd.contDiffOn fun _ h => h

lemma η77_ne_zero : (⟨η77, ηSig_mem 7 7⟩ : symS 14) ≠ 0 := by
  intro h
  have h1 := congrArg (fun S : symS 14 => (S : Mat 14) 0 0) h
  simp [η77, ηSig] at h1

/-- **Chimeric orthonormal frames over a chart of `Y` form a smooth manifold** of dimension
`14 + 91 = 105` (`fibreDim_chimFrames`): the pairs `((x, s), q)` with `s` in the Lorentzian fibre
and the matrix condition `qᵀ Gchim(s) q = η₇₇` (`mem_frames_iff`). By `bil_Gchim_iff` this says
exactly that `x ↦ Φ(q x)` is an isometry `(ℝ¹⁴, Q77) → (C_s, Bmod)`: a `(7,7)`-orthonormal frame of
`C` at `(x, s)`. Chartwise only; gluing across charts of `Y` is open. -/
theorem isManifold_chimFrames :
    letI := smoothLevelChartedOn (frames_submersive (G := Gchart) (U := chartU)
      isOpen_chartU contDiffOn_Gchart (fun p _ => Gchim_mem p.2) (ηSig_mem 7 7) (ηSig_sq 7 7)
      η77_ne_zero)
    IsManifold 𝓘(ℝ, Fin (fibreDim (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × Mat 14) (symS 14)) → ℝ) ∞
      (levelSet (frameF Gchart chartU) ⟨η77, ηSig_mem 7 7⟩) :=
  isManifold_frames isOpen_chartU contDiffOn_Gchart (fun p _ => Gchim_mem p.2)
    (ηSig_mem 7 7) (ηSig_sq 7 7) η77_ne_zero

lemma fibreDim_chimFrames :
    fibreDim (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × Mat 14) (symS 14) = 105 := by
  rw [fibreDim_frames]; simp; rfl

/-! ### Bridge: the matrix condition is chimeric orthonormality -/

lemma symMat_add (v w : Fin 10 → ℝ) : symMat (v + w) = symMat v + symMat w := by ext; rfl
lemma symMat_smul (c : ℝ) (v : Fin 10 → ℝ) : symMat (c • v) = c • symMat v := by ext; rfl
lemma covec_add (p p' : (Fin 4 → ℝ) →L[ℝ] ℝ) : covec (p + p') = covec p + covec p' := by ext; rfl
lemma covec_smul (c : ℝ) (p : (Fin 4 → ℝ) →L[ℝ] ℝ) : covec (c • p) = c • covec p := by ext; rfl

/-- `Bmod G` as a bilinear form. -/
noncomputable def BmodL (G : Matrix (Fin 4) (Fin 4) ℝ) : CFib →ₗ[ℝ] CFib →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (Bmod G)
    (fun u u' v => by
      simp only [Bmod, chimY, Prod.fst_add, Prod.snd_add, symMat_add, covec_add, Matrix.mul_add,
        Matrix.add_mul, trace_add, add_dotProduct]; ring)
    (fun c u v => by
      simp only [Bmod, chimY, Prod.smul_fst, Prod.smul_snd, symMat_smul, covec_smul,
        Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_dotProduct, smul_eq_mul]; ring)
    (fun u v v' => by
      simp only [Bmod, chimY, Prod.fst_add, Prod.snd_add, symMat_add, covec_add, Matrix.mul_add,
        trace_add, mulVec_add, dotProduct_add]; ring)
    (fun c u v => by
      simp only [Bmod, chimY, Prod.smul_fst, Prod.smul_snd, symMat_smul, covec_smul,
        Matrix.mul_smul, trace_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)

lemma BmodL_apply (G : Matrix (Fin 4) (Fin 4) ℝ) (u v : CFib) : BmodL G u v = Bmod G u v := rfl

lemma ΦL_expand (v : Fin 14 → ℝ) : ΦL v = ∑ k, v k • uΦ k := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 14 → ℝ) by
    ext i; by_cases h : i = k <;> simp [h], map_smul]; rfl

/-- `Bmod (symMat s) (Φ a) (Φ b) = a ⬝ᵥ (Gchim s *ᵥ b)`. -/
lemma Bmod_Φ (s : Fin 10 → ℝ) (a b : Fin 14 → ℝ) :
    Bmod (symMat s) (ΦL a) (ΦL b) = a ⬝ᵥ (Matrix.of (Gchim s) *ᵥ b) := by
  rw [← BmodL_apply, ΦL_expand a, ΦL_expand b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    BmodL_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Gchim, Matrix.of_apply]; ring

/-- `Bm` is the polar form of `Q77` halved, the form used by `orthoSetM`. -/
lemma Bm_eq_polar (x x' : Fin 14 → ℝ) : Bm x x' = QuadraticMap.polar Q77 x x' / 2 :=
  (Bη_Φ_eq x x').symm.trans (Bη_Φ x x')

/-- **Bridge**: the matrix condition `qᵀ Gchim(s) q = η₇₇` says exactly that the frame
`x ↦ Φ(q x)` is an isometry from `(ℝ¹⁴, Q77)` (`Bm = polar Q77 / 2`, `Bm_eq_polar`) to
`(C_s, Bmod)`: the same condition as `orthoSetM` at a point with `Gpt = symMat s`. The
identification of a chart point with `y : Yobs X` is not formalised here. -/
theorem bil_Gchim_iff (s : Fin 10 → ℝ) (q : Mat 14) :
    bil (Gchim s) q q = η77 ↔
      ∀ x x', Bmod (symMat s) (ΦL (Matrix.of q *ᵥ x)) (ΦL (Matrix.of q *ᵥ x')) = Bm x x' := by
  have key : ∀ x x', Bmod (symMat s) (ΦL (Matrix.of q *ᵥ x)) (ΦL (Matrix.of q *ᵥ x')) =
      x ⬝ᵥ (Matrix.of (bil (Gchim s) q q) *ᵥ x') := fun x x' => by
    rw [Bmod_Φ, bil_eq_mat, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
  constructor
  · intro h x x'; rw [key, h]; rfl
  · intro h
    apply Matrix.of.injective
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, single_dot_mulVec] at this
    rw [this]; unfold Bm; rw [single_dot_mulVec]

end GU.Library
