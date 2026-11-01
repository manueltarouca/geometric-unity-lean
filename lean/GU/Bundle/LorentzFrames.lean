import GU.Bundle.TimeReflection

/-!
# Phase 6, item 1 (algebraic core; the general-X clause of Phase 5 item 5): Lorentz frames with the same time orientation are `SO₀`-related

For an invertible `Λ`, `lorM Λ` is the matrix of `ΦL⁻¹ ∘ TP Λ ∘ ΦL` on `ℝ¹⁴`. Then
`tpFrame P ∘ lorM Λ = tpFrame (P Λ)` (`tpFrame_mul`), `lorM` is multiplicative (`lorM_mul`), and for a
Lorentz transformation `lorM Λ ∈ O(7,7)` (`lorM_mem`).

**`gRefl_mem_SO0`**: the reflection lies in `SO₀` (explicit rotation path). The main consequence,
`lorO_mem_SO0` (in `LorentzPaths.lean`): for an orthochronous Lorentz transformation `Λ`
(`Λ ηR Λᵀ = ηR`, `Λ₀₀ > 0`), `lorM Λ ∈ SO₀(7,7)`, whatever the sign of `det Λ`.
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### `TP` is multiplicative -/

lemma toCLM_mul (A B : M4) : toCLM (A * B) = (toCLM A).comp (toCLM B) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [toCLM_apply, Matrix.mulVec_mulVec]

lemma TP_mul {A B : M4} (hA : IsUnit A) (hB : IsUnit B) (u : CFib) :
    TP (A * B) (hA.mul hB) u = TP A hA (TP B hB u) := by
  have hsym : (B * symMat u.1 * Bᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm _).eq, Matrix.mul_assoc]
  refine Prod.ext ?_ ?_
  · show symCoords (A * B * symMat u.1 * (A * B)ᵀ) = symCoords (A * symMat (symCoords (B * symMat u.1 * Bᵀ)) * Aᵀ)
    rw [symMat_symCoords _ hsym, transpose_mul]
    simp only [Matrix.mul_assoc]
  · show u.2.comp (toCLM (A * B)⁻¹) = (u.2.comp (toCLM B⁻¹)).comp (toCLM A⁻¹)
    rw [Matrix.mul_inv_rev, toCLM_mul, ContinuousLinearMap.comp_assoc]

/-! ### The matrix of a transport -/

/-- `ΦL⁻¹ ∘ TP Λ ∘ ΦL` as a linear map. -/
def lorL (Λ : M4) (h : IsUnit Λ) : R14 →ₗ[ℝ] R14 :=
  (ΦL.symm : CFib →ₗ[ℝ] R14) ∘ₗ (TP Λ h).toLinearMap ∘ₗ (ΦL : R14 →ₗ[ℝ] CFib)

/-- **The matrix of `Λ` on frames** (`0` if `Λ` is not invertible); in `O(7,7)` when `Λ` is Lorentz
(`lorM_mem`). -/
def lorM (Λ : M4) : Mat 14 := by
  classical
  exact if h : IsUnit Λ then Matrix.of.symm (LinearMap.toMatrix' (lorL Λ h)) else 0

lemma lorM_of (Λ : M4) (h : IsUnit Λ) : Matrix.of (lorM Λ) = LinearMap.toMatrix' (lorL Λ h) := by
  classical
  unfold lorM
  rw [dite_cond_eq_true (eq_true h)]
  rfl

lemma matCLM_lorM (Λ : M4) (h : IsUnit Λ) (v : R14) : matCLM (lorM Λ) v = lorL Λ h v := by
  rw [matCLM_apply, lorM_of Λ h, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- **Frames transform by `lorM`.** -/
theorem tpFrame_mul {P Λ : M4} (hP : IsUnit P) (hΛ : IsUnit Λ) :
    (tpFrame P hP).comp (matCLM (lorM Λ)) = tpFrame (P * Λ) (hP.mul hΛ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, matCLM_lorM Λ hΛ, tpFrame_apply, tpFrame_apply, TP_mul]
  show TP P hP (ΦL (ΦL.symm (TP Λ hΛ (ΦL v)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

lemma lorL_mul {A B : M4} (hA : IsUnit A) (hB : IsUnit B) :
    lorL (A * B) (hA.mul hB) = lorL A hA ∘ₗ lorL B hB := by
  refine LinearMap.ext fun v => ?_
  show ΦL.symm (TP (A * B) (hA.mul hB) (ΦL v)) = ΦL.symm (TP A hA (ΦL (ΦL.symm (TP B hB (ΦL v)))))
  rw [ContinuousLinearEquiv.apply_symm_apply, TP_mul]

lemma lorM_mul {A B : M4} (hA : IsUnit A) (hB : IsUnit B) :
    Matrix.of (lorM (A * B)) = Matrix.of (lorM A) * Matrix.of (lorM B) := by
  rw [lorM_of _ (hA.mul hB), lorM_of _ hA, lorM_of _ hB, lorL_mul hA hB, LinearMap.toMatrix'_comp]

lemma TP_one (u : CFib) : TP 1 isUnit_one u = u := by
  refine Prod.ext ?_ ?_
  · show symCoords (1 * symMat u.1 * 1ᵀ) = u.1
    simp [symCoords_symMat]
  · show u.2.comp (toCLM 1⁻¹) = u.2
    refine ContinuousLinearMap.ext fun w => ?_
    simp [toCLM_apply]

lemma lorM_one : Matrix.of (lorM 1) = 1 := by
  rw [lorM_of 1 isUnit_one]
  have : lorL 1 isUnit_one = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    show ΦL.symm (TP 1 isUnit_one (ΦL v)) = v
    rw [TP_one, ContinuousLinearEquiv.symm_apply_apply]
  rw [this, LinearMap.toMatrix'_id]

/-- A Lorentz transformation. -/
def IsLorentz (Λ : M4) : Prop := Λ * ηR * Λᵀ = ηR

lemma IsLorentz.isUnit {Λ : M4} (h : IsLorentz Λ) : IsUnit Λ :=
  isUnit_of_eta_eq isUnit_one (by rw [h]; simp)

lemma Bm_lorL {Λ : M4} (h : IsLorentz Λ) (v w : R14) :
    Bm (lorL Λ h.isUnit v) (lorL Λ h.isUnit w) = Bm v w := by
  show Bm (ΦL.symm (TP Λ h.isUnit (ΦL v))) (ΦL.symm (TP Λ h.isUnit (ΦL w))) = _
  rw [← Bη_Φ_eq, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ← Bη_Φ_eq]
  have := TP_isometry Λ h.isUnit (ΦL v) (ΦL w)
  rw [h] at this
  exact this

/-- **A Lorentz transformation gives an element of `O(7,7)`.** -/
theorem lorM_mem {Λ : M4} (h : IsLorentz Λ) : lorM Λ ∈ O77 := by
  rw [mem_Orth_iff_mat]
  ext i j
  have hcol : ∀ k, Matrix.of (lorM Λ) *ᵥ Pi.single k 1 = lorL Λ h.isUnit (Pi.single k 1) := fun k => by
    rw [← matCLM_apply, matCLM_lorM Λ h.isUnit]
  have e : ((Matrix.of (lorM Λ))ᵀ * Matrix.of η77 * Matrix.of (lorM Λ)) i j =
      Bm (Matrix.of (lorM Λ) *ᵥ Pi.single i 1) (Matrix.of (lorM Λ) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    simp only [Bm, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [e, hcol, hcol, Bm_lorL h, Bm_singles]
  rfl

/-- `lorM` as an element of `O77`. -/
def lorO (Λ : M4) (h : IsLorentz Λ) : O77 := ⟨lorM Λ, lorM_mem h⟩

lemma lorO_val (Λ : M4) (h : IsLorentz Λ) : ((lorO Λ h : O77) : Mat 14) = lorM Λ := rfl

lemma lorO_one : lorO 1 (by simp [IsLorentz]) = 1 := by
  apply Subtype.ext
  show lorM 1 = Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)
  rw [← lorM_one]; rfl

lemma lorO_mul {A B : M4} (hA : IsLorentz A) (hB : IsLorentz B) (hAB : IsLorentz (A * B)) :
    lorO (A * B) hAB = lorO A hA * lorO B hB := by
  apply Subtype.ext
  show lorM (A * B) = mulM (lorM A) (lorM B)
  unfold mulM
  rw [← lorM_mul hA.isUnit hB.isUnit]; rfl

/-! ### Continuity -/

lemma continuous_lorM {Z : Type*} [TopologicalSpace Z] {Λ : Z → M4} (hΛ : Continuous Λ)
    (hu : ∀ z, IsUnit (Λ z)) : Continuous fun z => lorM (Λ z) := by
  have hT : Continuous fun z => tpF (Λ z) :=
    continuousOn_univ.mp (continuousOn_tpF (A := Set.univ) hΛ.continuousOn fun z _ => hu z)
  have he : ∀ z i j, lorM (Λ z) i j = ΦL.symm (tpF (Λ z) (Pi.single j 1)) i := by
    intro z i j
    have : lorM (Λ z) i j = LinearMap.toMatrix' (lorL (Λ z) (hu z)) i j :=
      congrFun (congrFun (lorM_of (Λ z) (hu z)) i) j
    rw [this, LinearMap.toMatrix'_apply,
      tpF_of_unit (hu z), tpFrame_apply]
    rfl
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [he]
  exact (continuous_apply i).comp (ΦL.symm.continuous.comp
    ((ContinuousLinearMap.apply ℝ CFib (Pi.single j 1 : R14)).continuous.comp hT))

/-! ### The reflection -/

lemma lorM_rR : lorM rR = gReflM := by
  have h : lorL rR isUnit_rR = Matrix.toLin' (Matrix.of gReflM) := by
    refine LinearMap.ext fun v => ?_
    show ΦL.symm (TP rR isUnit_rR (ΦL v)) = _
    rw [TP_rR, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  apply Matrix.of.injective
  rw [lorM_of rR isUnit_rR, h, LinearMap.toMatrix'_toLin']

/-- Rotation by `θ` in the planes `(0,1)` (signature `+`) and `(7,11)` (signature `−`). -/
def rotM (θ : ℝ) : Mat 14 := fun i j =>
  if i = j then (if i = 0 ∨ i = 1 ∨ i = 7 ∨ i = 11 then Real.cos θ else 1)
  else if (i = 1 ∧ j = 0) ∨ (i = 11 ∧ j = 7) then Real.sin θ
  else if (i = 0 ∧ j = 1) ∨ (i = 7 ∧ j = 11) then -Real.sin θ else 0

lemma eta77_diag : Matrix.of η77 = Matrix.diagonal fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1 :=
  rfl

lemma rotM_mem (θ : ℝ) : rotM θ ∈ O77 := by
  rw [mem_Orth_iff_mat, eta77_diag]
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rw [ Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.diagonal] <;> nlinarith

lemma continuous_rotM : Continuous rotM := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold rotM
  split_ifs <;> fun_prop

/-- **The reflection lies in the identity component.** -/
theorem gRefl_mem_SO0 : gRefl ∈ SO0 := by
  let γ : ℝ → O77 := fun t => ⟨rotM (Real.pi * t), rotM_mem _⟩
  have hγ : Continuous γ := (continuous_rotM.comp (continuous_const.mul continuous_id)).subtype_mk _
  have h0 : γ 0 = 1 := by
    apply Subtype.ext
    show rotM (Real.pi * 0) = Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotM]
  have h1 : γ 1 = gRefl := by
    apply Subtype.ext
    show rotM (Real.pi * 1) = gReflM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotM, gReflM, dRefl, Matrix.diagonal]
  have hsub := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).image γ hγ.continuousOn
  have hmem : (1 : O77) ∈ γ '' Set.Icc 0 1 := ⟨0, ⟨le_refl _, zero_le_one⟩, h0⟩
  have := hsub.subset_connectedComponent hmem ⟨1, ⟨zero_le_one, le_refl _⟩, h1⟩
  exact this

end

end GU.Library
