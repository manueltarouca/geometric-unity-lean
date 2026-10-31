import GU.Spinor.SpinSU2
import GU.Spinor.SpinIso6

/-!
# Towards `Spin(6) ≅ SU(4)`: the half-spin representation of `Spin(6)` on `ℂ⁴`

`σ(v)`, for `v ∈ ℝ⁶`, is an explicit complex `4 × 4` matrix with `σ(v) σ(v)ᴴ = σ(v)ᴴ σ(v) = |v|²`
(`σ_mul_conj`, `σ_conj_mul`) and `det σ(v) = |v|⁴` (`det_σM`). It is `v₅ + i ∑ v_k τ_k`, with
`τ₁..τ₅` five anticommuting Hermitian matrices: `X⊗1, Y⊗1, Z⊗X, Z⊗Y, Z⊗Z`.
`γ₆ = CliffordAlgebra.lift (v ↦ [[0, σ(v)], [σ(v)ᴴ, 0]]) : Cl(Q₆) →ₐ M₂(M₄(ℂ))` is the spin
representation on `ℂ⁸`. Even elements are block-diagonal, and the `(0,0)` block is a half-spin
representation. **`spinSU4 : spinGroup Q₆ →* SU(4)`** (with `det = 1`, `detU_eq_one`), and it is
nontrivial (`spinSU4_negOne : −1 ↦ −1`).

Not proved yet: that `spinSU4` is injective or surjective, i.e. `Spin(6) ≅ SU(4)`.
-/

namespace GU.Spinor

open CliffordAlgebra Matrix

/-- `σ(v) = v₅ + i(v₀ X⊗1 + v₁ Y⊗1 + v₂ Z⊗X + v₃ Z⊗Y + v₄ Z⊗Z)`. -/
def σM (v : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![⟨v 5, v 4⟩, ⟨v 3, v 2⟩, ⟨v 1, v 0⟩, 0;
     ⟨-v 3, v 2⟩, ⟨v 5, -v 4⟩, 0, ⟨v 1, v 0⟩;
     ⟨-v 1, v 0⟩, 0, ⟨v 5, -v 4⟩, ⟨-v 3, -v 2⟩;
     0, ⟨-v 1, v 0⟩, ⟨v 3, -v 2⟩, ⟨v 5, v 4⟩]

/-- `σ` as a real-linear map. -/
noncomputable def σL : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := σM
  map_add' v w := Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [σM] <;> ring
  map_smul' c v := Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [σM]

lemma Q6_apply (v : Fin 6 → ℝ) : Q6 v = ∑ i, v i ^ 2 := by
  simp [Q6, QuadraticMap.weightedSumSquares_apply, sq]

lemma σ_mul_conj (v : Fin 6 → ℝ) : σM v * (σM v)ᴴ = ((Q6 v : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Q6_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [σM, Matrix.mul_apply, Fin.sum_univ_succ, sq,
      Complex.mul_re, Complex.mul_im] <;> ring

lemma σ_conj_mul (v : Fin 6 → ℝ) : (σM v)ᴴ * σM v = ((Q6 v : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Q6_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [σM, Matrix.mul_apply, Fin.sum_univ_succ, sq,
      Complex.mul_re, Complex.mul_im] <;> ring

lemma det_σM (v : Fin 6 → ℝ) : (σM v).det = (((Q6 v) ^ 2 : ℝ) : ℂ) := by
  rw [Q6_apply, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.det_unique, Fin.sum_univ_zero]
  apply Complex.ext <;>
    simp [σM, Matrix.submatrix_apply, Fin.succAbove, Complex.mul_re, Complex.mul_im, pow_succ] <;> ring

/-! ### The representation `γ₆ : Cl(Q₆) → M₂(M₄(ℂ))` -/

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ
abbrev M8 := Matrix (Fin 2) (Fin 2) M4C

/-- `γ(v) = [[0, σ(v)], [σ(v)ᴴ, 0]]`. -/
noncomputable def g6 : (Fin 6 → ℝ) →ₗ[ℝ] M8 where
  toFun v := !![0, σM v; (σM v)ᴴ, 0]
  map_add' v w := Matrix.ext fun i j => by
    have ha : σM (v + w) = σM v + σM w := σL.map_add v w
    fin_cases i <;> fin_cases j <;> simp [ha, Matrix.conjTranspose_add]
  map_smul' c v := Matrix.ext fun i j => by
    have hs : σM (c • v) = c • σM v := σL.map_smul c v
    fin_cases i <;> fin_cases j <;> simp [hs, Matrix.conjTranspose_smul]

lemma g6_sq (v : Fin 6 → ℝ) : g6 v * g6 v = algebraMap ℝ M8 (Q6 v) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [g6, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply, σ_mul_conj,
      σ_conj_mul, Algebra.algebraMap_eq_smul_one]

/-- The representation of `Cl(Q₆)` on `ℂ⁸ = ℂ⁴ ⊕ ℂ⁴`. -/
noncomputable def γ6 : CliffordAlgebra Q6 →ₐ[ℝ] M8 := CliffordAlgebra.lift Q6 ⟨g6, g6_sq⟩

@[simp] lemma γ6_ι (v : Fin 6 → ℝ) : γ6 (ι Q6 v) = g6 v := CliffordAlgebra.lift_ι_apply _ _ _

/-- Block-diagonal. -/
def IsDiag8 (A : M8) : Prop := A 0 1 = 0 ∧ A 1 0 = 0

lemma isDiag8_mul {A B : M8} (hA : IsDiag8 A) (hB : IsDiag8 B) : IsDiag8 (A * B) := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1, hA.2, hB.1, hB.2]

lemma γ6_even {x : CliffordAlgebra Q6} (hx : x ∈ evenOdd Q6 0) : IsDiag8 (γ6 x) := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]; constructor <;> simp [Matrix.algebraMap_matrix_apply]
  | add x y _ _ hx hy => rw [map_add]; exact ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, γ6_ι, γ6_ι]
    refine isDiag8_mul ?_ hx
    constructor <;> simp [g6, Matrix.mul_apply, Fin.sum_univ_two]

lemma diag8_mul_00 {A B : M8} (hA : IsDiag8 A) : (A * B) 0 0 = A 0 0 * B 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1]

lemma star_algebraMap_8 (r : ℝ) : star (algebraMap ℝ M8 r) = algebraMap ℝ M8 r := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.star_apply, Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h; simp only [ite_true]
    rw [Algebra.algebraMap_eq_smul_one, StarModule.star_smul, star_one, star_trivial]
  · simp [h, Ne.symm h]

lemma g6_star (v : Fin 6 → ℝ) : star (g6 v) = g6 v := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [g6, Matrix.star_apply, Matrix.star_eq_conjTranspose]

/-- `γ(star x) = γ(involute x)ᴴ`. -/
lemma γ6_star (x : CliffordAlgebra Q6) : γ6 (star x) = star (γ6 (involute x)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [star_algebraMap_Cl, involute.commutes, AlgHom.commutes, star_algebraMap_8]
  | ι v => rw [CliffordAlgebra.star_ι, involute_ι, map_neg, γ6_ι, star_neg, g6_star]
  | mul a b ha hb => rw [star_mul, map_mul, map_mul, ha, hb, map_mul, star_mul]
  | add a b ha hb => rw [star_add, map_add, map_add, ha, hb, map_add, star_add]

lemma involute_of_even {x : CliffordAlgebra Q6} (hx : x ∈ evenOdd Q6 0) : involute x = x := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => exact involute.commutes r
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul_ι_mul m₁ m₂ x _ hx => rw [map_mul, map_mul, involute_ι, involute_ι, hx, neg_mul_neg]

lemma γ6_spin_unitary {x : CliffordAlgebra Q6} (hx : x ∈ spinGroup Q6) :
    γ6 x 0 0 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have he := (spinGroup.mem_iff.mp hx).2
  have hd := γ6_even he
  have hst : γ6 (star x) = star (γ6 x) := by rw [γ6_star, involute_of_even he]
  have h1 : star (γ6 x) * γ6 x = 1 := by
    rw [← hst, ← map_mul, spinGroup.star_mul_self_of_mem hx, map_one]
  have := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hd.2, star_zero, zero_mul,
    add_zero, Matrix.one_apply_eq] at this
  exact Matrix.mem_unitaryGroup_iff'.mpr this

/-- **`spinGroup Q₆ →* U(4)`**, `x ↦ γ(x)₀₀`. -/
noncomputable def spinU4 : spinGroup Q6 →* Matrix.unitaryGroup (Fin 4) ℂ where
  toFun x := ⟨γ6 x 0 0, γ6_spin_unitary x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    show γ6 ((x : CliffordAlgebra Q6) * y) 0 0 = γ6 x 0 0 * γ6 y 0 0
    rw [map_mul, diag8_mul_00 (γ6_even (spinGroup.mem_iff.mp x.2).2)])

/-! ### Determinant one -/

/-- `det ∘ spinU4`. -/
noncomputable def detU : spinGroup Q6 →* ℂ :=
  Matrix.detMonoidHom.comp ((Matrix.unitaryGroup (Fin 4) ℂ).subtype.comp spinU4)

lemma detU_pair (a b : Fin 6 → ℝ) (ha : Q6 a = 1) (hb : Q6 b = 1)
    (h : ι Q6 a * ι Q6 b ∈ spinGroup Q6) : detU ⟨ι Q6 a * ι Q6 b, h⟩ = 1 := by
  show (γ6 (ι Q6 a * ι Q6 b) 0 0).det = 1
  rw [map_mul, γ6_ι, γ6_ι]
  have : (g6 a * g6 b) 0 0 = σM a * (σM b)ᴴ := by
    simp [g6, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, Matrix.det_mul, Matrix.det_conjTranspose, det_σM, det_σM, ha, hb]
  simp

/-- `detU ∘ spin6Equiv⁻¹` as a homomorphism on `Spin6`. -/
noncomputable def detH : Spin6 →* ℂ := detU.comp spin6Equiv.symm.toMonoidHom

lemma detH_eq_one (y : Spin6) : detH y = 1 := by
  obtain ⟨z, hz⟩ := y
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, hqa, hqb, hzab⟩ := hz
    have hQ : ∀ c, SuppIn S6 c → Q6 (res6 c) = Q77 c := fun c hc => by
      rw [← Q77_f6L, f6L_res6 hc]
    have hmem := pair_mem_gen Q6 (res6 a) (res6 b) (by rw [hQ a ha, hQ b hb, hqa, hqb]; norm_num)
    have hpre : spin6Equiv.symm ⟨z, Subgroup.subset_closure ⟨a, b, ha, hb, hqa, hqb, hzab⟩⟩ =
        ⟨ι Q6 (res6 a) * ι Q6 (res6 b), hmem⟩ := by
      apply spin6Equiv.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext; apply Subtype.ext
      show z.1 = Φ6 (ι Q6 (res6 a) * ι Q6 (res6 b))
      rw [map_mul, Φ6_ι, Φ6_ι, f6L_res6 ha, f6L_res6 hb, hzab]
    show detU (spin6Equiv.symm _) = 1
    rw [hpre]
    exact detU_pair _ _ (by rw [hQ a ha, hqa]) (by rw [hQ b hb, hqb]) hmem
  | one => exact map_one detH
  | mul u w hu hw ihu ihw =>
    have := map_mul detH ⟨u, hu⟩ ⟨w, hw⟩
    rw [ihu, ihw, one_mul] at this
    exact this
  | inv u hu ihu =>
    have := map_mul detH (⟨u, hu⟩ : Spin6)⁻¹ ⟨u, hu⟩
    rw [inv_mul_cancel, map_one, ihu, mul_one] at this
    exact this.symm

/-- **Spin elements have determinant one** in the half-spin representation. -/
theorem detU_eq_one (x : spinGroup Q6) : detU x = 1 := by
  have := detH_eq_one (spin6Equiv x)
  simpa [detH] using this

lemma spinU4_mem_SU (x : spinGroup Q6) :
    ((spinU4 x : Matrix.unitaryGroup (Fin 4) ℂ) : M4C) ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ :=
  ⟨(spinU4 x).2, detU_eq_one x⟩

/-- **`spinGroup Q₆ →* SU(4)`**: the half-spin representation of `Spin(6)` on `ℂ⁴`. -/
noncomputable def spinSU4 : spinGroup Q6 →* Matrix.specialUnitaryGroup (Fin 4) ℂ where
  toFun x := ⟨spinU4 x, spinU4_mem_SU x⟩
  map_one' := Subtype.ext (by
    show ((spinU4 1 : Matrix.unitaryGroup (Fin 4) ℂ) : M4C) = 1
    rw [map_one]; rfl)
  map_mul' x y := Subtype.ext (by
    show ((spinU4 (x * y) : Matrix.unitaryGroup (Fin 4) ℂ) : M4C) = _
    rw [map_mul]; rfl)

/-- `−1 = ι(e₀) ι(−e₀) ∈ spinGroup Q₆`. -/
noncomputable def negOne6 : spinGroup Q6 :=
  ⟨ι Q6 (Pi.single 0 1) * ι Q6 (-Pi.single 0 1), pair_mem_gen Q6 _ _ (by
    rw [QuadraticMap.map_neg]; simp [Q6, QuadraticMap.weightedSumSquares_apply, Pi.single_apply])⟩

lemma negOne6_val : (negOne6 : CliffordAlgebra Q6) = -1 := by
  show ι Q6 (Pi.single 0 1) * ι Q6 (-Pi.single 0 1) = -1
  rw [map_neg, mul_neg, ι_sq_scalar, show Q6 (Pi.single 0 1) = 1 by
    simp [Q6, QuadraticMap.weightedSumSquares_apply, Pi.single_apply], map_one]

/-- **Nontriviality**: `spinSU4 (−1) = −1`. -/
theorem spinSU4_negOne : ((spinSU4 negOne6 : Matrix.specialUnitaryGroup (Fin 4) ℂ) : M4C) = -1 := by
  show γ6 (negOne6 : CliffordAlgebra Q6) 0 0 = -1
  rw [negOne6_val, map_neg, map_one]
  rfl

end GU.Spinor
