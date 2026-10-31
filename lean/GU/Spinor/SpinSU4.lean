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

**`spinSU4_injective`**: `Spin(6) ↪ SU(4)`. Spin elements act on `W6` by `σ(v) ↦ A σ(v) Bᴴ`
(`vecRep_spinU`). If `A = 1`, this forces `Bᴴ = ±1`, so `x` acts as `±1` on `W6`. Then `x = ±1`, or
`x = ±ω₆` (the volume element, with `γ(ω₆) = diag(−i, i)`); only `x = 1` has `A = 1`.

Not proved yet: surjectivity, so `Spin(6) ≅ SU(4)` is still open.
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

/-! ### Vector action -/

lemma diag8_conj_01 {A : M8} (hA : IsDiag8 A) (G : M8) :
    (A * G * star A) 0 1 = A 0 0 * G 0 1 * star (A 1 1) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hA.1, hA.2]

/-- **Vector action**: `x ∈ spinGroup Q₆` acts on `W6` by `σ(v) ↦ A σ(v) Bᴴ`, where `γ(x) = diag(A, B)`. -/
lemma vecRep_spinU (x : spinGroup Q6) (v : Fin 6 → ℝ) :
    σM (res6 (vecRep (spin6Hom x) (f6L v))) =
      γ6 (x : CliffordAlgebra Q6) 0 0 * σM v * (γ6 (x : CliffordAlgebra Q6) 1 1)ᴴ ∧
    SuppIn S6 (vecRep (spin6Hom x) (f6L v)) := by
  set y := spin6Hom x
  set u := vecRep y (f6L v)
  have hout := (spin6_iff y).mp (spin6Hom_mem x)
  have hsu : SuppIn S6 u := supp_of_polar u fun j hj => by
    rw [← hout.2.2 j hj, vecRep_polar, polar_eb_right,
      f6L_off v (by revert hj; revert j; unfold inW6; decide)]; ring
  refine ⟨?_, hsu⟩
  have hιu : ι Q77 u = Φ6 ((x : CliffordAlgebra Q6) * ι Q6 v * star (x : CliffordAlgebra Q6)) := by
    show ι Q77 (vecL _ _) = _
    rw [ι_vecL, map_mul, map_mul, Φ6_ι, Φ6_star]; rfl
  have hw : (x : CliffordAlgebra Q6) * ι Q6 v * star (x : CliffordAlgebra Q6) = ι Q6 (res6 u) := by
    apply Φ6_injective
    rw [← hιu, Φ6_ι, f6L_res6 hsu]
  have he := (spinGroup.mem_iff.mp x.2).2
  have hγ := congrArg γ6 hw
  rw [map_mul, map_mul, γ6_star, involute_of_even he, γ6_ι, γ6_ι] at hγ
  have h01 := congrFun (congrFun hγ 0) 1
  rw [diag8_conj_01 (γ6_even he)] at h01
  simpa [g6, Matrix.star_eq_conjTranspose] using h01.symm

/-! ### Injectivity -/

lemma σ_forces (u w w' : Fin 6 → ℝ) (h0 : σM w = σM (Pi.single 0 1) * σM u)
    (h1 : σM w' = σM (Pi.single 1 1) * σM u) : u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 ∧ u 3 = 0 ∧ u 4 = 0 := by
  have e : ∀ i j, (σM w i j = (σM (Pi.single 0 1) * σM u) i j) ∧
      (σM w' i j = (σM (Pi.single 1 1) * σM u) i j) :=
    fun i j => ⟨congrFun (congrFun h0 i) j, congrFun (congrFun h1 i) j⟩
  have e03 := e 0 3
  have e00 := e 0 0
  have e11 := e 1 1
  have e02 := e 0 2
  have e13 := e 1 3
  simp [σM, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff] at e03 e00 e11 e02 e13
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := e03
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := e00
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := e11
  obtain ⟨⟨d1, d2⟩, d3, d4⟩ := e02
  obtain ⟨⟨f1, f2⟩, f3, f4⟩ := e13
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma σM_injective : Function.Injective σM := fun v w h => by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  simp [σM, Complex.ext_iff] at e00 e01 e02
  funext k; fin_cases k
  · exact e02.2
  · exact e02.1
  · exact e01.2
  · exact e01.1
  · exact e00.2
  · exact e00.1

lemma σM_e5 : σM (Pi.single 5 1) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [σM, Pi.single_apply, Matrix.one_apply] <;> rfl

lemma σM_neg (v : Fin 6 → ℝ) : σM (-v) = -σM v := by
  rw [show σM (-v) = σL (-v) from rfl, map_neg]; rfl

/-- Two elements of `Spin6` that agree on `W6` have equal `vecRep` (both fix the complement). -/
lemma vecRep_ext6 {y y' : Spin77} (hy : y ∈ Spin6) (hy' : y' ∈ Spin6)
    (h : ∀ v, vecRep y (f6L v) = vecRep y' (f6L v)) : vecRep y = vecRep y' := by
  have hout := ((spin6_iff y).mp hy).2.2
  have hout' := ((spin6_iff y').mp hy').2.2
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun ℝ (Fin 14)).ext fun j => ?_
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
  by_cases hj : j ∈ S6
  · have hk : ∃ k : Fin 6, emb6 k = j := by revert hj; revert j; decide
    obtain ⟨k, rfl⟩ := hk
    rw [show (Pi.single (emb6 k) 1 : Fin 14 → ℝ) = f6L (Pi.single k 1) from (f6L_single k).symm]
    exact h _
  · exact (hout j hj).trans (hout' j hj).symm

/-- If `x` acts on `σ(W6)` as `σ(v) ↦ σ(s • v)`, then `x` acts as `s` on `W6`. -/
lemma action_scalar (x : spinGroup Q6) (s : ℝ)
    (hA : ∀ v, σM (res6 (vecRep (spin6Hom x) (f6L v))) = σM (s • v)) (v : Fin 6 → ℝ) :
    vecRep (spin6Hom x) (f6L v) = f6L (s • v) := by
  have hsupp := (vecRep_spinU x v).2
  rw [← f6L_res6 hsupp, σM_injective (hA v)]

/-- The volume element `ω₆ = e₀e₁e₂e₃e₄e₅ ∈ spinGroup Q₆`. -/
noncomputable def ω6 : spinGroup Q6 :=
  let p : Fin 6 → Fin 6 → spinGroup Q6 := fun a b =>
    ⟨ι Q6 (Pi.single a 1) * ι Q6 (Pi.single b 1), pair_mem_gen Q6 _ _ (by
      simp [Q6, QuadraticMap.weightedSumSquares_apply, Pi.single_apply])⟩
  p 0 1 * p 2 3 * p 4 5

lemma g6_pair (a b : Fin 6 → ℝ) :
    g6 a * g6 b = !![σM a * (σM b)ᴴ, 0; 0, (σM a)ᴴ * σM b] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [g6, Matrix.mul_apply, Fin.sum_univ_two]

lemma diag8_mk_mul (A B C D : M4C) :
    (!![A, 0; 0, B] : M8) * !![C, 0; 0, D] = !![A * C, 0; 0, B * D] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma γ6_ω6 : γ6 (ω6 : CliffordAlgebra Q6) =
    !![σM (Pi.single 0 1) * (σM (Pi.single 1 1))ᴴ * (σM (Pi.single 2 1) * (σM (Pi.single 3 1))ᴴ) *
        (σM (Pi.single 4 1) * (σM (Pi.single 5 1))ᴴ), 0;
      0, (σM (Pi.single 0 1))ᴴ * σM (Pi.single 1 1) * ((σM (Pi.single 2 1))ᴴ * σM (Pi.single 3 1)) *
        ((σM (Pi.single 4 1))ᴴ * σM (Pi.single 5 1))] := by
  show γ6 (ι Q6 (Pi.single 0 1) * ι Q6 (Pi.single 1 1) * (ι Q6 (Pi.single 2 1) * ι Q6 (Pi.single 3 1)) *
    (ι Q6 (Pi.single 4 1) * ι Q6 (Pi.single 5 1))) = _
  simp only [map_mul, γ6_ι, g6_pair, diag8_mk_mul]

set_option maxHeartbeats 2000000 in
lemma blk00 : σM (Pi.single 0 1) * (σM (Pi.single 1 1))ᴴ * (σM (Pi.single 2 1) * (σM (Pi.single 3 1))ᴴ) *
    (σM (Pi.single 4 1) * (σM (Pi.single 5 1))ᴴ) = (-Complex.I) • (1 : M4C) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [σM, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply, Matrix.one_apply, Complex.ext_iff,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

set_option maxHeartbeats 2000000 in
lemma blk11 : (σM (Pi.single 0 1))ᴴ * σM (Pi.single 1 1) * ((σM (Pi.single 2 1))ᴴ * σM (Pi.single 3 1)) *
    ((σM (Pi.single 4 1))ᴴ * σM (Pi.single 5 1)) = Complex.I • (1 : M4C) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [σM, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply, Matrix.one_apply, Complex.ext_iff,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

lemma γ6_ω6_00 : γ6 (ω6 : CliffordAlgebra Q6) 0 0 = (-Complex.I) • (1 : M4C) := by
  rw [γ6_ω6]; exact blk00

lemma γ6_ω6_11 : γ6 (ω6 : CliffordAlgebra Q6) 1 1 = Complex.I • (1 : M4C) := by
  rw [γ6_ω6]; exact blk11

lemma γ6_entry_ne_one {x : CliffordAlgebra Q6} {c : ℂ} (h : γ6 x 0 0 = c • (1 : M4C)) (hc : c ≠ 1) :
    γ6 x 0 0 ≠ 1 := by
  intro h1
  have := congrFun (congrFun (h.symm.trans h1) 0) 0
  simp at this
  exact hc this

lemma vecRep_ω6 (v : Fin 6 → ℝ) : vecRep (spin6Hom ω6) (f6L v) = f6L (-v) := by
  have h := vecRep_spinU ω6 v
  rw [← f6L_res6 h.2]
  congr 1
  apply σM_injective
  rw [h.1, γ6_ω6_00, γ6_ω6_11, σM_neg]
  refine Matrix.ext fun i j => ?_
  simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq]
  ring_nf
  simp [Complex.ext_iff]

/-- **`spinSU4` is injective**: `Spin(6) ↪ SU(4)`. -/
theorem spinSU4_injective : Function.Injective spinSU4 := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hA : γ6 (x : CliffordAlgebra Q6) 0 0 = 1 :=
    congrArg (fun z : Matrix.specialUnitaryGroup (Fin 4) ℂ => (z : M4C)) hx
  have hact : ∀ v, σM (res6 (vecRep (spin6Hom x) (f6L v))) =
      σM v * (γ6 (x : CliffordAlgebra Q6) 1 1)ᴴ := fun v => by
    rw [(vecRep_spinU x v).1, hA, one_mul]
  set u := res6 (vecRep (spin6Hom x) (f6L (Pi.single 5 1)))
  have hu : σM u = (γ6 (x : CliffordAlgebra Q6) 1 1)ᴴ := by
    rw [hact, σM_e5, one_mul]
  have h0 := hact (Pi.single 0 1)
  have h1 := hact (Pi.single 1 1)
  rw [← hu] at h0 h1
  obtain ⟨u0, u1, u2, u3, u4⟩ := σ_forces _ _ _ h0 h1
  have hQu : Q6 u = 1 := by
    have hs := (vecRep_spinU x (Pi.single 5 1)).2
    rw [← Q77_f6L, f6L_res6 hs, vecRep_isometry, Q77_f6L]
    simp [Q6, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  have hu5 : u 5 = 1 ∨ u 5 = -1 := by
    rw [Q6_apply] at hQu
    simp only [Fin.sum_univ_six, u0, u1, u2, u3, u4] at hQu
    have : u 5 * u 5 = 1 := by nlinarith
    exact mul_self_eq_one_iff.mp this
  have huv : u = u 5 • Pi.single 5 1 := by
    funext k; fin_cases k <;> simp [u0, u1, u2, u3, u4]
  have hB : (γ6 (x : CliffordAlgebra Q6) 1 1)ᴴ = (u 5 : ℂ) • (1 : M4C) := by
    rw [← hu, huv, show σM (u 5 • Pi.single 5 1) = σL (u 5 • Pi.single 5 1) from rfl, map_smul]
    show u 5 • σM (Pi.single 5 1) = _
    rw [σM_e5]
    refine Matrix.ext fun i j => ?_
    simp [Matrix.one_apply, Complex.real_smul]
  have hscal : ∀ v, vecRep (spin6Hom x) (f6L v) = f6L (u 5 • v) := fun v => by
    apply action_scalar x (u 5)
    intro w
    rw [hact, hB, show σM (u 5 • w) = σL (u 5 • w) from rfl, map_smul]
    show σM w * ((u 5 : ℂ) • 1) = u 5 • σM w
    rw [Matrix.mul_smul, mul_one]
    refine Matrix.ext fun i j => ?_
    simp [Complex.real_smul]
  have hy := spin6Hom_mem x
  rcases hu5 with h5 | h5
  · -- acts trivially
    have hv : vecRep (spin6Hom x) = vecRep (1 : Spin77) :=
      vecRep_ext6 hy (Subgroup.one_mem _) fun v => by rw [hscal, h5, one_smul, map_one]; rfl
    rcases (vecRep_eq_iff _ _).mp hv with e | e
    · apply Subtype.ext
      apply Φ6_injective
      show Φ6 (x : CliffordAlgebra Q6) = Φ6 1
      rw [map_one]; exact e
    · exfalso
      have hx1 : (x : CliffordAlgebra Q6) = -1 := Φ6_injective (by
        rw [map_neg, map_one]; exact e)
      apply γ6_entry_ne_one (c := -1) _ (by norm_num) hA
      rw [hx1, map_neg, map_one]
      refine Matrix.ext fun i j => ?_
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · -- acts as `−1` on `W6`: then `x = ±ω₆`
    have hv : vecRep (spin6Hom x) = vecRep (spin6Hom ω6) :=
      vecRep_ext6 hy (spin6Hom_mem ω6) fun v => by
        rw [hscal, h5, neg_one_smul, vecRep_ω6]
    rcases (vecRep_eq_iff _ _).mp hv with e | e
    · exfalso
      have hxω : (x : CliffordAlgebra Q6) = ω6 := Φ6_injective e
      apply γ6_entry_ne_one (c := -Complex.I) _ (by simp [Complex.ext_iff]) hA
      rw [hxω, γ6_ω6_00]
    · exfalso
      have hxω : (x : CliffordAlgebra Q6) = -ω6 := Φ6_injective (by rw [map_neg]; exact e)
      apply γ6_entry_ne_one (c := Complex.I) _ (by simp [Complex.ext_iff]) hA
      rw [hxω, map_neg, Matrix.neg_apply, γ6_ω6_00, neg_smul, neg_neg]

end GU.Spinor
