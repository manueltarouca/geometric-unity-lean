import GU.Spinor.SpinCover
import GU.Observerse.ChimericCovariance
import GU.Observerse.ChimericBasis

/-!
# `O(Bη) ≅ O(7,7)` and the homomorphism `Spin(7,7) → O(Bη)`

* `Φiso : (ℝ¹⁴, Q77) ≃ (CFib, Bη)` with `Bη (Φ x) (Φ x) = Q77 x` (`Φiso_isometry`): an explicit
  isometry built from the rescaled, sign-ordered chimeric basis.
* `spinToOG : Spin(7,7) →* O(Bη)`, `x ↦ Φ ∘ vecRep x ∘ Φ⁻¹` (`spinToOG`). This is the structure-group
  map along which a spin structure lifts the orthonormal frame bundle (`OrthoFrames.lean`), and
  `−1` maps to the identity (`spinToOG_neg_one`).
-/

open GU GU.Observerse GU.Chimeric GU.Spinor Matrix

namespace GU.Iso77

theorem finrank_CFib : Module.finrank ℝ CFib = 14 := by
  rw [Module.finrank_prod]
  have : Module.finrank ℝ ((Fin 4 → ℝ) →L[ℝ] ℝ) = 4 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin 4 → ℝ) (F' := ℝ)).finrank_eq]
    simp
  rw [this]; simp

noncomputable def dotCLM (q : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ q)

lemma covec_dotCLM (q : Fin 4 → ℝ) : covec (dotCLM q) = q := by
  ext i; simp [covec, dotCLM, dotProductBilin, dotProduct, Pi.single_apply]

lemma ηR_eq : ηR = ηr := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, ηr, diagonal]

/-- Convert `E14 = (H*-vector, Sym² coords)` to `CFib`. -/
noncomputable def toCF (x : E14) : CFib := (x.2, dotCLM x.1)

lemma ηr_inv : ηr⁻¹ = ηr := by rw [← ηR_eq, ηR_inv]

theorem Bη_toCF (x y : E14) : Bη (toCF x) (toCF y) = chimB x y := by
  simp only [Bη, Bmod, chimY, toCF, covec_dotCLM, ηR_eq, ηr_inv, chimB, LinearMap.mk₂_apply]

theorem Bη_bvec (i j : Fin 14) :
    Bη (toCF (chimVec i)) (toCF (chimVec j)) = if i = j then (chimNorms i : ℝ) else 0 := by
  rw [Bη_toCF, chimB_basis]

lemma dotCLM_covec (p : (Fin 4 → ℝ) →L[ℝ] ℝ) : dotCLM (covec p) = p := by
  ext v
  simp only [dotCLM, LinearMap.coe_toContinuousLinearMap', dotProductBilin, dotProduct]
  conv_rhs => rw [pi_eq_sum_univ v, map_sum]
  simp [mul_comm]
  exact Finset.sum_congr rfl fun x _ => by
    rw [covec]; congr 2; ext j; simp [Pi.single_apply, eq_comm]

/-- `toCF` as a linear isomorphism `E14 ≃ CFib`. -/
noncomputable def toCFL : E14 ≃ₗ[ℝ] CFib where
  toFun := toCF
  invFun u := (covec u.2, u.1)
  map_add' x y := by
    simp only [toCF, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    ext v; simp [dotCLM, dotProductBilin, add_dotProduct]
  map_smul' c x := by
    simp only [toCF, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq, true_and]
    ext v; simp [dotCLM, dotProductBilin]
  left_inv x := by simp [toCF, covec_dotCLM]
  right_inv u := by simp [toCF, dotCLM_covec]

/-- Positive directions first, then negative. -/
def σl : Fin 14 → Fin 14 := ![3, 4, 5, 7, 8, 9, 10, 0, 1, 2, 6, 11, 12, 13]

theorem σl_bij : Function.Bijective σl := by decide

noncomputable def σe : Fin 14 ≃ Fin 14 := Equiv.ofBijective σl σl_bij

theorem σ_signs : ∀ i : Fin 14, (0 < chimNorms (σl i) ↔ (i : ℕ) < 7) := by decide

noncomputable def cfac (i : Fin 14) : ℝ := (Real.sqrt |(chimNorms (σl i) : ℝ)|)⁻¹

lemma chimNorms_ne (i : Fin 14) : (chimNorms i : ℝ) ≠ 0 := by
  have : chimNorms i ≠ 0 := (by decide : ∀ k : Fin 14, chimNorms k ≠ 0) i
  exact_mod_cast this

lemma cfac_ne (i : Fin 14) : cfac i ≠ 0 := by
  unfold cfac
  apply inv_ne_zero
  exact Real.sqrt_ne_zero'.mpr (abs_pos.mpr (chimNorms_ne _))

lemma cfac_sq_mul (i : Fin 14) : cfac i * cfac i * (chimNorms (σl i) : ℝ) = if (i : ℕ) < 7 then 1 else -1 := by
  unfold cfac
  rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
  have hs := σ_signs i
  have hn := chimNorms_ne (σl i)
  split_ifs with h
  · have hp : (0 : ℝ) < chimNorms (σl i) := by exact_mod_cast hs.mpr h
    rw [abs_of_pos hp, inv_mul_cancel₀ hn]
  · have hp : ¬ (0 : ℤ) < chimNorms (σl i) := fun h' => h (hs.mp h')
    have hneg : (chimNorms (σl i) : ℝ) < 0 := by
      have : chimNorms (σl i) < 0 := lt_of_le_of_ne (not_lt.mp hp) (by exact_mod_cast hn)
      exact_mod_cast this
    rw [abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hn]

/-- Rescaled, reordered orthonormal basis of `E14`. -/
noncomputable def Bon : Module.Basis (Fin 14) ℝ E14 :=
  (chimVec_basis.reindex σe.symm).isUnitSMul (fun i => (cfac_ne i).isUnit)

lemma Bon_apply (i : Fin 14) : Bon i = cfac i • chimVec (σl i) := by
  simp [Bon, Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply, chimVec_basis, σe]

/-- **Isometry** `(ℝ¹⁴, Q77) → (E14, chimB)`. -/
noncomputable def Ψ : (Fin 14 → ℝ) ≃ₗ[ℝ] E14 := Bon.equivFun.symm

theorem Ψ_isometry (x : Fin 14 → ℝ) : chimB (Ψ x) (Ψ x) = Q77 x := by
  rw [Ψ, Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Bon_apply, smul_eq_mul]
  rw [Q77, QuadraticMap.weightedSumSquares_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [chimB_basis, if_pos rfl, ← cfac_sq_mul]; simp only [smul_eq_mul]; ring
  · intro j _ hji
    have hne : ¬ σl j = σl i := fun h => hji (σl_bij.1 h)
    simp only [chimB_basis, hne, ite_false]; ring
  · simp

/-- **Isometry to the chimeric fiber model**: `Bη (Φ x) (Φ x) = Q77 x`. -/
noncomputable def Φiso : (Fin 14 → ℝ) ≃ₗ[ℝ] CFib := Ψ.trans toCFL

theorem Φiso_isometry (x : Fin 14 → ℝ) : Bη (Φiso x) (Φiso x) = Q77 x := by
  show Bη (toCF (Ψ x)) (toCF (Ψ x)) = Q77 x
  rw [Bη_toCF, Ψ_isometry]

lemma Bη_eq (u v : CFib) : Bη u v = chimB (toCFL.symm u) (toCFL.symm v) := by
  rw [← Bη_toCF]; congr 1 <;> exact (toCFL.apply_symm_apply _).symm

lemma chimB_symm (x y : E14) : chimB x y = chimB y x := by
  simp only [chimB, LinearMap.mk₂_apply]
  rw [trace_mul_comm (ηr * symMat x.2 * ηr) (symMat y.2)]
  have hη : ηrᵀ = ηr := by ext i j; fin_cases i <;> fin_cases j <;> simp [ηr, diagonal]
  rw [dotProduct_mulVec, ← vecMul_transpose, hη, dotProduct_comm]
  simp only [Matrix.mul_assoc]
  rw [show symMat y.2 * (ηr * (symMat x.2 * ηr)) = (symMat y.2 * (ηr * symMat x.2)) * ηr by
    simp only [Matrix.mul_assoc], trace_mul_comm]
  ring

/-- Polarization: preserving the quadratic form preserves the bilinear form. -/
lemma polar (A : CFib ≃ₗ[ℝ] CFib) (hA : ∀ u, Bη (A u) (A u) = Bη u u) (u v : CFib) :
    Bη (A u) (A v) = Bη u v := by
  have key : ∀ x y : CFib, Bη x y = (Bη (x + y) (x + y) - Bη x x - Bη y y) / 2 := by
    intro x y
    simp only [Bη_eq, map_add, LinearMap.add_apply]
    rw [chimB_symm (toCFL.symm y) (toCFL.symm x)]; ring
  rw [key, key u v, ← map_add, hA, hA, hA]

/-- **`Spin(7,7) → O(Bη)`**. -/
noncomputable def spinToOG : Spin77 →* ↥OG where
  toFun x := ⟨(Φiso.symm.trans (vecRep x)).trans Φiso, fun u v => by
    apply polar
    intro w
    show Bη (Φiso (vecRep x (Φiso.symm w))) (Φiso (vecRep x (Φiso.symm w))) = Bη w w
    rw [Φiso_isometry, vecRep_isometry, ← Φiso_isometry, Φiso.apply_symm_apply]⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro w
    show Φiso (vecRep 1 (Φiso.symm w)) = w
    rw [map_one]; simp
  map_mul' x y := by
    apply Subtype.ext; apply LinearEquiv.ext; intro w
    show Φiso (vecRep (x * y) (Φiso.symm w)) = Φiso (vecRep x (Φiso.symm (Φiso (vecRep y (Φiso.symm w)))))
    rw [map_mul, Φiso.symm_apply_apply]; rfl

theorem spinToOG_neg_one : spinToOG ⟨-1, neg_one_mem_spin⟩ = 1 := by
  apply Subtype.ext; apply LinearEquiv.ext; intro w
  show Φiso (vecRep ⟨-1, neg_one_mem_spin⟩ (Φiso.symm w)) = w
  rw [vecRep_neg_one, Φiso.apply_symm_apply]

end GU.Iso77
