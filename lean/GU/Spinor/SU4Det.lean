import Mathlib
import GU.Spinor.Lambda2

/-!
# Track 1, S4: `det T_U = 1`

* `unitary_sqrt`: every unitary `4 × 4` matrix has a unitary square root, via the continuous
  functional calculus with `z ↦ z^{1/2}` on the finite spectrum.
* `det_sq_of_isometry`: an isometry of `(ℝ⁶, Q₆)` has `det² = 1`.
* **`det_TUL`**: for `U ∈ SU(4)`, `det T_U = 1`. Write `U = V²`. If `det V = 1`, then
  `T_U = T_V²`. If `det V = −1`, then `ζV ∈ SU(4)` with `ζ = (1+i)/√2`, `(ζV)² = iU`, and
  `T_{iU} = −T_U`, so `det T_U = det(−T_{ζV}²) = (det T_{ζV})² = 1` (the space is 6-dimensional).
-/

namespace GU.Spinor

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **Unitary square roots** of unitary `4 × 4` matrices. -/
theorem unitary_sqrt (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : U ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ)) :
    ∃ V ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ), V * V = U := by
  have hn : IsStarNormal U := ⟨by
    have := (Unitary.mem_iff.mp hU); show star U * U = U * star U; rw [this.1, this.2]⟩
  let f : ℂ → ℂ := fun z => z ^ (2⁻¹ : ℂ)
  have hfin : (spectrum ℂ U).Finite := Matrix.finite_spectrum U
  have hcont : ContinuousOn f (spectrum ℂ U) := hfin.continuousOn _
  refine ⟨cfc f U, ?_, ?_⟩
  · have hcirc : ∀ z ∈ spectrum ℂ U, ‖z‖ = 1 := fun z hz => by
      have := Unitary.spectrum_subset_circle ⟨U, hU⟩ hz
      simpa using this
    have hf1 : ∀ z ∈ spectrum ℂ U, star (f z) * f z = 1 := fun z hz => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have : ‖f z‖ = 1 := by
        have hsq : f z ^ 2 = z := Complex.cpow_nat_inv_pow z (by norm_num)
        have h2 : ‖f z‖ ^ 2 = 1 := by rw [← norm_pow, hsq, hcirc z hz]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h2
      rw [this]; norm_num
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · rw [← cfc_star, ← cfc_mul _ _ U, ← cfc_one ℂ U]
      exact cfc_congr fun z hz => hf1 z hz
    · rw [← cfc_star, ← cfc_mul _ _ U, ← cfc_one ℂ U]
      exact cfc_congr fun z hz => by rw [mul_comm]; exact hf1 z hz
  · rw [← cfc_mul f f U]
    conv_rhs => rw [← cfc_id' ℂ U]
    refine cfc_congr fun z _ => ?_
    simp only [f, ← pow_two]
    exact Complex.cpow_nat_inv_pow z (by norm_num)

/-- An isometry of `(ℝ⁶, Q₆)` has `det² = 1`. -/
theorem det_sq_of_isometry (T : Module.End ℝ (Fin 6 → ℝ)) (hT : ∀ v, Q6 (T v) = Q6 v) :
    LinearMap.det T * LinearMap.det T = 1 := by
  set M := LinearMap.toMatrix' T
  have hdot : ∀ v w : Fin 6 → ℝ, (T v) ⬝ᵥ (T w) = v ⬝ᵥ w := fun v w => by
    have hq : ∀ u : Fin 6 → ℝ, Q6 u = u ⬝ᵥ u := fun u => by
      rw [Q6_apply]; simp [dotProduct, sq]
    have h1 := hT (v + w)
    rw [map_add, hq, hq] at h1
    have h2 := hT v; have h3 := hT w
    rw [hq, hq] at h2 h3
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm (T w) (T v), dotProduct_comm w v] at h1
    linarith
  have hMM : Mᵀ * M = 1 := by
    refine Matrix.ext fun i j => ?_
    have := hdot (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, LinearMap.toMatrix'_apply, Matrix.one_apply]
    rw [show (∑ k, T (Pi.single i 1) k * T (Pi.single j 1) k) = T (Pi.single i 1) ⬝ᵥ T (Pi.single j 1)
      from rfl, this]
    simp [dotProduct, Pi.single_apply, eq_comm]
  have := congrArg Matrix.det hMM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, LinearMap.det_toMatrix'] at this
  exact this

lemma TUL_mul_of {U V W : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ)
    (hV : V ∈ specialUnitaryGroup (Fin 4) ℂ) (hW : W ∈ specialUnitaryGroup (Fin 4) ℂ) (h : V * W = U) :
    TUL hU = TUL hV * TUL hW := by
  refine LinearMap.ext fun v => ?_
  show TU U v = TU V (TU W v)
  rw [← TU_mul hV hW, h]

lemma TU_I {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ)
    (hIU : Complex.I • U ∈ specialUnitaryGroup (Fin 4) ℂ) (v : Fin 6 → ℝ) :
    TU (Complex.I • U) v = -TU U v := by
  apply σK_injective
  rw [σK_TU hIU, show σM (-TU U v) = -σM (TU U v) from σM_neg _, Matrix.neg_mul, σK_TU hU]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Complex.I_mul_I, neg_one_smul]

lemma det_isometry_sq {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ) :
    LinearMap.det (TUL hU) * LinearMap.det (TUL hU) = 1 :=
  det_sq_of_isometry _ (TU_isometry hU)

/-- **S4: `det T_U = 1`** for `U ∈ SU(4)`. -/
theorem det_TUL {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ) :
    LinearMap.det (TUL hU) = 1 := by
  obtain ⟨hu, hdetU⟩ := mem_specialUnitaryGroup_iff.mp hU
  obtain ⟨V, hVu, hVV⟩ := unitary_sqrt U hu
  have hdV : V.det * V.det = 1 := by rw [← Matrix.det_mul, hVV]; exact hdetU
  rcases mul_self_eq_one_iff.mp hdV with h1 | h1
  · have hV : V ∈ specialUnitaryGroup (Fin 4) ℂ := mem_specialUnitaryGroup_iff.mpr ⟨hVu, h1⟩
    rw [TUL_mul_of hU hV hV hVV, map_mul]
    exact det_isometry_sq hV
  · -- `ζ = (1 + i)/√2`, `ζ² = i`, `ζ⁴ = −1`
    set ζ : ℂ := (1 + Complex.I) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : Real.sqrt 2 ≠ 0 := by positivity
    have hζ2 : ζ * ζ = Complex.I := by
      apply Complex.ext <;> simp [ζ] <;> field_simp <;> nlinarith [hs]
    have hζn : star ζ * ζ = 1 := by
      apply Complex.ext <;> simp [ζ] <;> field_simp <;> nlinarith [hs]
    have hIu : Complex.I • U ∈ specialUnitaryGroup (Fin 4) ℂ := by
      refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
      · rw [mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          (mem_unitaryGroup_iff.mp hu)]
        simp [Complex.star_def, Complex.conj_I]
      · rw [Matrix.det_smul, hdetU]; simp [Fintype.card_fin]
    have hV' : ζ • V ∈ specialUnitaryGroup (Fin 4) ℂ := by
      refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
      · rw [mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          mem_unitaryGroup_iff.mp hVu, mul_comm, hζn, one_smul]
      · rw [Matrix.det_smul, h1, Fintype.card_fin,
          show ζ ^ 4 = (ζ * ζ) * (ζ * ζ) by ring, hζ2, Complex.I_mul_I]
        norm_num
    have hsq : (ζ • V) * (ζ • V) = Complex.I • U := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hζ2, hVV]
    have hneg : TUL hU = -TUL hIu := LinearMap.ext fun v => by
      show TU U v = -TU (Complex.I • U) v
      rw [TU_I hU hIu, neg_neg]
    rw [hneg, TUL_mul_of hIu hV' hV' hsq, show -(TUL hV' * TUL hV') = (-1 : ℝ) • (TUL hV' * TUL hV')
      from (neg_one_smul ℝ _).symm, LinearMap.det_smul, map_mul, det_isometry_sq hV',
      Module.finrank_fin_fun]
    norm_num

end GU.Spinor
