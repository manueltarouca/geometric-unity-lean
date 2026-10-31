import GU.Gauge.Inhomogeneous

/-!
# A concrete gauge model: matrix-valued polynomials with `θ(h) = h⁻¹ ∂h`

`GaugeData` is not vacuous. For any commutative ring `R` with a derivation-like map `∂`
(here `Polynomial.derivative`), take `𝓗 = (Matrix n n R[X])ˣ`, `N = Matrix n n R[X]`,
`ad ϖ h = h⁻¹ ϖ h`, `θ h = h⁻¹ (∂h)` (entrywise derivative). The Leibniz rule gives the
cocycle law `θ(ab) = b⁻¹ θ(a) b + θ(b)`, the defining property of a Maurer–Cartan form.

`matrix_no_common_convention`: already for 2×2 real polynomial matrices, no tilted map makes
Lemmas 6.3 and 7.2 hold simultaneously. The footnote-7 sign slip is visible in a genuine
non-abelian gauge model, not just in U(1).
-/

namespace GU.MatrixModel

open Polynomial Matrix

variable (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- Entrywise derivative. -/
noncomputable def dM (A : Matrix n n R[X]) : Matrix n n R[X] := A.map derivative

omit [DecidableEq n] in
lemma dM_mul (A B : Matrix n n R[X]) : dM n R (A * B) = dM n R A * B + A * dM n R B := by
  ext i j
  simp only [dM, map_apply, mul_apply, Matrix.add_apply, derivative_sum, derivative_mul,
    Finset.sum_add_distrib]

omit [Fintype n] in
lemma dM_one : dM n R 1 = 0 := by
  ext i j; simp [dM, one_apply]; split_ifs <;> simp

/-- The gauge data. -/
noncomputable def gaugeData : GaugeData (Matrix n n R[X])ˣ (Matrix n n R[X]) where
  ad ϖ h := (h⁻¹ : (Matrix n n R[X])ˣ).1 * ϖ * h.1
  ad_one _ := by simp
  ad_mul ϖ a b := by
    simp only [_root_.mul_inv_rev, Units.val_mul]; simp only [Matrix.mul_assoc]
  ad_add _ _ _ := by simp [Matrix.mul_add, Matrix.add_mul]
  θ h := (h⁻¹ : (Matrix n n R[X])ˣ).1 * dM n R h.1
  θ_mul a b := by
    simp only [_root_.mul_inv_rev, Units.val_mul, dM_mul, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc (a⁻¹ : (Matrix n n R[X])ˣ).1 a.1, Units.inv_mul, Matrix.one_mul]

/-- The unipotent gauge transformation `h = [[1, X], [0, 1]]`. -/
noncomputable def hX : (Matrix (Fin 2) (Fin 2) ℝ[X])ˣ where
  val := !![1, X; 0, 1]
  inv := !![1, -X; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

lemma hX_inv_val : ((hX⁻¹ : (Matrix (Fin 2) (Fin 2) ℝ[X])ˣ) : Matrix (Fin 2) (Fin 2) ℝ[X])
    = !![1, -X; 0, 1] := rfl

lemma θ_hX : (gaugeData (Fin 2) ℝ).θ hX = !![0, 1; 0, 0] := by
  show (hX⁻¹ : (Matrix (Fin 2) (Fin 2) ℝ[X])ˣ).1 * dM (Fin 2) ℝ hX.1 = _
  rw [hX_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hX, dM, mul_apply, Fin.sum_univ_two]

theorem matrix_no_common_convention :
    ¬ ∃ s : (Matrix (Fin 2) (Fin 2) ℝ[X])ˣ → Matrix (Fin 2) (Fin 2) ℝ[X],
      (∀ h, (gaugeData (Fin 2) ℝ).pi (⟨h, s h⟩ : IG (gaugeData (Fin 2) ℝ)) = (gaugeData (Fin 2) ℝ).pi 1) ∧
      (∀ h, (gaugeData (Fin 2) ℝ).T (⟨h, s h⟩ : IG (gaugeData (Fin 2) ℝ)) =
        (gaugeData (Fin 2) ℝ).ad ((gaugeData (Fin 2) ℝ).T 1) h) := by
  rintro ⟨s, hπ, hT⟩
  have := (gaugeData (Fin 2) ℝ).no_common_section s hπ hT hX
  rw [θ_hX] at this
  have h01 := congrFun (congrFun this 0) 1
  simp at h01

end GU.MatrixModel
