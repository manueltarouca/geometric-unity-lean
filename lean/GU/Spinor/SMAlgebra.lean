import GU.Spinor.HyperchargeOp
import GU.synthetic_predictions

/-!
# Standard Model algebra checks inside `Spin(6,4)`

* `Y_commutes_sm`: the hypercharge operator `Ŷ` commutes with every generator of
  `u(3) ⊕ u(2)` (`smPart`). Hypercharge is a colour and weak-isospin singlet, as it must be.
* `weinberg_angle`: over one generation (the 16 odd weights),
  `Tr(T₃²) / Tr(Q²) = 3/8`. This is the classic unification-scale value of `sin²θ_W` for
  matter in a `Spin(10)`-type 16, which the (6,4) block inherits.
-/

namespace GU.Spinor

open Matrix Complex CSum GU.Predictions

lemma toC_sub (A B : M128) : toC (A - B) = toC A - toC B := by ext i j; simp [toC]

lemma toMat_flatMap_planes (L : List (Gen × Gen)) :
    toMat (L.flatMap fun p => biv p.1 p.2) = (L.map fun p => (gammaP p.1 * gammaP p.2).toMat).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [biv] at ih
    simp only [List.flatMap_cons, toMat_append, biv, toMat_cons, toMat_nil, add_zero, ih,
      List.map_cons, List.sum_cons]

lemma Jpos_toC : toC (toMat Jpos) = πC 0 + πC 1 + πC 2 := by
  rw [Jpos, toMat_flatMap_planes]
  simp [planes, πC, planeOp, toC, add_assoc]
  ext i j; simp [Matrix.add_apply]

lemma Jneg_toC : toC (toMat Jneg) = πC 3 + πC 4 := by
  rw [Jneg, toMat_flatMap_planes]
  simp [planes, πC, planeOp, toC]
  ext i j; simp [Matrix.add_apply]

lemma toC_add (A B : M128) : toC (A + B) = toC A + toC B := by ext i j; simp [toC]

lemma commutes_of_isZero {X Y : CSum} (h : isZero (comm X Y) = true) :
    toC (toMat X) * toC (toMat Y) = toC (toMat Y) * toC (toMat X) := by
  have := toMat_eq_zero h
  rw [toMat_comm, sub_eq_zero] at this
  rw [← toC_mul, ← toC_mul, this]

theorem Y_commutes_sm : ∀ X ∈ smPart, Yop * toC (toMat X) = toC (toMat X) * Yop := by
  intro X hX
  have h := List.all_eq_true.mp center_two_u1.1 X hX
  simp only [Bool.and_eq_true] at h
  have h1 := commutes_of_isZero h.1
  have h2 := commutes_of_isZero h.2
  rw [Jpos_toC] at h1; rw [Jneg_toC] at h2
  rw [Yop, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, h1, h2]

/-- `12 T₃ᴸ = 3(s₃ − s₄)`. -/
def twelveT3 (s : Fin 5 → Bool) : ℤ := 3 * (sgn (s 3) - sgn (s 4))

/-- **`sin²θ_W = 3/8`**: `8 Σ (12T₃)² = 3 Σ (12Q)²` over one generation. -/
theorem weinberg_angle :
    8 * ((oddWeights.map fun s => twelveT3 s ^ 2).sum) = 3 * ((oddWeights.map fun s => twelveQ s ^ 2).sum) := by
  decide

/-- Consistency: `Q = T₃ + Y` is exactly the definition of `twelveQ`. -/
theorem Q_eq : ∀ s, twelveQ s = twelveT3 s + twelveY s := by
  intro s; simp [twelveQ, twelveT3]; ring

end GU.Spinor
