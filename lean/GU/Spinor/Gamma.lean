/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Geometry.Signature

/-!
# Explicit gamma matrices for `Cl(7,7)` (closing roadblock R4, part 1)

We realise `Cl(7,7)` on `ℝ¹²⁸ = (ℝ²)^{⊗7}`. Spinor indices are `Idx = Fin 7 → Fin 2`.
Generator `(k, t)` is the Jordan–Wigner string

  `γ_(k,t) = σ₃ ⊗ ⋯ ⊗ σ₃ ⊗ X_t ⊗ 1 ⊗ ⋯ ⊗ 1`   (`X_t` in slot `k`),

with `X_false = σ₁` (squares to `+1`) and `X_true = ε = [[0,1],[-1,0]]` (squares to `-1`).

The algebra lives in `tprod`, the 7-fold Kronecker product, and the 2×2 tables `F2`. Every
128×128 identity is reduced to a 2×2 table plus a sign count over `Fin 7`, checked by `decide`.

Result: `cliffordRep : Cl77 →ₐ[ℝ] Matrix Idx Idx ℝ`, the real Clifford module of (3.18).
-/

namespace GU.Spinor

open Matrix

/-- Spinor index: `Fin 7 → Fin 2`, so `2⁷ = 128` components. -/
abbrev Idx := Fin 7 → Fin 2

/-- Real 128×128 matrices. -/
abbrev M128 := Matrix Idx Idx ℝ

/-- 7-fold Kronecker product of 2×2 real matrices. -/
def tprod (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) : M128 :=
  Matrix.of fun a b => ∏ j, A j (a j) (b j)

theorem tprod_mul (A B : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) :
    tprod A * tprod B = tprod (fun j => A j * B j) := by
  ext a b
  simp only [tprod, mul_apply, of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

theorem tprod_smul (s : Fin 7 → ℝ) (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) :
    tprod (fun j => s j • A j) = (∏ j, s j) • tprod A := by
  ext a b
  simp [tprod, Finset.prod_mul_distrib]

theorem tprod_one : tprod (fun _ => 1) = 1 := by
  ext a b
  simp only [tprod, of_apply, one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem tprod_transpose (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) :
    (tprod A)ᵀ = tprod (fun j => (A j)ᵀ) := by
  ext a b; rfl

/-- The four 2×2 building blocks. -/
inductive F2
  | one | s3 | s1 | ep
  deriving DecidableEq, Repr

namespace F2

/-- `1`, `σ₃`, `σ₁`, `ε`. -/
def toM : F2 → Matrix (Fin 2) (Fin 2) ℝ
  | one => !![1, 0; 0, 1]
  | s3 => !![1, 0; 0, -1]
  | s1 => !![0, 1; 1, 0]
  | ep => !![0, 1; -1, 0]

/-- Commutation sign: `a b = sgn a b • b a`. -/
def sgn : F2 → F2 → ℤ
  | one, _ => 1
  | _, one => 1
  | a, b => if a = b then 1 else -1

/-- `a² = sq a • 1`. -/
def sq : F2 → ℤ
  | ep => -1
  | _ => 1

/-- `aᵀ = tr a • a`. -/
def tr : F2 → ℤ
  | ep => -1
  | _ => 1

@[simp] theorem toM_one : toM .one = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem comm (a b : F2) : toM a * toM b = (sgn a b : ℝ) • (toM b * toM a) := by
  cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toM, sgn, mul_apply, Fin.sum_univ_two]

theorem square (a : F2) : toM a * toM a = (sq a : ℝ) • 1 := by
  cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toM, sq, mul_apply, Fin.sum_univ_two]

theorem transpose (a : F2) : (toM a)ᵀ = (tr a : ℝ) • toM a := by
  cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [toM, tr]

end F2

/-- Generators of `Cl(7,7)`: slot `k` and type `t` (`false`: `+1`, `true`: `-1`). -/
abbrev Gen := Fin 7 × Bool

/-- The 2×2 block of generator `g` in slot `j`. -/
def sym (g : Gen) (j : Fin 7) : F2 :=
  if j < g.1 then .s3 else if j = g.1 then (if g.2 then .ep else .s1) else .one

/-- `γ_g` as a 128×128 real matrix. -/
def gamma (g : Gen) : M128 := tprod (fun j => F2.toM (sym g j))

theorem gamma_comm (g g' : Gen) :
    gamma g * gamma g' = ((∏ j, F2.sgn (sym g j) (sym g' j) : ℤ) : ℝ) • (gamma g' * gamma g) := by
  rw [gamma, gamma, tprod_mul, tprod_mul, Int.cast_prod, ← tprod_smul]
  congr 1; funext j; exact F2.comm _ _

theorem gamma_sq (g : Gen) : gamma g * gamma g = ((∏ j, F2.sq (sym g j) : ℤ) : ℝ) • 1 := by
  rw [gamma, tprod_mul, Int.cast_prod, ← tprod_one, ← tprod_smul]
  congr 1; funext j; exact F2.square _

/-- Sign count: distinct generators anticommute. -/
theorem sgn_prod_of_ne : ∀ g g' : Gen, g ≠ g' → ∏ j, F2.sgn (sym g j) (sym g' j) = -1 := by
  decide

/-- Sign count: `γ_(k,t)² = +1` for `t = false`, `-1` for `t = true`. -/
theorem sq_prod : ∀ g : Gen, ∏ j, F2.sq (sym g j) = if g.2 then -1 else 1 := by
  decide

/-- Basis index `i : Fin 14` of `ℝ^{7,7}` ↦ generator. `i < 7` are the `+1` directions. -/
def gen (i : Fin 14) : Gen := (⟨i % 7, Nat.mod_lt _ (by norm_num)⟩, decide (7 ≤ (i : ℕ)))

theorem gen_injective : Function.Injective gen := by
  intro i j h; revert i j; decide

/-- Weights of `Q77`. -/
def w (i : Fin 14) : ℝ := if (i : ℕ) < 7 then 1 else -1

/-- `{γ_i, γ_j} = 2 η_ij`. -/
theorem anticomm (i j : Fin 14) :
    gamma (gen i) * gamma (gen j) + gamma (gen j) * gamma (gen i)
      = (if i = j then 2 * w i else 0) • (1 : M128) := by
  by_cases h : i = j
  · subst h
    simp only [gamma_sq, sq_prod, ite_true]
    rw [← two_smul ℝ, smul_smul]
    congr 1
    simp only [gen, w]
    split_ifs <;> simp_all
  · simp only [h, ite_false, zero_smul]
    rw [gamma_comm, sgn_prod_of_ne _ _ (gen_injective.ne h)]
    simp

/-- The Clifford map `v ↦ Σ vᵢ γᵢ`. -/
def gammaMap : (Fin 14 → ℝ) →ₗ[ℝ] M128 where
  toFun v := ∑ i, v i • gamma (gen i)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

theorem gammaMap_sq (v : Fin 14 → ℝ) :
    gammaMap v * gammaMap v = algebraMap ℝ M128 (Q77 v) := by
  set a : Fin 14 → Fin 14 → M128 := fun i j => (v i * v j) • (gamma (gen i) * gamma (gen j))
  have hS : gammaMap v * gammaMap v = ∑ i, ∑ j, a i j := by
    simp only [gammaMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum, a,
      smul_mul_smul_comm]
  have h2 : (2 : ℝ) • ∑ i, ∑ j, a i j = (2 : ℝ) • algebraMap ℝ M128 (Q77 v) := by
    calc (2 : ℝ) • ∑ i, ∑ j, a i j = ∑ i, ∑ j, (a i j + a j i) := by
          rw [two_smul]
          conv_lhs => arg 2; rw [Finset.sum_comm]
          simp only [Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, (v i * v j) • ((if i = j then 2 * w i else 0) • (1 : M128)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← anticomm, smul_add]; simp only [a, mul_comm (v j) (v i)]
      _ = ∑ i, (v i * v i * (2 * w i)) • (1 : M128) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [smul_smul, ite_smul]
      _ = (2 : ℝ) • algebraMap ℝ M128 (Q77 v) := by
          rw [Algebra.algebraMap_eq_smul_one, smul_smul, Q77,
            QuadraticMap.weightedSumSquares_apply, Finset.mul_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [w, smul_eq_mul]
          congr 1; split_ifs <;> ring
  rw [hS]
  exact smul_right_injective M128 (two_ne_zero (α := ℝ)) h2

/-- The real Clifford representation `Cl(7,7) → ℝ(128)` (3.18). -/
def cliffordRep : Cl77 →ₐ[ℝ] M128 := CliffordAlgebra.lift Q77 ⟨gammaMap, gammaMap_sq⟩

@[simp] theorem cliffordRep_ι (v : Fin 14 → ℝ) :
    cliffordRep (CliffordAlgebra.ι Q77 v) = gammaMap v :=
  CliffordAlgebra.lift_ι_apply _ _ _

end GU.Spinor
