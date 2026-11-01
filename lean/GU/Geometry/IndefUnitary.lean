/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import Mathlib

/-!
# The indefinite unitary group `U(p,q)` (roadblock R5)

Mathlib has the indefinite *Lie algebras* (`LieAlgebra.Orthogonal.so'`) but no `U(p,q)` group.
We define `U(J) = {A | Aᴴ J A = J}` and prove it is a group when `J` is the indefinite
diagonal matrix. `H = U(64,64)` is the structure group of the draft's main bundle (3.31).
-/

namespace GU

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrices preserving the Hermitian form `J`: `Aᴴ J A = J`. -/
def indefUnitary (J : Matrix n n ℂ) : Submonoid (Matrix n n ℂ) where
  carrier := {A | Aᴴ * J * A = J}
  one_mem' := by simp
  mul_mem' {A B} hA hB := by
    change Aᴴ * J * A = J at hA
    change Bᴴ * J * B = J at hB
    change (A * B)ᴴ * J * (A * B) = J
    calc (A * B)ᴴ * J * (A * B) = Bᴴ * (Aᴴ * J * A) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hA, hB]

variable {J : Matrix n n ℂ}

lemma indefUnitary_left_inv (hJ : J * J = 1) {A : Matrix n n ℂ} (hA : A ∈ indefUnitary J) :
    J * Aᴴ * J * A = 1 := by
  have hA' : Aᴴ * J * A = J := hA
  calc J * Aᴴ * J * A = J * (Aᴴ * J * A) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA', hJ]

lemma indefUnitary_inv_mem (hJ : J * J = 1) (hJh : Jᴴ = J) {A : Matrix n n ℂ}
    (hA : A ∈ indefUnitary J) : J * Aᴴ * J ∈ indefUnitary J := by
  have hr : A * (J * Aᴴ * J) = 1 := mul_eq_one_comm.mp (indefUnitary_left_inv hJ hA)
  have hAJ : A * J * Aᴴ = J := by
    calc A * J * Aᴴ = A * (J * Aᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]
  show (J * Aᴴ * J)ᴴ * J * (J * Aᴴ * J) = J
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJh]
  calc J * (A * J) * J * (J * Aᴴ * J) = J * (A * J * (J * J) * Aᴴ) * J := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hJ, Matrix.mul_one, hAJ, hJ, Matrix.one_mul]

variable (p q : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- `J_{p,q} = diag(1,…,1,-1,…,-1)`. -/
abbrev Jpq : Matrix (p ⊕ q) (p ⊕ q) ℂ := LieAlgebra.Orthogonal.indefiniteDiagonal p q ℂ

lemma Jpq_mul_self : Jpq p q * Jpq p q = 1 := by
  rw [Jpq, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext (i | i) <;> simp

omit [Fintype p] [Fintype q] in
lemma Jpq_conjTranspose : (Jpq p q)ᴴ = Jpq p q := by
  rw [Jpq, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_conjTranspose]
  congr 1; ext (i | i) <;> simp

/-- `U(p,q)`. -/
abbrev UPQ : Type _ := ↥(indefUnitary (Jpq p q))

instance : Group (UPQ p q) :=
  { (inferInstance : Monoid (UPQ p q)) with
    inv := fun A => ⟨Jpq p q * A.1ᴴ * Jpq p q,
      indefUnitary_inv_mem (Jpq_mul_self p q) (Jpq_conjTranspose p q) A.2⟩
    inv_mul_cancel := fun A => Subtype.ext (indefUnitary_left_inv (Jpq_mul_self p q) A.2) }

/-- The draft's structure group `H = U(64,64)` (3.31). -/
abbrev U6464 := UPQ (Fin 64) (Fin 64)

end GU
