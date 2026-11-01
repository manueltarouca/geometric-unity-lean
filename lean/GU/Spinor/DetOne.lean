/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Basis

/-!
# `ρ_D(Spin(7,7)) ⊂ SO(64,64)`: the determinant is 1 (draft (3.30))

`Γ = σ₃^{⊗7}` is diagonal, with sign given by the parity of the spinor index (`Γ_apply`).
* `ρ(x)` commutes with `Γ`, so it is block-diagonal `(ρ_L, ρ_R)` in the parity splitting:
  `GL(64) × GL(64)` of (3.25).
* `C` anticommutes with `Γ`, so it is block-off-diagonal `[[0, B], [B', 0]]`, and `C² = 1`
  gives `B B' = 1`.
* `ρᵀ C ρ = C` gives `ρ_Lᵀ B ρ_R = B`, hence `det ρ_L · det ρ_R = 1` and `det ρ(x) = 1`
  (`det_rho_eq_one`). This is the SO(64,64) step of (3.30); `det ρ_L = 1` (the SL(64,ℝ) step) is
  not proved.
-/

namespace GU.Spinor

open Matrix

/-- Even parity of a spinor index (Boolean). -/
def evb (a : Idx) : Bool := ((List.finRange 7).countP fun j => a j == 1) % 2 == 0

/-- Even parity of a spinor index. -/
def ev (a : Idx) : Prop := evb a = true

instance : DecidablePred ev := fun a => inferInstanceAs (Decidable (evb a = true))

set_option maxRecDepth 20000 in
lemma prod_sign_b : ∀ a : Idx, (∏ j, ((![1, -1] : Fin 2 → ℤ) (a j))) = if evb a then 1 else -1 := by
  decide

lemma prod_sign (a : Idx) :
    (∏ j, ((![1, -1] : Fin 2 → ℤ) (a j))) = if ev a then 1 else -1 := prod_sign_b a

lemma Γ_apply (a b : Idx) : Γ a b = if a = b then (if ev a then 1 else -1) else 0 := by
  have h : (fun _ : Fin 7 => F2.toM .s3) = fun _ => diagonal ((![1, -1] : Fin 2 → ℤ) · : Fin 2 → ℝ) := by
    funext j; ext x y; fin_cases x <;> fin_cases y <;> simp [F2.toM]
  rw [Γ, h, tprod_diagonal, diagonal_apply]
  split_ifs <;> simp_all [← Int.cast_prod, prod_sign]

lemma Γ_diag_ne {a b : Idx} (h : ¬ (ev a ↔ ev b)) : Γ a a - Γ b b ≠ 0 := by
  rw [Γ_apply, Γ_apply]; by_cases ha : ev a <;> by_cases hb : ev b <;> simp_all
  all_goals norm_num

lemma entry_zero_of_commute (M : M128) (hM : Γ * M = M * Γ) {a b : Idx} (h : ¬ (ev a ↔ ev b)) :
    M a b = 0 := by
  have e := congrFun (congrFun hM a) b
  have hΓ : ∀ x y : Idx, x ≠ y → Γ x y = 0 := fun x y hxy => by rw [Γ_apply]; simp [hxy]
  rw [mul_apply, mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hΓ a c (Ne.symm hc), zero_mul])
    (by simp), Finset.sum_eq_single b (fun c _ hc => by rw [hΓ c b hc, mul_zero]) (by simp)] at e
  have : M a b * (Γ a a - Γ b b) = 0 := by linear_combination e
  exact (mul_eq_zero.mp this).resolve_right (Γ_diag_ne h)

lemma entry_zero_of_anticommute (M : M128) (hM : M * Γ = -(Γ * M)) {a b : Idx} (h : ev a ↔ ev b) :
    M a b = 0 := by
  have e := congrFun (congrFun hM a) b
  have hΓ : ∀ x y : Idx, x ≠ y → Γ x y = 0 := fun x y hxy => by rw [Γ_apply]; simp [hxy]
  rw [neg_apply, mul_apply, mul_apply, Finset.sum_eq_single b (fun c _ hc => by rw [hΓ c b hc, mul_zero])
    (by simp), Finset.sum_eq_single a (fun c _ hc => by rw [hΓ a c (Ne.symm hc), zero_mul]) (by simp)] at e
  have hab : Γ a a = Γ b b := by rw [Γ_apply, Γ_apply]; simp [h]
  rw [hab] at e
  have h2 : Γ b b ≠ 0 := by rw [Γ_apply]; by_cases hb : ev b <;> simp [hb]
  have : M a b * (2 * Γ b b) = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd h0 (mul_ne_zero two_ne_zero h2)

/-- Parity splitting `Idx ≃ L ⊕ R`. -/
abbrev par : Idx ≃ {a // ev a} ⊕ {a // ¬ ev a} := (Equiv.sumCompl ev).symm

lemma reindexR_mul (A B : M128) : reindex par par (A * B) = reindex par par A * reindex par par B := by
  simp

theorem det_rho_eq_one (x : Spin77) : (cliffordRep x).det = 1 := by
  set ρ := cliffordRep x
  have hcomm : Γ * ρ = ρ * Γ := spin_commutes_Γ x
  have hpres : ρᵀ * C * ρ = C := spin_preserves_C x
  set ρ' := reindex par par ρ
  set C' := reindex par par C
  have hρ : ρ' = fromBlocks ρ'.toBlocks₁₁ 0 0 ρ'.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks ρ']
    congr 1
    · ext i j; exact entry_zero_of_commute ρ hcomm (by simp [i.2, j.2])
    · ext i j; exact entry_zero_of_commute ρ hcomm (by simp [i.2, j.2])
  have hC : C' = fromBlocks 0 C'.toBlocks₁₂ C'.toBlocks₂₁ 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks C']
    congr 1
    · ext i j; exact entry_zero_of_anticommute C C_Γ (by simp [i.2, j.2])
    · ext i j; exact entry_zero_of_anticommute C C_Γ (by simp [i.2, j.2])
  set A := ρ'.toBlocks₁₁; set D := ρ'.toBlocks₂₂
  set B := C'.toBlocks₁₂; set B' := C'.toBlocks₂₁
  have hdet : ρ.det = A.det * D.det := by
    rw [← det_reindex_self par ρ, show reindex par par ρ = ρ' from rfl, hρ, det_fromBlocks_zero₂₁]
  -- C'² = 1 gives B B' = 1
  have hCC : C' * C' = 1 := by rw [← reindexR_mul, C_mul_C]; ext i j; simp [reindex_apply, one_apply]
  rw [hC, fromBlocks_multiply] at hCC
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hCC
  have hBB : B * B' = 1 := by
    have := congrArg toBlocks₁₁ hCC
    simpa [toBlocks_fromBlocks₁₁, ← fromBlocks_one] using this
  have hB'B : B' * B = 1 := by
    have := congrArg toBlocks₂₂ hCC
    simpa [toBlocks_fromBlocks₂₂, ← fromBlocks_one] using this
  -- ρ'ᵀ C' ρ' = C'
  have hP : ρ'ᵀ * C' * ρ' = C' := by
    show (reindex par par ρ)ᵀ * reindex par par C * reindex par par ρ = reindex par par C
    rw [show (reindex par par ρ)ᵀ = reindex par par ρᵀ by ext i j; rfl, ← reindexR_mul,
      ← reindexR_mul, hpres]
  rw [hρ, hC, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hP
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, transpose_zero] at hP
  have h12 : A.transpose * B * D = B := by
    have := congrArg toBlocks₁₂ hP
    simpa [toBlocks_fromBlocks₁₂] using this
  have h1 : A.det * D.det = 1 := by
    have e : Aᵀ * (B * D * B') = 1 := by
      calc Aᵀ * (B * D * B') = Aᵀ * B * D * B' := by simp only [Matrix.mul_assoc]
        _ = B * B' := by rw [h12]
        _ = 1 := hBB
    have := congrArg det e
    rw [det_mul, det_transpose, det_conj_of_mul_eq_one hBB hB'B, det_one] at this
    exact this
  rw [hdet, h1]

end GU.Spinor
