import GU.Spinor.Dirac

/-!
# The draft's `U(64,64)` is the standard `U(64,64)`

`rhoD` lands in `UC`, the unitary group of the spinor form `C` of (3.24). Here we prove
`UC ≃* U6464 = U(diag(1⁶⁴, -1⁶⁴))`, so `ρ_D` becomes a homomorphism into the standard group.

Construction: `D = σ₃ ⊗ 1 ⊗ ⋯ ⊗ 1` is diagonal with entries `±1`, split by the first spinor bit.
`C` and `D` anticommute, so `P = (1 + C D)/√2` satisfies `Pᵀ P = 1` and `Pᵀ C P = D`.
Every step follows from `C² = D² = 1`, `Cᵀ = C`, `Dᵀ = D` and `C D = -D C`.
Reindexing `D` along `Idx ≃ Fin 64 ⊕ Fin 64` gives `J_{64,64}`.
-/

namespace GU.Spinor

open Matrix

/-! ### Diagonal tensor products -/

theorem tprod_diagonal (d : Fin 7 → Fin 2 → ℝ) :
    tprod (fun j => diagonal (d j)) = diagonal (fun a => ∏ j, d j (a j)) := by
  ext a b
  simp only [tprod, of_apply, diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- `±1` according to the first spinor bit. -/
def lam (a : Idx) : ℝ := if a 0 = 0 then 1 else -1

/-- `D = diag(lam)`. -/
def D : M128 := diagonal lam

/-- Slot pattern of `D`: `σ₃` in slot 0, identity elsewhere. -/
def dsym (j : Fin 7) : F2 := if j = 0 then .s3 else .one

theorem D_eq_tprod : D = tprod (fun j => F2.toM (dsym j)) := by
  have h : ∀ j, F2.toM (dsym j) = diagonal (fun x => if j = 0 ∧ x = 1 then -1 else 1) := by
    intro j
    by_cases hj : j = 0 <;> ext x y <;> fin_cases x <;> fin_cases y <;>
      simp [dsym, hj, F2.toM]
  simp_rw [h]
  rw [tprod_diagonal, D]
  congr 1; funext a
  rw [Fin.prod_univ_succ]
  simp only [lam, Fin.succ_ne_zero, false_and, ite_false, Finset.prod_const_one, mul_one, true_and]
  generalize a 0 = x
  fin_cases x <;> simp

theorem C_D : C * D = -(D * C) := by
  have hs : ∏ j, F2.sgn (csym j) (dsym j) = -1 := by decide
  rw [C, D_eq_tprod, tprod_mul, tprod_mul]
  simp_rw [F2.comm (csym _)]
  rw [tprod_smul, ← Int.cast_prod, hs]
  simp

theorem D_mul_D : D * D = 1 := by
  rw [D, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; simp only [lam]; split_ifs <;> norm_num

theorem D_transpose : Dᵀ = D := diagonal_transpose _

/-- `P = (1 + C D)/√2`. -/
noncomputable def P : M128 := (Real.sqrt 2)⁻¹ • (1 + C * D)

lemma half : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]

lemma P_transpose : Pᵀ = (Real.sqrt 2)⁻¹ • (1 + D * C) := by
  rw [P, transpose_smul, transpose_add, transpose_one, transpose_mul, C_transpose, D_transpose]

/-- `C D` squares to `-1`. -/
lemma CD_sq : C * D * (C * D) = -1 := by
  calc C * D * (C * D) = C * (D * C) * D := by simp only [Matrix.mul_assoc]
    _ = -1 := by
      rw [show D * C = -(C * D) by rw [C_D, neg_neg], Matrix.mul_neg, Matrix.neg_mul,
        ← Matrix.mul_assoc, C_mul_C, Matrix.one_mul, D_mul_D]

theorem PtP : Pᵀ * P = 1 := by
  rw [P_transpose, P, Matrix.smul_mul, Matrix.mul_smul, smul_smul, half]
  have : (1 + D * C) * (1 + C * D) = 2 • (1 : M128) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    rw [show D * C * (C * D) = 1 by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, C_mul_C, Matrix.one_mul, D_mul_D],
      show D * C = -(C * D) by rw [C_D, neg_neg]]
    rw [two_smul]; abel
  rw [this, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; norm_num

theorem PtCP : Pᵀ * C * P = D := by
  rw [P_transpose, P, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, half]
  have : (1 + D * C) * C * (1 + C * D) = 2 • D := by
    have hDC : D * C = -(C * D) := by rw [C_D, neg_neg]
    have hDCC : D * C * C = D := by rw [Matrix.mul_assoc, C_mul_C, Matrix.mul_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hDCC]
    have hDCD : D * (C * D) = -C := by
      rw [← Matrix.mul_assoc, hDC, Matrix.neg_mul, Matrix.mul_assoc, D_mul_D, Matrix.mul_one]
    have hCCD : C * (C * D) = D := by rw [← Matrix.mul_assoc, C_mul_C, Matrix.one_mul]
    rw [hDCD]
    rw [hCCD]
    rw [two_smul]; abel
  rw [this, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; norm_num

theorem PPt : P * Pᵀ = 1 := mul_eq_one_comm.mp PtP

/-! ### Transport of unitary groups -/

section Transport

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma conj_mem {J₁ J₂ Q : Matrix n n ℂ} (hQ : Q * Qᴴ = 1) (hJ : Qᴴ * J₁ * Q = J₂)
    {A : Matrix n n ℂ} (hA : A ∈ indefUnitary J₁) : Qᴴ * A * Q ∈ indefUnitary J₂ := by
  have hA' : Aᴴ * J₁ * A = J₁ := hA
  have hJ' : Q * J₂ * Qᴴ = J₁ := by
    rw [← hJ]; simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
  show (Qᴴ * A * Q)ᴴ * J₂ * (Qᴴ * A * Q) = J₂
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  calc _ = Qᴴ * (Aᴴ * (Q * J₂ * Qᴴ) * A) * Q := by
        simp only [Matrix.mul_assoc]
    _ = J₂ := by rw [hJ', hA', hJ]

/-- Conjugation by a unitary `Q` with `Qᴴ J₁ Q = J₂` identifies `U(J₁)` with `U(J₂)`. -/
def conjEquiv {J₁ J₂ Q : Matrix n n ℂ} (hQ : Qᴴ * Q = 1) (hJ : Qᴴ * J₁ * Q = J₂) :
    indefUnitary J₁ ≃* indefUnitary J₂ where
  toFun A := ⟨Qᴴ * A.1 * Q, conj_mem (mul_eq_one_comm.mp hQ) hJ A.2⟩
  invFun B := ⟨Q * B.1 * Qᴴ, by
    have h1 : Qᴴᴴ * Qᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hQ
    have h2 : Qᴴᴴ * J₂ * Qᴴ = J₁ := by
      rw [conjTranspose_conjTranspose, ← hJ]
      have hQ' := mul_eq_one_comm.mp hQ
      simp only [← Matrix.mul_assoc, hQ', Matrix.one_mul]
      rw [Matrix.mul_assoc, hQ', Matrix.mul_one]
    simpa using conj_mem (Q := Qᴴ) (by rw [conjTranspose_conjTranspose]; exact hQ) h2 B.2⟩
  left_inv A := Subtype.ext (by
    have hQ' := mul_eq_one_comm.mp hQ
    simp only [← Matrix.mul_assoc, hQ', Matrix.one_mul]
    rw [Matrix.mul_assoc, hQ', Matrix.mul_one])
  right_inv B := Subtype.ext (by
    simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQ, Matrix.mul_one])
  map_mul' A B := Subtype.ext (by
    show Qᴴ * (A.1 * B.1) * Q = Qᴴ * A.1 * Q * (Qᴴ * B.1 * Q)
    have hQ' := mul_eq_one_comm.mp hQ
    calc Qᴴ * (A.1 * B.1) * Q = Qᴴ * A.1 * (Q * Qᴴ) * B.1 * Q := by
          rw [hQ', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

omit [DecidableEq n] [DecidableEq m] in
lemma reindex_mul' (e : n ≃ m) (A B : Matrix n n ℂ) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  simp

lemma reindex_mem (e : n ≃ m) {J A : Matrix n n ℂ} (hA : A ∈ indefUnitary J) :
    reindex e e A ∈ indefUnitary (reindex e e J) := by
  have hA' : Aᴴ * J * A = J := hA
  show (reindex e e A)ᴴ * reindex e e J * reindex e e A = reindex e e J
  rw [conjTranspose_reindex, ← reindex_mul', ← reindex_mul', hA']

/-- Reindexing identifies `U(J)` with `U(reindex e e J)`. -/
def reindexEquiv (e : n ≃ m) (J : Matrix n n ℂ) :
    indefUnitary J ≃* indefUnitary (reindex e e J) where
  toFun A := ⟨reindex e e A.1, reindex_mem e A.2⟩
  invFun B := ⟨reindex e.symm e.symm B.1, by
    have := reindex_mem e.symm B.2
    rwa [show reindex e.symm e.symm (reindex e e J) = J by ext; simp [reindex_apply]] at this⟩
  left_inv A := Subtype.ext (by ext; simp [reindex_apply])
  right_inv B := Subtype.ext (by ext; simp [reindex_apply])
  map_mul' A B := Subtype.ext (reindex_mul' e A.1 B.1)

end Transport

/-! ### Assembling `UC ≃* U(64,64)` -/

/-- Half of the spinor indices have first bit `0`: the split is 64 + 64. -/
theorem card_split : Fintype.card {a : Idx // a 0 = 0} = 64 := by decide
theorem card_split' : Fintype.card {a : Idx // ¬ a 0 = 0} = 64 := by decide

/-- Spinors whose first bit is `0` (chirality `+` of slot 0). -/
noncomputable def splitL : {a : Idx // a 0 = 0} ≃ Fin 64 := Fintype.equivFinOfCardEq card_split

/-- Spinors whose first bit is `1`. -/
noncomputable def splitR : {a : Idx // ¬ a 0 = 0} ≃ Fin 64 := Fintype.equivFinOfCardEq card_split'

/-- `Idx ≃ Fin 64 ⊕ Fin 64`, by the first spinor bit (`0 ↦ inl`). -/
noncomputable def splitIdx : Idx ≃ Fin 64 ⊕ Fin 64 :=
  (Equiv.sumCompl (fun a : Idx => a 0 = 0)).symm.trans (Equiv.sumCongr splitL splitR)

lemma splitIdx_symm_inl (i : Fin 64) : splitIdx.symm (Sum.inl i) = (splitL.symm i).1 := rfl
lemma splitIdx_symm_inr (i : Fin 64) : splitIdx.symm (Sum.inr i) = (splitR.symm i).1 := rfl

theorem reindex_D : reindex splitIdx splitIdx (toC D) = Jpq (Fin 64) (Fin 64) := by
  have hD : toC D = diagonal (fun a => ((lam a : ℝ) : ℂ)) := by
    ext a b; simp only [toC, D, map_apply, diagonal_apply]; split_ifs <;> simp
  have hL : ∀ i j : Fin 64, (splitL.symm i).1 = (splitL.symm j).1 ↔ i = j := fun i j =>
    Subtype.val_injective.eq_iff.trans splitL.symm.injective.eq_iff
  have hR : ∀ i j : Fin 64, (splitR.symm i).1 = (splitR.symm j).1 ↔ i = j := fun i j =>
    Subtype.val_injective.eq_iff.trans splitR.symm.injective.eq_iff
  rw [hD]
  ext (i | i) (j | j) <;>
    simp only [reindex_apply, submatrix_apply, splitIdx_symm_inl, splitIdx_symm_inr,
      diagonal_apply, Jpq, LieAlgebra.Orthogonal.indefiniteDiagonal, Sum.inl.injEq,
      Sum.inr.injEq, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false]
  · simp only [hL]; split_ifs <;> simp [lam, (splitL.symm i).2]
  · refine ite_eq_right_iff.mpr fun h => absurd (h ▸ (splitL.symm i).2) (splitR.symm j).2
  · refine ite_eq_right_iff.mpr fun h => absurd (h ▸ (splitR.symm i).2) ?_
    exact fun h' => h' ((splitL.symm j).2)
  · simp only [hR]; split_ifs <;> simp [lam, (splitR.symm i).2]

/-- Complexified `P` is unitary and carries `C` to `D`. -/
lemma PcHPc : (toC P)ᴴ * toC P = 1 := by
  rw [toC_conjTranspose, ← toC_mul, PtP, toC, Matrix.map_one] <;> simp

lemma PcHCPc : (toC P)ᴴ * Cc * toC P = toC D := by
  rw [toC_conjTranspose, Cc, ← toC_mul, ← toC_mul, PtCP]

/-- The draft's `U(64,64)` (unitary group of `C`) is the standard `U(64,64)`. -/
noncomputable def UC_equiv_U6464 : UC ≃* U6464 :=
  (conjEquiv PcHPc PcHCPc).trans
    ((reindexEquiv splitIdx (toC D)).trans (MulEquiv.submonoidCongr (congrArg _ reindex_D)))

end GU.Spinor
