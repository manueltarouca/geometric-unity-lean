import GU.Spinor.WeightSpaces

/-!
# Hypercharge as an operator on `S̸(Y)`

`π_k` acts on the weight space `range P_s` by `−i s_k` (`πC_on_weight`). Hence the operators

  `Ŷ = (i/12)(−2(π₀+π₁+π₂) + 3(π₃+π₄))`,  `Q̂ = Ŷ + (i/4)(π₃ − π₄)`

built from the central generators `J₊ = π₀+π₁+π₂` and `J₋ = π₃+π₄` of `u(3)⊕u(2)` act on each
4-dimensional weight space by the scalars `twelveY s / 12` and `twelveQ s / 12`
(`Y_on_weight`, `Q_on_weight`). Together with `hypercharge_table`, `charge_table` and
`weightSpace_finrank`, the spectrum of `Ŷ` on the odd `N`-chirality is that of one SM
generation (+ν^c), each state with multiplicity 4.
-/

namespace GU.Spinor

open Matrix Complex

lemma Xs_F (s : Fin 5 → Bool) (k : Fin 5) :
    Xs s k * ((1 / 2 : ℂ) • (1 + Xs s k)) = (1 / 2 : ℂ) • (1 + Xs s k) := by
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Xs_sq, add_comm]

lemma Xs_Pw (s : Fin 5 → Bool) (k : Fin 5) : ∀ n, k.val < n → n ≤ 5 → Xs s k * Pw s n = Pw s n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hk hn
    simp only [Pw, (show n < 5 by omega), ↓reduceDIte]
    by_cases hkn : k.val = n
    · have hc := (Pw_props s n (by omega)).2 k
      have : (⟨n, by omega⟩ : Fin 5) = k := Fin.ext hkn.symm
      rw [this, ← Matrix.mul_assoc, ← hc.eq, Matrix.mul_assoc, Xs_F]
    · rw [← Matrix.mul_assoc, ih (by omega) (by omega)]

/-- `π_k` acts on the weight space by `−i s_k`. -/
theorem πC_on_weight (s : Fin 5 → Bool) (k : Fin 5) :
    πC k * Pw s 5 = (-(sgnC (s k) * I)) • Pw s 5 := by
  have h := Xs_Pw s k 5 k.2 le_rfl
  rw [Xs, Matrix.smul_mul] at h
  have hu : (sgnC (s k) * I) * (-(sgnC (s k) * I)) = 1 := by
    unfold sgnC; split_ifs <;> ring_nf <;> simp [I_sq]
  calc πC k * Pw s 5 = ((-(sgnC (s k) * I)) * (sgnC (s k) * I)) • (πC k * Pw s 5) := by
        rw [mul_comm, hu, one_smul]
    _ = (-(sgnC (s k) * I)) • Pw s 5 := by rw [← smul_smul, h]

/-- Hypercharge operator. -/
noncomputable def Yop : MC :=
  (I / 12) • ((-2 : ℂ) • (πC 0 + πC 1 + πC 2) + (3 : ℂ) • (πC 3 + πC 4))

/-- Electric charge operator. -/
noncomputable def Qop : MC := Yop + (I / 4) • (πC 3 - πC 4)

lemma sgnC_eq (b : Bool) : sgnC b = (sgn b : ℂ) := by unfold sgnC sgn; split_ifs <;> simp

theorem Y_on_weight (s : Fin 5 → Bool) : Yop * Pw s 5 = ((twelveY s : ℂ) / 12) • Pw s 5 := by
  simp only [Yop, Matrix.smul_mul, Matrix.add_mul, πC_on_weight, smul_add, smul_smul, ← add_smul]
  congr 1
  simp only [twelveY, sgnC_eq]
  push_cast
  ring_nf
  simp [I_sq]
  ring

theorem Q_on_weight (s : Fin 5 → Bool) : Qop * Pw s 5 = ((twelveQ s : ℂ) / 12) • Pw s 5 := by
  simp only [Qop, Matrix.add_mul, Y_on_weight, Matrix.smul_mul, Matrix.sub_mul, πC_on_weight,
    smul_sub, smul_smul, ← sub_smul, ← add_smul]
  congr 1
  simp only [twelveQ, twelveY, sgnC_eq]
  push_cast
  ring_nf
  simp [I_sq]
  ring

end GU.Spinor
