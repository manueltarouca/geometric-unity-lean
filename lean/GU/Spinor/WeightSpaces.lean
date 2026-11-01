/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Hypercharge
import GU.Spinor.Branching

/-!
# Weight spaces of `S̸(Y) = ℂ¹²⁸` under the five plane operators

For a sign vector `s ∈ {±1}⁵` set `X_k = i s_k π_k` (so `X_k² = 1`, pairwise commuting) and
`P_s = Π_k (1 + X_k)/2`. Proved: `P_s` is idempotent with rank exactly 4 for **every** `s`
(`weightSpace_finrank`). So each of the 32 weights of `hypercharge_table` is a genuine
4-dimensional joint eigenspace of the actual 128×128 spinor operators (4 = 2 Lorentz spinor
components × 2 `Y`-chiralities).

Method: `tr(Q_{n+1} M) = tr(Q_n M) + i s_n tr(Q_n π_n M)` is evaluated symbolically on Pauli
strings with Gaussian-integer arithmetic (`gtr`), and `decide` checks `tr Q_5 = 128` for all 32 `s`.
-/

namespace GU.Spinor

open Matrix Complex

abbrev MC := Matrix Idx Idx ℂ

def sgnC (b : Bool) : ℂ := if b then -1 else 1

/-- `π_k` over `ℂ`. -/
def πC (k : Fin 5) : MC := toC (planeOp k).toMat

def Xs (s : Fin 5 → Bool) (k : Fin 5) : MC := (sgnC (s k) * I) • πC k

lemma planeOp_eq (k l : Fin 5) : planeOp k * planeOp l = planeOp l * planeOp k :=
  PString.eq_of_beq ((List.all_eq_true.mp (by decide : (List.finRange 5).all (fun k =>
    (List.finRange 5).all fun l => PString.beq (planeOp k * planeOp l) (planeOp l * planeOp k)) = true)
    k (List.mem_finRange k)) |> List.all_eq_true.mp |> fun h => h l (List.mem_finRange l))

lemma πC_comm (k l : Fin 5) : πC k * πC l = πC l * πC k := by
  simp only [πC, ← toC_mul, ← PString.toMat_mul, planeOp_eq k l]

lemma πC_sq (k : Fin 5) : πC k * πC k = -1 := by
  have h : planeOp k * planeOp k = PString.neg PString.one :=
    PString.eq_of_beq ((List.all_eq_true.mp (by decide : (List.finRange 5).all (fun k =>
      PString.beq (planeOp k * planeOp k) (PString.neg PString.one)) = true)) k (List.mem_finRange k))
  rw [πC, ← toC_mul, ← PString.toMat_mul, h, PString.toMat_neg, PString.toMat_one]
  ext i j; simp [toC, Matrix.one_apply]; split_ifs <;> simp

lemma Xs_sq (s : Fin 5 → Bool) (k : Fin 5) : Xs s k * Xs s k = 1 := by
  rw [Xs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, πC_sq]
  have : sgnC (s k) * I * (sgnC (s k) * I) = -1 := by
    unfold sgnC; split_ifs <;> ring_nf <;> simp [I_sq]
  rw [this]; simp

lemma Xs_comm (s : Fin 5 → Bool) (k l : Fin 5) : Xs s k * Xs s l = Xs s l * Xs s k := by
  simp only [Xs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, πC_comm k l, mul_comm (sgnC (s k) * I)]

/-! ### Symbolic trace -/

/-- Gaussian integers `(a, b) ↦ a + b i`. -/
def gC (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * I

/-- Multiply by `i·σ` (σ = ±1). -/
def mulIσ (σ : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (-(σ * z.2), σ * z.1)

def sgnZ (b : Bool) : ℤ := if b then -1 else 1

/-- Symbolic `tr(Q_n · m)`. -/
def gtr (s : Fin 5 → Bool) : ℕ → PString → ℤ × ℤ
  | 0, m => (m.tr, 0)
  | n + 1, m =>
    if h : n < 5 then gtr s n m + mulIσ (sgnZ (s ⟨n, h⟩)) (gtr s n (planeOp ⟨n, h⟩ * m))
    else gtr s n m

/-- `Q_n = Π_{k<n} (1 + X_k)`. -/
def Q (s : Fin 5 → Bool) : ℕ → MC
  | 0 => 1
  | n + 1 => if h : n < 5 then Q s n * (1 + Xs s ⟨n, h⟩) else Q s n

lemma gC_add (z w : ℤ × ℤ) : gC (z + w) = gC z + gC w := by
  simp [gC, Prod.fst_add, Prod.snd_add]; ring

lemma gC_mulIσ (b : Bool) (z : ℤ × ℤ) : gC (mulIσ (sgnZ b) z) = (sgnC b * I) * gC z := by
  unfold gC mulIσ sgnZ sgnC; split_ifs <;> push_cast <;> ring_nf <;> simp [I_sq]

theorem trace_Q (s : Fin 5 → Bool) (n : ℕ) (m : PString) :
    trace (Q s n * toC m.toMat) = gC (gtr s n m) := by
  induction n generalizing m with
  | zero =>
    simp only [Q, gtr, Matrix.one_mul, gC]
    rw [trace_toC, PString.trace_toMat]; simp
  | succ n ih =>
    simp only [Q, gtr]
    split_ifs with h
    · rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, trace_add, ih, gC_add,
        Xs, Matrix.smul_mul, Matrix.mul_smul, trace_smul, πC, ← toC_mul, ← PString.toMat_mul, ih,
        gC_mulIσ, smul_eq_mul]
    · exact ih m

theorem gtr_all : ∀ s : Fin 5 → Bool, gtr s 5 PString.one = (128, 0) := by decide

/-- `P_s = Π_k (1 + X_k)/2`, built left to right. -/
noncomputable def Pw (s : Fin 5 → Bool) : ℕ → MC
  | 0 => 1
  | n + 1 => if h : n < 5 then Pw s n * ((1 / 2 : ℂ) • (1 + Xs s ⟨n, h⟩)) else Pw s n

lemma Pw_eq (s : Fin 5 → Bool) (n : ℕ) (hn : n ≤ 5) : Pw s n = ((1 / 2 : ℂ) ^ n) • Q s n := by
  induction n with
  | zero => simp [Pw, Q]
  | succ n ih =>
    simp only [Pw, Q, (show n < 5 by omega), ↓reduceDIte]
    rw [ih (by omega), Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

lemma Pw_props (s : Fin 5 → Bool) (n : ℕ) (hn : n ≤ 5) :
    IsIdempotentElem (Pw s n) ∧ ∀ k, Commute (Pw s n) (Xs s k) := by
  induction n with
  | zero => exact ⟨IsIdempotentElem.one, fun k => Commute.one_left _⟩
  | succ n ih =>
    obtain ⟨hi, hc⟩ := ih (by omega)
    simp only [Pw, (show n < 5 by omega), ↓reduceDIte]
    set F := (1 / 2 : ℂ) • (1 + Xs s ⟨n, by omega⟩)
    have hF : IsIdempotentElem F := half_idem (Xs_sq s _)
    have hFX : ∀ k, Commute F (Xs s k) := fun k => by
      show F * Xs s k = Xs s k * F
      simp only [F, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, Xs_comm s ⟨n, _⟩ k]
    have hPF : Commute (Pw s n) F := by
      show Pw s n * F = F * Pw s n
      simp only [F, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul, (hc ⟨n, by omega⟩).eq]
    exact ⟨hi.mul_of_commute hPF hF, fun k => (hc k).mul_left (hFX k)⟩

/-- **Every weight space has rank 4.** -/
theorem weightSpace_finrank (s : Fin 5 → Bool) :
    IsIdempotentElem (Pw s 5) ∧ Module.finrank ℂ (LinearMap.range (Matrix.toLin' (Pw s 5))) = 4 := by
  have hI := (Pw_props s 5 le_rfl).1
  refine ⟨hI, ?_⟩
  have hL : IsIdempotentElem (Matrix.toLin' (Pw s 5)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hI.eq]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hL).trace
  rw [Matrix.trace_toLin'_eq] at ht
  have hq : trace (Q s 5) = 128 := by
    have := trace_Q s 5 PString.one
    rw [PString.toMat_one] at this
    have h1 : toC (1 : M128) = 1 := by ext i j; simp [toC, Matrix.one_apply]
    rw [h1, Matrix.mul_one, gtr_all, gC] at this
    simpa using this
  have htr : trace (Pw s 5) = 4 := by
    rw [Pw_eq s 5 le_rfl, trace_smul, hq]; norm_num
  rw [htr] at ht
  exact_mod_cast ht.symm

end GU.Spinor
