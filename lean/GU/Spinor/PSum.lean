/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Pauli

/-!
# Integer linear combinations of Pauli strings

`CSum := List PString` (each string carries its integer coefficient in `s`), read as
`Σ p.toMat`. Products and commutators are computed symbolically. `toMat_eq_zero` certifies
`Σ = 0` from a decidable check: for every pattern occurring in the list, its coefficients sum
to zero. This turns Lie-algebra identities in `cl(7,7) ≅ gl(128)` into `decide`-checkable facts.
-/

namespace GU.Spinor

open Matrix

/-- Boolean equality of slot patterns (kernel-reducible). -/
def fbeq (f g : Fin 7 → F2) : Bool := (List.finRange 7).all fun j => f j == g j

theorem fbeq_iff {f g : Fin 7 → F2} : fbeq f g = true ↔ f = g := by
  simp only [fbeq, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨funext, fun h j => h ▸ rfl⟩

abbrev CSum := List PString

namespace CSum

def toMat (L : CSum) : M128 := (L.map PString.toMat).sum

def mul (L M : CSum) : CSum := L.flatMap fun p => M.map fun q => p * q

def neg (L : CSum) : CSum := L.map PString.neg

/-- Commutator `[L, M]`. -/
def comm (L M : CSum) : CSum := mul L M ++ neg (mul M L)

/-- Integer scaling. -/
def smul (c : ℤ) (L : CSum) : CSum := L.map fun p => ⟨c * p.s, p.f⟩

@[simp] lemma toMat_nil : toMat [] = 0 := rfl
@[simp] lemma toMat_cons (p : PString) (L : CSum) : toMat (p :: L) = p.toMat + toMat L := by
  simp [toMat]
@[simp] lemma toMat_append (L M : CSum) : toMat (L ++ M) = toMat L + toMat M := by
  simp [toMat]

lemma toMat_map_mul (p : PString) (M : CSum) : toMat (M.map fun q => p * q) = p.toMat * toMat M := by
  induction M with
  | nil => simp
  | cons q M ih => simp only [List.map_cons, toMat_cons, ih, PString.toMat_mul, Matrix.mul_add]

theorem toMat_mul (L M : CSum) : toMat (mul L M) = toMat L * toMat M := by
  induction L with
  | nil => simp [mul]
  | cons p L ih =>
    simp only [mul, List.flatMap_cons, toMat_append, toMat_cons, Matrix.add_mul] at *
    rw [toMat_map_mul, ih]

theorem toMat_neg (L : CSum) : toMat (neg L) = -toMat L := by
  induction L with
  | nil => simp [neg]
  | cons p L ih => simp only [neg, List.map_cons, toMat_cons, neg_add] at *; rw [PString.toMat_neg, ih]

theorem toMat_comm (L M : CSum) : toMat (comm L M) = toMat L * toMat M - toMat M * toMat L := by
  rw [comm, toMat_append, toMat_neg, toMat_mul, toMat_mul, sub_eq_add_neg]

/-- Total coefficient of a pattern. -/
def coef (L : CSum) (f : Fin 7 → F2) : ℤ := ((L.filter fun p => fbeq p.f f).map (·.s)).sum

/-- Decidable sufficient condition for `toMat L = 0`. -/
def isZero (L : CSum) : Bool := L.all fun p => coef L p.f == 0

lemma toMat_of_same (L : CSum) (f : Fin 7 → F2) (h : ∀ p ∈ L, p.f = f) :
    toMat L = ((((L.map (·.s)).sum : ℤ)) : ℝ) • tprod (fun j => F2.toM (f j)) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [toMat_cons, List.map_cons, List.sum_cons, Int.cast_add, add_smul]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), PString.toMat, h p (List.mem_cons_self ..)]

theorem toMat_eq_zero_aux : ∀ (k : ℕ) (L : CSum), L.length ≤ k →
    (∀ p ∈ L, coef L p.f = 0) → toMat L = 0 := by
  intro k
  induction k with
  | zero => intro L hL _; rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hL)]; rfl
  | succ k ih =>
    intro L hL hc
    cases L with
    | nil => rfl
    | cons p rest =>
      set L := p :: rest with hLdef
      set P : PString → Bool := fun q => fbeq q.f p.f
      have hperm : (L.filter P ++ L.filter (fun q => !P q)).Perm L := List.filter_append_perm P L
      have hsplit : toMat L = toMat (L.filter P) + toMat (L.filter fun q => !P q) := by
        rw [← toMat_append]; simp only [toMat]; exact ((hperm.map PString.toMat).sum_eq).symm
      have h1 : toMat (L.filter P) = 0 := by
        rw [toMat_of_same _ p.f (fun q hq => fbeq_iff.mp (List.mem_filter.mp hq).2)]
        have := hc p (List.mem_cons_self ..)
        simp only [coef] at this
        rw [this]; simp
      have h2 : toMat (L.filter fun q => !P q) = 0 := by
        apply ih
        · have hlt : (L.filter fun q => !P q).length < L.length := by
            apply List.length_filter_lt_length_iff_exists.mpr
            exact ⟨p, List.mem_cons_self .., by simp [P, fbeq_iff]⟩
          omega
        · intro q hq
          have hq' := List.mem_filter.mp hq
          have hne : ¬ q.f = p.f := by
            intro h
            have : fbeq q.f p.f = true := fbeq_iff.mpr h
            simp [P, this] at hq'
          rw [← hc q hq'.1]
          simp only [coef, List.filter_filter]
          congr 2
          apply List.filter_congr
          intro r _
          by_cases hr : fbeq r.f q.f = true
          · have : r.f = q.f := fbeq_iff.mp hr
            have hP : P r = false := by
              simp only [P, this]; exact Bool.eq_false_iff.mpr (fun h => hne (fbeq_iff.mp h))
            simp [hr, hP]
          · simp [hr]
      rw [hsplit, h1, h2, add_zero]

theorem toMat_eq_zero {L : CSum} (h : isZero L = true) : toMat L = 0 :=
  toMat_eq_zero_aux L.length L le_rfl fun p hp => by
    have := List.all_eq_true.mp h p hp
    simpa using this

/-- Two sums agree as matrices if their difference passes the zero test. -/
theorem toMat_eq_of {L M : CSum} (h : isZero (L ++ neg M) = true) : toMat L = toMat M := by
  have := toMat_eq_zero h
  rw [toMat_append, toMat_neg, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

end CSum

end GU.Spinor
