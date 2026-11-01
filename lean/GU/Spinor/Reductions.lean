/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.PSum
import GU.Spinor.Branching

/-!
# Structure-group reductions in the normal bundle `N^{6,4}` (draft §4.1, (4.6))

All statements live in `cl(7,7) ≅ gl(128,ℝ)` and use the explicit gammas of the (6,4) block
(`gens10`). Bivectors `γ_aγ_b` span `spin(6,4)`.

* **Maximal compact.** `θ` = conjugation by `e₋ = γ(3,−)γ(4,−)γ(5,−)γ(6,−)`. Bivectors inside
  the positive 6 or the negative 4 commute with `e₋` (this is `so(6) ⊕ so(4) ≅ su(4) ⊕ su(2) ⊕ su(2)`,
  Pati–Salam), and mixed bivectors anticommute (the noncompact part). Counts: 15 + 6 = 21 vs 24.
* **Complex reduction U(3,2).** `J = Σ_k γ_{2k-1}γ_{2k}` over the five planes (three positive,
  two negative) is the complex structure. `u32` lists 25 elements commuting with `J` and linearly
  independent (certified via the trace form). The matching upper bound (the centraliser of `J` in
  `spin(6,4)` is exactly this 25-dimensional span) is `centralizer_spin64` in `SpanFull.lean`.
* **Standard Model (4.6).** The 13 elements of `u32` that also commute with `e₋` span
  `u(3) ⊕ u(2) = su(3) ⊕ su(2) ⊕ u(1) ⊕ u(1)`: the Standard Model algebra up to one extra
  `u(1)`, exactly the "reductive factor of U(1)" caveat stated after (4.6).
-/

namespace GU.Spinor

open Matrix CSum

def biv (a b : Gen) : CSum := [gammaP a * gammaP b]

/-- The five complex planes of `N^{6,4} ≅ ℂ^{3,2}`. -/
def planes : List (Gen × Gen) :=
  [((1, false), (2, false)), ((3, false), (4, false)), ((5, false), (6, false)),
   ((3, true), (4, true)), ((5, true), (6, true))]

/-- Complex structure `J`. -/
def Jc : CSum := planes.flatMap fun p => biv p.1 p.2

/-- Product of the four negative generators of the (6,4) block (Cartan involution). -/
def eNeg : CSum := [gprod [(3, true), (4, true), (5, true), (6, true)]]

def sameType (p q : Gen × Gen) : Bool := p.1.2 == q.1.2

/-- The 25 generators of `u(3,2)`: `J_k` per plane, and for each pair of planes the two
combinations commuting with `J`. -/
def u32 : List CSum :=
  (planes.map fun p => biv p.1 p.2) ++
  ((List.finRange 5).flatMap fun i => (List.finRange 5).filterMap fun j =>
    if i < j then some (i, j) else none).flatMap fun ij =>
      let p := planes.get ⟨ij.1, by simp [planes]⟩
      let q := planes.get ⟨ij.2, by simp [planes]⟩
      if sameType p q then
        [biv p.1 q.1 ++ biv p.2 q.2, biv p.1 q.2 ++ neg (biv p.2 q.1)]
      else
        [biv p.1 q.1 ++ neg (biv p.2 q.2), biv p.1 q.2 ++ biv p.2 q.1]

/-- All 45 bivectors of the (6,4) block. -/
def bivs10 : List CSum :=
  ((List.finRange 10).flatMap fun i => (List.finRange 10).filterMap fun j =>
    if i < j then some (biv (gens10.get (Fin.cast (by decide) i)) (gens10.get (Fin.cast (by decide) j)))
    else none)

theorem bivs10_length : bivs10.length = 45 := by decide

/-- **Pati–Salam / maximal compact:** 21 bivectors commute with `e₋` (`so(6) ⊕ so(4)`,
`15 + 6`), and the other 24 anticommute (noncompact). -/
theorem pati_salam_split :
    (bivs10.filter fun X => isZero (comm X eNeg)).length = 21 ∧
      (bivs10.filter fun X => isZero (mul X eNeg ++ mul eNeg X)).length = 24 := by decide

theorem u32_length : u32.length = 25 := by decide

/-- Every listed element commutes with `J`. -/
theorem u32_commutes_J : u32.all (fun X => isZero (comm X Jc)) = true := by decide

/-- Compact (θ-fixed) part: elements commuting with `e₋`. -/
def smPart : List CSum := u32.filter fun X => isZero (comm X eNeg)

theorem smPart_length : smPart.length = 13 := by decide

/-- The remaining 12 elements are θ-odd (they anticommute with `e₋`). -/
theorem noncompact_anticomm :
    (u32.filter fun X => !isZero (comm X eNeg)).all
      (fun X => isZero (mul X eNeg ++ mul eNeg X)) = true := by decide

/-! ### Linear independence via the trace form -/

/-- `tr(X Y)` computed symbolically. -/
def trPair (X Y : CSum) : ℤ := ((mul X Y).map PString.tr).sum

lemma trace_toMat_sum (L : CSum) : trace (toMat L) = (((L.map PString.tr).sum : ℤ) : ℝ) := by
  induction L with
  | nil => simp
  | cons p L ih => simp [trace_add, ih, PString.trace_toMat]

lemma trace_mul_eq (X Y : CSum) : trace (toMat X * toMat Y) = (trPair X Y : ℝ) := by
  rw [← toMat_mul, trace_toMat_sum, trPair]

/-- A family with diagonal, nondegenerate trace-Gram matrix is linearly independent. -/
theorem linIndep_of_gram {k : ℕ} (B : Fin k → CSum)
    (hg : ∀ i j, i ≠ j → trPair (B i) (B j) = 0) (hd : ∀ i, trPair (B i) (B i) ≠ 0) :
    LinearIndependent ℝ (fun i => toMat (B i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum j
  have h := congrArg (fun M => trace (M * toMat (B j))) hsum
  simp only [Finset.sum_mul, trace_sum, smul_mul_assoc, trace_smul, zero_mul, trace_zero,
    trace_mul_eq, smul_eq_mul] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hg i j hij]; simp) (by simp)] at h
  have := hd j
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd (by exact_mod_cast h) this

theorem u32_gram_offdiag : ∀ i j : Fin 25, i ≠ j →
    trPair (u32.get ⟨i, by rw [u32_length]; exact i.2⟩) (u32.get ⟨j, by rw [u32_length]; exact j.2⟩) = 0 := by
  decide

theorem u32_gram_diag : ∀ i : Fin 25,
    trPair (u32.get ⟨i, by rw [u32_length]; exact i.2⟩) (u32.get ⟨i, by rw [u32_length]; exact i.2⟩) ≠ 0 := by
  decide

/-- **`dim u(3,2) = 25`** inside `spin(6,4) ⊂ gl(128)`: the 25 elements are independent. -/
theorem u32_linIndep :
    LinearIndependent ℝ (fun i : Fin 25 => toMat (u32.get ⟨i, by rw [u32_length]; exact i.2⟩)) :=
  linIndep_of_gram _ u32_gram_offdiag u32_gram_diag

end GU.Spinor
