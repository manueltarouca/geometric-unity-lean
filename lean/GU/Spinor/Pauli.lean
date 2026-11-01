/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Gamma

/-!
# Pauli-string calculus for `Cl(7,7)`

`{±1, ±σ₃, ±σ₁, ±ε}` is closed under multiplication, so every product of gamma matrices is
`± tprod(f)` for a slot pattern `f : Fin 7 → F2`. `PString` represents these symbolically;
`toMat_mul` proves the symbolic product agrees with matrix multiplication, so identities between
gamma products become decidable equalities of `PString`s, checked by `decide`.

Traces: `tr(tprod f) = ∏ⱼ tr(f j)`, which is `128` for the identity string and `0` otherwise.
-/

namespace GU.Spinor

open Matrix

namespace F2

/-- Multiplication table: `toM a * toM b = (mulT a b).1 • toM (mulT a b).2`. -/
def mulT : F2 → F2 → ℤ × F2
  | one, x => (1, x)
  | x, one => (1, x)
  | s3, s3 => (1, one)
  | s1, s1 => (1, one)
  | ep, ep => (-1, one)
  | s3, s1 => (1, ep)
  | s1, s3 => (-1, ep)
  | s3, ep => (1, s1)
  | ep, s3 => (-1, s1)
  | s1, ep => (-1, s3)
  | ep, s1 => (1, s3)

theorem mulT_spec (a b : F2) : toM a * toM b = ((mulT a b).1 : ℝ) • toM (mulT a b).2 := by
  cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toM, mulT, mul_apply, Fin.sum_univ_two]

/-- 2×2 trace. -/
def trace2 : F2 → ℤ
  | one => 2
  | _ => 0

theorem trace_toM (a : F2) : trace (toM a) = (trace2 a : ℝ) := by
  cases a <;> simp [toM, trace2, trace, Fin.sum_univ_two]
  norm_num

end F2

/-- A signed Pauli string `s · tprod(f)`. -/
@[ext]
structure PString where
  s : ℤ
  f : Fin 7 → F2

namespace PString

/-- Kernel-reducible equality test (the derived `DecidableEq` on function fields gets stuck). -/
def beq (p q : PString) : Bool :=
  p.s == q.s && (List.finRange 7).all fun j => p.f j == q.f j

theorem eq_of_beq {p q : PString} (h : beq p q = true) : p = q := by
  simp only [beq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  exact PString.ext h.1 (funext h.2)

/-- The matrix of a Pauli string. -/
def toMat (p : PString) : M128 := (p.s : ℝ) • tprod (fun j => F2.toM (p.f j))

instance : Mul PString :=
  ⟨fun p q => ⟨p.s * q.s * ∏ j, (F2.mulT (p.f j) (q.f j)).1, fun j => (F2.mulT (p.f j) (q.f j)).2⟩⟩

@[simp] lemma mul_s (p q : PString) :
    (p * q).s = p.s * q.s * ∏ j, (F2.mulT (p.f j) (q.f j)).1 := rfl
@[simp] lemma mul_f (p q : PString) (j) : (p * q).f j = (F2.mulT (p.f j) (q.f j)).2 := rfl

theorem toMat_mul (p q : PString) : (p * q).toMat = p.toMat * q.toMat := by
  simp only [toMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, tprod_mul]
  simp_rw [F2.mulT_spec]
  rw [tprod_smul, smul_smul]
  simp only [mul_s, mul_f, Int.cast_mul, Int.cast_prod]
  congr 1; ring

/-- The identity string. -/
def one : PString := ⟨1, fun _ => .one⟩

theorem toMat_one : one.toMat = 1 := by
  simp [toMat, one, tprod_one]

/-- `-p`. -/
def neg (p : PString) : PString := ⟨-p.s, p.f⟩

theorem toMat_neg (p : PString) : (neg p).toMat = -p.toMat := by
  simp [toMat, neg, neg_smul]

/-- Integer trace: `tr(tprod f) = ∏ tr(f j)`. -/
def tr (p : PString) : ℤ := p.s * ∏ j, F2.trace2 (p.f j)

theorem trace_tprod (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) :
    trace (tprod A) = ∏ j, trace (A j) := by
  simp only [trace, diag, tprod, of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem trace_toMat (p : PString) : trace p.toMat = (p.tr : ℝ) := by
  simp [toMat, tr, trace_smul, trace_tprod, F2.trace_toM]

/-- Product of a list of strings. -/
def prod : List PString → PString
  | [] => one
  | p :: ps => p * prod ps

theorem toMat_prod (L : List PString) : (prod L).toMat = (L.map toMat).prod := by
  induction L with
  | nil => simp [prod, toMat_one]
  | cons p ps ih => simp [prod, toMat_mul, ih]

end PString

/-- The string of a generator. -/
def gammaP (g : Gen) : PString := ⟨1, sym g⟩

theorem toMat_gammaP (g : Gen) : (gammaP g).toMat = gamma g := by
  simp [PString.toMat, gammaP, gamma]

/-- Product of the generators in a list, as a string. -/
def gprod (L : List Gen) : PString := PString.prod (L.map gammaP)

theorem toMat_gprod (L : List Gen) : (gprod L).toMat = (L.map gamma).prod := by
  rw [gprod, PString.toMat_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => toMat_gammaP g

end GU.Spinor
