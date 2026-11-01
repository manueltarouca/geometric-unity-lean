/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.UG.R0
import GU.Spinor.UG.R1
import GU.Spinor.UG.R2
import GU.Spinor.UG.R3
import GU.Spinor.UG.R4
import GU.Spinor.UG.Diag
import GU.Spinor.CentralizerMain

/-!
# `span(u32 ∪ u32c)` is the whole bivector algebra `spin(6,4)`; the centraliser of `J` there is `u(3,2)`

* `allU_linIndep`: the 45 elements are linearly independent (row-wise trace-Gram, `GU/Spinor/UG/`).
* `allU_in_bivs`: each is `±b_k ± b_l` for bivectors `b_k` of the (6,4) block (`repT`, by `decide`).
* `span_eq`: hence their span equals the span of the 45 bivectors (`dim ≤ 45`).
* **`centralizer_spin64`**: an element of `spin(6,4) = span(bivectors)` commutes with `J` iff it lies
  in `span(u32)`, which has dimension 25 (`u32_linIndep`). So the centraliser of the complex
  structure `J` in `spin(6,4)` is exactly the 25-dimensional `u(3,2)`.
-/

namespace GU.Spinor

open Matrix CSum

def bv (k : ℕ) : CSum := bivs10.getD k []

def repT : List (ℕ × ℤ × ℕ × ℤ) := [(0, 1, 45, 1), (17, 1, 45, 1), (30, 1, 45, 1), (39, 1, 45, 1), (44, 1, 45, 1), (1, 1, 10, 1), (2, 1, 9, -1), (3, 1, 12, 1), (4, 1, 11, -1), (5, 1, 14, -1), (6, 1, 13, 1), (7, 1, 16, -1), (8, 1, 15, 1), (18, 1, 25, 1), (19, 1, 24, -1), (20, 1, 27, -1), (21, 1, 26, 1), (22, 1, 29, -1), (23, 1, 28, 1), (31, 1, 36, -1), (32, 1, 35, 1), (33, 1, 38, -1), (34, 1, 37, 1), (40, 1, 43, 1), (41, 1, 42, -1), (1, 1, 10, -1), (2, 1, 9, 1), (3, 1, 12, -1), (4, 1, 11, 1), (5, 1, 14, 1), (6, 1, 13, -1), (7, 1, 16, 1), (8, 1, 15, -1), (18, 1, 25, -1), (19, 1, 24, 1), (20, 1, 27, 1), (21, 1, 26, -1), (22, 1, 29, 1), (23, 1, 28, -1), (31, 1, 36, 1), (32, 1, 35, -1), (33, 1, 38, 1), (34, 1, 37, -1), (40, 1, 43, -1), (41, 1, 42, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep_ok : (List.range 45).all (fun i => let t := repT.getD i (0, 0, 0, 0);
    isZero (allU.getD i [] ++ neg (smul t.2.1 (bv t.1) ++ smul t.2.2.2 (bv t.2.2.1)))) = true := by
  decide +kernel

theorem U_gram_offdiag (i j : Fin 45) (h : i ≠ j) : trPair (U i) (U j) = 0 := by
  fin_cases i
  exacts [Urow0 j h, Urow1 j h, Urow2 j h, Urow3 j h, Urow4 j h, Urow5 j h, Urow6 j h, Urow7 j h, Urow8 j h, Urow9 j h, Urow10 j h, Urow11 j h, Urow12 j h, Urow13 j h, Urow14 j h, Urow15 j h, Urow16 j h, Urow17 j h, Urow18 j h, Urow19 j h, Urow20 j h, Urow21 j h, Urow22 j h, Urow23 j h, Urow24 j h, Urow25 j h, Urow26 j h, Urow27 j h, Urow28 j h, Urow29 j h, Urow30 j h, Urow31 j h, Urow32 j h, Urow33 j h, Urow34 j h, Urow35 j h, Urow36 j h, Urow37 j h, Urow38 j h, Urow39 j h, Urow40 j h, Urow41 j h, Urow42 j h, Urow43 j h, Urow44 j h]

theorem allU_linIndep : LinearIndependent ℝ (fun i => toMat (U i)) :=
  linIndep_of_gram _ U_gram_offdiag U_gram_diag

lemma toMat_smul (c : ℤ) (L : CSum) : toMat (smul c L) = (c : ℝ) • toMat L := by
  induction L with
  | nil => simp [CSum.smul]
  | cons p L ih =>
    simp only [CSum.smul, List.map_cons, toMat_cons] at *
    rw [ih, smul_add]
    congr 1
    simp [PString.toMat, smul_smul]

/-- The span of the 45 bivectors of the (6,4) block: `spin(6,4)`. -/
noncomputable def spin64 : Submodule ℝ M128 := Submodule.span ℝ (Set.range fun k : Fin 45 => toMat (bv k))

lemma bv_mem (k : ℕ) : toMat (bv k) ∈ spin64 := by
  by_cases hk : k < 45
  · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  · have : bv k = [] := by
      unfold bv; rw [List.getD_eq_default]; simp [bivs10_length]; omega
    rw [this]; exact spin64.zero_mem

theorem allU_in_bivs (i : Fin 45) : toMat (U i) ∈ spin64 := by
  have h := List.all_eq_true.mp rep_ok i.val (List.mem_range.mpr i.2)
  simp only at h
  have e := toMat_eq_zero h
  rw [toMat_append, toMat_neg, toMat_append, toMat_smul, toMat_smul, ← sub_eq_add_neg, sub_eq_zero] at e
  have hU : toMat (U i) = toMat (allU.getD i.val []) := by
    simp [U, allU_length]
  rw [hU, e]
  exact spin64.add_mem (spin64.smul_mem _ (bv_mem _)) (spin64.smul_mem _ (bv_mem _))

theorem span_eq : Submodule.span ℝ (Set.range fun i : Fin 45 => toMat (U i)) = spin64 := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact allU_in_bivs i)
  · rw [finrank_span_eq_card allU_linIndep]
    exact finrank_range_le_card (fun k : Fin 45 => toMat (bv k))

lemma comm_of_mem_span {Y : M128} (hY : Y ∈ Submodule.span ℝ (Set.range fun i : Fin 25 => toMat (U25 i))) :
    Y * toMat Jc = toMat Jc * Y := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have := toMat_eq_zero (U25_comm i); rwa [toMat_comm, sub_eq_zero] at this
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]

lemma U_split (c : Fin 45 → ℝ) :
    ∑ i : Fin 45, c i • toMat (U i) =
      (∑ i : Fin 25, c (Fin.castAdd 20 i) • toMat (U25 i)) + ∑ j : Fin 20, c (Fin.natAdd 25 j) • toMat (Uc j) := by
  rw [show (∑ i : Fin 45, c i • toMat (U i)) = ∑ i : Fin (25 + 20), c i • toMat (U i) from rfl,
    Fin.sum_univ_add]
  congr 1

/-- **The centraliser of `J` in `spin(6,4)` is exactly `span(u32)`**, a 25-dimensional space (`u(3,2)`). -/
theorem centralizer_spin64 (X : M128) (hX : X ∈ spin64) :
    X * toMat Jc = toMat Jc * X ↔ X ∈ Submodule.span ℝ (Set.range fun i : Fin 25 => toMat (U25 i)) := by
  rw [← span_eq, Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, rfl⟩ := hX
  rw [U_split]
  constructor
  · intro hcomm
    have hb := (centralizer_iff _ _).mp hcomm
    have : (fun j : Fin 20 => c (Fin.natAdd 25 j)) = 0 := hb
    rw [show (∑ j : Fin 20, c (Fin.natAdd 25 j) • toMat (Uc j)) = 0 by
      simp only [congrFun this, Pi.zero_apply, zero_smul, Finset.sum_const_zero], add_zero]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · exact comm_of_mem_span

theorem u32_span_finrank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : Fin 25 => toMat (U25 i))) = 25 := by
  have : LinearIndependent ℝ (fun i : Fin 25 => toMat (U25 i)) := by
    have h := allU_linIndep.comp (Fin.castAdd 20) (Fin.castAdd_injective 25 20)
    convert h using 2 with i
    simp only [Function.comp, U, U25, allU, List.get_eq_getElem, Fin.val_cast]
    rw [List.getElem_append_left]
    rfl
  rw [finrank_span_eq_card this, Fintype.card_fin]

end GU.Spinor
