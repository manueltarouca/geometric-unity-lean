/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.TorusPeriod
import GU.Spinor.SpinKernel

/-!
# The kernel of the torus `ℝ⁵ → Spin(7,7)`

**`torus_eq_one_iff`**: `torus s = 1 ↔ s = n·π` with `n ∈ ℤ⁵` and `Σ nₖ` even.

Proof: `torus s` maps `e_{a_k}` to `cos(2sₖ) e_{a_k} − ε sin(2sₖ) e_{b_k}` (the other four circles fix
plane `k`), so `torus s = 1` forces `cos 2sₖ = 1`, i.e. `sₖ = nₖπ`; then every circle is `(−1)^{nₖ}` and
`torus s = (−1)^{Σ nₖ}`, which is `1` iff `Σ nₖ` is even (`−1 ≠ 1`, `negOne_ne_one`).

On the fundamental domain `[0, 2π)⁵` the kernel is `{nπ : n ∈ {0,1}⁵, Σ n even}`
(`torus_eq_one_iff_fundamental`); there are 16 such `n` (`kernel_reps_card`). As a group:
`ker torus / 2πℤ⁵ ≃* (ℤ/2)⁴` (`torusKer_quot_equiv_four`, `TorusKernelGroup.lean`).
-/

namespace GU.Spinor

open CliffordAlgebra Real

lemma pa_ne_pa {k l : Fin 5} (h : l ≠ k) : pa k ≠ pa l := by
  revert h; fin_cases k <;> fin_cases l <;> decide

lemma pa_ne_pb' (k l : Fin 5) : pa k ≠ pb l := by fin_cases k <;> fin_cases l <;> decide

lemma pb_ne_pb {k l : Fin 5} (h : l ≠ k) : pb k ≠ pb l := by
  revert h; fin_cases k <;> fin_cases l <;> decide

/-- A torus element whose `k`-th angle is trivial fixes `e_{a_k}`. -/
lemma torus_fix (k : Fin 5) (g : Fin 5 → Multiplicative ℝ) (hg : g k = 1) :
    vecRep (torus g) (eb (pa k)) = eb (pa k) := by
  have hfix : ∀ l, vecRep (planeCircle l (g l)) (eb (pa k)) = eb (pa k) := fun l => by
    by_cases h : l = k
    · subst h; rw [hg, map_one, map_one]; rfl
    · exact circle_fixes l (Multiplicative.toAdd (g l)) _
        ⟨by simp [eb, (pa_ne_pa h).symm], by simp [eb, (pa_ne_pb' k l).symm]⟩
  rw [torus_eq]
  simp only [map_mul, LinearEquiv.mul_apply, hfix]

/-- **The torus rotates plane `k` by `2sₖ`.** -/
lemma vecRep_torus (k : Fin 5) (s : Fin 5 → ℝ) :
    vecRep (torus fun l => Multiplicative.ofAdd (s l)) (eb (pa k)) =
      cos (2 * s k) • eb (pa k) - (εp k * sin (2 * s k)) • eb (pb k) := by
  set f : Fin 5 → Multiplicative ℝ := fun l => Multiplicative.ofAdd (s l)
  have hf : f = Pi.mulSingle k (f k) * Function.update f k 1 := by
    funext l; by_cases h : l = k
    · subst h; simp
    · simp [h]
  rw [hf, map_mul, show torus (Pi.mulSingle k (f k)) = planeCircle k (f k) from
    MonoidHom.noncommPiCoprod_mulSingle _ _ _, map_mul, LinearEquiv.mul_apply,
    torus_fix k _ (by simp)]
  exact vecRep_circle k (s k)

lemma circle_intpi (k : Fin 5) (n : ℤ) :
    planeCircle k (Multiplicative.ofAdd (n * π)) = negOne ^ n := by
  have h : planeCircle k (Multiplicative.ofAdd π) = negOne := Subtype.ext (circle_pi k)
  rw [show Multiplicative.ofAdd ((n : ℝ) * π) = (Multiplicative.ofAdd π) ^ n by
    rw [← ofAdd_zsmul, zsmul_eq_mul], map_zpow, h]

lemma negOne_sq : negOne ^ 2 = 1 := Subtype.ext (by simp [negOne])

lemma orderOf_negOne : orderOf negOne = 2 :=
  orderOf_eq_prime negOne_sq negOne_ne_one

lemma negOne_zpow_eq_one_iff (m : ℤ) : negOne ^ m = 1 ↔ Even m := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_negOne, Nat.cast_ofNat, even_iff_two_dvd]

lemma torus_intpi (n : Fin 5 → ℤ) :
    torus (fun k => Multiplicative.ofAdd (n k * π)) = negOne ^ (∑ k, n k) := by
  rw [torus_eq]
  simp only [circle_intpi, Fin.sum_univ_five, zpow_add]

/-- **Kernel of the torus**: `torus s = 1 ↔ s ∈ πℤ⁵` with even coordinate sum. -/
theorem torus_eq_one_iff (s : Fin 5 → ℝ) :
    torus (fun k => Multiplicative.ofAdd (s k)) = 1 ↔
      ∃ n : Fin 5 → ℤ, (∀ k, s k = n k * π) ∧ Even (∑ k, n k) := by
  constructor
  · intro h
    have hn : ∀ k, ∃ m : ℤ, s k = m * π := fun k => by
      have hv := vecRep_torus k s
      rw [h, map_one] at hv
      have c := congrFun hv (pa k)
      simp [eb, (pa_ne_pb k)] at c
      obtain ⟨m, hm⟩ := (cos_eq_one_iff _).mp c.symm
      exact ⟨m, by linarith⟩
    choose n hn using hn
    refine ⟨n, hn, ?_⟩
    have hs : (fun k => Multiplicative.ofAdd (s k)) = fun k => Multiplicative.ofAdd ((n k : ℝ) * π) :=
      funext fun k => by rw [hn k]
    rw [hs, torus_intpi] at h
    exact (negOne_zpow_eq_one_iff _).mp h
  · rintro ⟨n, hn, he⟩
    have hs : (fun k => Multiplicative.ofAdd (s k)) = fun k => Multiplicative.ofAdd ((n k : ℝ) * π) :=
      funext fun k => by rw [hn k]
    rw [hs, torus_intpi]
    exact (negOne_zpow_eq_one_iff _).mpr he

/-- **On the fundamental domain `[0, 2π)⁵`** the kernel is `{nπ : n ∈ {0,1}⁵, Σ n even}`. -/
theorem torus_eq_one_iff_fundamental (s : Fin 5 → ℝ) (hs : ∀ k, 0 ≤ s k ∧ s k < 2 * π) :
    torus (fun k => Multiplicative.ofAdd (s k)) = 1 ↔
      ∃ n : Fin 5 → Fin 2, (∀ k, s k = (n k : ℕ) * π) ∧ Even (∑ k, (n k : ℕ)) := by
  rw [torus_eq_one_iff]
  constructor
  · rintro ⟨n, hn, he⟩
    have hb : ∀ k, 0 ≤ n k ∧ n k < 2 := fun k => by
      have h1 := hs k; rw [hn k] at h1
      have hp := pi_pos
      constructor
      · by_contra hc
        have : (n k : ℝ) ≤ -1 := by exact_mod_cast (by omega : n k ≤ -1)
        nlinarith
      · by_contra hc
        have : (2 : ℝ) ≤ n k := by exact_mod_cast (by omega : 2 ≤ n k)
        nlinarith
    refine ⟨fun k => ⟨(n k).toNat, by have := hb k; omega⟩, fun k => ?_, ?_⟩
    · rw [hn k]; congr 1
      have := hb k
      exact_mod_cast (Int.toNat_of_nonneg this.1).symm
    · have hcast : ((∑ k, ((n k).toNat : ℕ) : ℕ) : ℤ) = ∑ k, n k := by
        push_cast
        exact Finset.sum_congr rfl fun k _ => Int.toNat_of_nonneg (hb k).1
      rw [← Int.even_coe_nat, hcast]; exact he
  · rintro ⟨n, hn, he⟩
    refine ⟨fun k => (n k : ℕ), fun k => by rw [hn k]; push_cast; rfl, ?_⟩
    rw [← Nat.cast_sum, Int.even_coe_nat]; exact he

/-- There are `16 = 2⁴` even-weight vectors in `{0,1}⁵`. -/
theorem kernel_reps_card :
    (Finset.univ.filter fun n : Fin 5 → Fin 2 => Even (∑ k, (n k : ℕ))).card = 16 := by decide

end GU.Spinor
