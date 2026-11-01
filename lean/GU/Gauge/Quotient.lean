/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Gauge.Inhomogeneous

/-!
# `A/𝓗 = 𝒢/(𝓗 × 𝓗)` (draft (5.13)–(5.14)), algebraically

Fix the base connection `A0` (offset `0`). The orbit map `g ↦ A0 · g` (`rightAct 0`) is onto the
space of connections (`orbit_surjective`), and its fibres are the cosets of the stabilizer
`τ₋(𝓗)` (`orbit_eq_iff`). Ordinary gauge transformations act through the "Seedhe" copy
`ε ↦ (ε, 0)` (`seedhe`, `gauge_eq_rightAct_seedhe`). Hence two connections `A0·g`, `A0·g'` are
gauge equivalent iff `g'` lies in the double coset `τ₋(𝓗) · g · seedhe(𝓗)`
(`gauge_equiv_iff_double_coset`). This is the content of (5.14).
-/

namespace GU.GaugeData

variable {H N : Type*} [Group H] [AddCommGroup N] (D : GaugeData H N)

/-- The Seedhe (straight) gauge group `ε ↦ (ε, 0)`. -/
def seedhe : H →* IG D where
  toFun h := ⟨h, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

theorem gauge_eq_rightAct_seedhe (α : N) (h : H) : D.gauge α h = D.rightAct α (D.seedhe h) := by
  simp [rightAct, seedhe]

theorem orbit_surjective : Function.Surjective (fun g : IG D => D.rightAct 0 g) :=
  fun α => ⟨⟨1, α⟩, by simp [rightAct, gauge, D.ad_one]⟩

/-- Fibres of the orbit map are `τ₋(𝓗)`-cosets. -/
theorem orbit_eq_iff (g g' : IG D) :
    D.rightAct 0 g = D.rightAct 0 g' ↔ ∃ h, g' = D.tau (-1) h * g := by
  constructor
  · intro hgg
    have hs : D.rightAct 0 (g' * g⁻¹) = 0 := by
      rw [D.rightAct_mul, ← hgg, ← D.rightAct_mul, mul_inv_cancel, D.rightAct_one]
    obtain ⟨h, hh⟩ := (D.stabilizer_eq_range_tau_neg _).mp hs
    exact ⟨h, by rw [hh, inv_mul_cancel_right]⟩
  · rintro ⟨h, rfl⟩
    rw [D.rightAct_mul, (D.stabilizer_eq_range_tau_neg _).mpr ⟨h, rfl⟩]

/-- **(5.14)**: gauge equivalence of `A0·g` and `A0·g'` is the double coset relation. -/
theorem gauge_equiv_iff_double_coset (g g' : IG D) :
    (∃ k : H, D.rightAct 0 g' = D.gauge (D.rightAct 0 g) k) ↔
      ∃ h k : H, g' = D.tau (-1) h * g * D.seedhe k := by
  constructor
  · rintro ⟨k, hk⟩
    rw [gauge_eq_rightAct_seedhe, ← D.rightAct_mul] at hk
    obtain ⟨h, hh⟩ := (D.orbit_eq_iff _ _).mp hk.symm
    exact ⟨h, k, by rw [hh, mul_assoc]⟩
  · rintro ⟨h, k, rfl⟩
    refine ⟨k, ?_⟩
    have e : D.rightAct 0 (D.tau (-1) h * g) = D.rightAct 0 g :=
      ((D.orbit_eq_iff g _).mpr ⟨h, rfl⟩).symm
    rw [gauge_eq_rightAct_seedhe, D.rightAct_mul 0 (D.tau (-1) h * g), e]

end GU.GaugeData
