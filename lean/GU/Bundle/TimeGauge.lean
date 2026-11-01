/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SpinExamples

/-!
# Phase 4, item 4: the time-gauge locus and its global frame

`gaugeSet`: symmetric `G` passing the Lorentzian Cholesky tests (`G₀₀ > 0` and the three Schur
pivots `m1, m2, m3 > 0`), an open set (`isOpen_gaugeSet`) containing `ηR` (`ηR_mem_gaugeSet`).
**`gaugeP_eq`**: `G = P ηR Pᵀ` for the explicit `P = gaugeP G`, continuous on the set
(`continuousOn_gaugeP`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The spatial Schur complement (negated). -/
def schur (G : M4) (i j : Fin 4) : ℝ := G 0 i * G 0 j / G 0 0 - G i j

def c11 (G : M4) : ℝ := Real.sqrt (schur G 1 1)
def c21 (G : M4) : ℝ := schur G 1 2 / c11 G
def c31 (G : M4) : ℝ := schur G 1 3 / c11 G
def m2 (G : M4) : ℝ := schur G 2 2 - c21 G ^ 2
def c22 (G : M4) : ℝ := Real.sqrt (m2 G)
def c32 (G : M4) : ℝ := (schur G 2 3 - c31 G * c21 G) / c22 G
def m3 (G : M4) : ℝ := schur G 3 3 - c31 G ^ 2 - c32 G ^ 2
def c33 (G : M4) : ℝ := Real.sqrt (m3 G)

/-- **The time-gauge locus.** -/
def gaugeSet : Set M4 := {G | 0 < G 0 0 ∧ 0 < schur G 1 1 ∧ 0 < m2 G ∧ 0 < m3 G}

/-- **The Lorentzian Cholesky factor.** -/
def gaugeP (G : M4) : M4 :=
  !![Real.sqrt (G 0 0), 0, 0, 0;
     G 0 1 / Real.sqrt (G 0 0), c11 G, 0, 0;
     G 0 2 / Real.sqrt (G 0 0), c21 G, c22 G, 0;
     G 0 3 / Real.sqrt (G 0 0), c31 G, c32 G, c33 G]

/-- **`G = P ηR Pᵀ` on the gauge locus.** -/
theorem gaugeP_eq {G : M4} (hs : G.IsSymm) (hG : G ∈ gaugeSet) : gaugeP G * ηR * (gaugeP G)ᵀ = G := by
  obtain ⟨h0, h1, h2, h3⟩ := hG
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hs i) j; exact this
  set r := Real.sqrt (G 0 0) with hr
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have hr2 : r * r = G 0 0 := Real.mul_self_sqrt h0.le
  have hc1 : c11 G ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hc12 : c11 G * c11 G = schur G 1 1 := Real.mul_self_sqrt h1.le
  have hc2 : c22 G ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  have hc22 : c22 G * c22 G = m2 G := Real.mul_self_sqrt h2.le
  have hc32 : c33 G * c33 G = m3 G := Real.mul_self_sqrt h3.le
  have e11 : G 1 1 = (G 0 1 / r) * (G 0 1 / r) - c11 G * c11 G := by
    rw [hc12, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e12 : G 1 2 = (G 0 1 / r) * (G 0 2 / r) - c11 G * c21 G := by
    have : c11 G * c21 G = schur G 1 2 := by unfold c21; field_simp
    rw [this, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e13 : G 1 3 = (G 0 1 / r) * (G 0 3 / r) - c11 G * c31 G := by
    have : c11 G * c31 G = schur G 1 3 := by unfold c31; field_simp
    rw [this, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e22 : G 2 2 = (G 0 2 / r) * (G 0 2 / r) - c21 G * c21 G - c22 G * c22 G := by
    rw [hc22, m2, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e23 : G 2 3 = (G 0 2 / r) * (G 0 3 / r) - c21 G * c31 G - c22 G * c32 G := by
    have : c22 G * c32 G = schur G 2 3 - c31 G * c21 G := by unfold c32; field_simp
    rw [this, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e33 : G 3 3 = (G 0 3 / r) * (G 0 3 / r) - c31 G * c31 G - c32 G * c32 G - c33 G * c33 G := by
    rw [hc32, m3, schur]; field_simp; rw [← hr2]; field_simp; ring
  have e01 : G 0 1 = r * (G 0 1 / r) := by field_simp
  have e02 : G 0 2 = r * (G 0 2 / r) := by field_simp
  have e03 : G 0 3 = r * (G 0 3 / r) := by field_simp
  have s10 := hsym 0 1
  have s20 := hsym 0 2
  have s30 := hsym 0 3
  have s21 := hsym 1 2
  have s31 := hsym 1 3
  have s32 := hsym 2 3
  rw [GU.Iso77.ηR_eq, ηr]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [gaugeP, ← hr] <;>
    linarith [hr2, e01, e02, e03, e11, e12, e13, e22, e23, e33, s10, s20, s30, s21, s31, s32]

/-! ### Openness and continuity -/

section Cont

lemma cG (i j : Fin 4) : Continuous fun G : M4 => G i j := continuous_apply_apply i j

def S0 : Set M4 := {G | 0 < G 0 0}
def S1 : Set M4 := {G | 0 < G 0 0 ∧ 0 < schur G 1 1}
def S2 : Set M4 := {G | 0 < G 0 0 ∧ 0 < schur G 1 1 ∧ 0 < m2 G}

lemma cschur (i j : Fin 4) : ContinuousOn (fun G => schur G i j) S0 :=
  (((cG 0 i).mul (cG 0 j)).continuousOn.div (cG 0 0).continuousOn fun _ h => ne_of_gt h).sub
    (cG i j).continuousOn

lemma S1_sub : S1 ⊆ S0 := fun _ h => h.1
lemma S2_sub : S2 ⊆ S1 := fun _ h => ⟨h.1, h.2.1⟩
lemma gauge_sub : gaugeSet ⊆ S2 := fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

lemma cc11 : ContinuousOn c11 S0 := Real.continuous_sqrt.comp_continuousOn (cschur 1 1)
lemma c11_ne {G : M4} (h : G ∈ S1) : c11 G ≠ 0 := (Real.sqrt_pos.mpr h.2).ne'
lemma cc21 : ContinuousOn c21 S1 :=
  ((cschur 1 2).mono S1_sub).div (cc11.mono S1_sub) fun _ h => c11_ne h
lemma cc31 : ContinuousOn c31 S1 :=
  ((cschur 1 3).mono S1_sub).div (cc11.mono S1_sub) fun _ h => c11_ne h
lemma cm2 : ContinuousOn m2 S1 := ((cschur 2 2).mono S1_sub).sub (cc21.pow 2)
lemma cc22 : ContinuousOn c22 S1 := Real.continuous_sqrt.comp_continuousOn cm2
lemma c22_ne {G : M4} (h : G ∈ S2) : c22 G ≠ 0 := (Real.sqrt_pos.mpr h.2.2).ne'
lemma cc32 : ContinuousOn c32 S2 :=
  (((cschur 2 3).mono (S2_sub.trans S1_sub)).sub ((cc31.mono S2_sub).mul (cc21.mono S2_sub))).div
    (cc22.mono S2_sub) fun _ h => c22_ne h
lemma cm3 : ContinuousOn m3 S2 :=
  (((cschur 3 3).mono (S2_sub.trans S1_sub)).sub ((cc31.mono S2_sub).pow 2)).sub (cc32.pow 2)
lemma cc33 : ContinuousOn c33 S2 := Real.continuous_sqrt.comp_continuousOn cm3

lemma isOpen_S0 : IsOpen S0 := isOpen_lt continuous_const (cG 0 0)
lemma isOpen_S1 : IsOpen S1 := by
  have := (cschur 1 1).isOpen_inter_preimage isOpen_S0 (isOpen_Ioi (a := (0 : ℝ)))
  exact this
lemma isOpen_S2 : IsOpen S2 := by
  have := cm2.isOpen_inter_preimage isOpen_S1 (isOpen_Ioi (a := (0 : ℝ)))
  convert this using 1
  ext G; exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **The gauge locus is open.** -/
theorem isOpen_gaugeSet : IsOpen gaugeSet := by
  have := cm3.isOpen_inter_preimage isOpen_S2 (isOpen_Ioi (a := (0 : ℝ)))
  convert this using 1
  ext G; exact ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩

/-- **The Cholesky factor is continuous on the gauge locus.** -/
theorem continuousOn_gaugeP : ContinuousOn gaugeP gaugeSet := by
  have hS : gaugeSet ⊆ S0 := gauge_sub.trans (S2_sub.trans S1_sub)
  have hS1 : gaugeSet ⊆ S1 := gauge_sub.trans S2_sub
  have hr : ContinuousOn (fun G : M4 => Real.sqrt (G 0 0)) gaugeSet :=
    (Real.continuous_sqrt.comp (cG 0 0)).continuousOn
  have hrn : ∀ G ∈ gaugeSet, Real.sqrt (G 0 0) ≠ 0 := fun G h => (Real.sqrt_pos.mpr h.1).ne'
  refine continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [gaugeP] <;> simp
  all_goals first
    | exact continuousOn_const
    | exact hr
    | exact (cG _ _).continuousOn.div hr hrn
    | exact cc11.mono hS
    | exact cc21.mono hS1
    | exact cc31.mono hS1
    | exact cc22.mono hS1
    | exact cc32.mono gauge_sub
    | exact cc33.mono gauge_sub

end Cont

/-- **`ηR` is in the gauge locus.** -/
lemma ηR_mem_gaugeSet : (ηR : M4) ∈ gaugeSet := by
  rw [GU.Iso77.ηR_eq]
  have e : ∀ i j : Fin 4, ηr i j = if i = j then (![1, -1, -1, -1] : Fin 4 → ℝ) i else 0 := fun i j => by
    simp [ηr, Matrix.diagonal_apply]
  have s11 : schur ηr 1 1 = 1 := by simp [schur, e]
  have s12 : schur ηr 1 2 = 0 := by simp [schur, e]
  have s13 : schur ηr 1 3 = 0 := by simp [schur, e]
  have s22 : schur ηr 2 2 = 1 := by simp [schur, e]
  have s23 : schur ηr 2 3 = 0 := by simp [schur, e]
  have s33 : schur ηr 3 3 = 1 := by simp [schur, e]
  have h21 : c21 ηr = 0 := by simp [c21, s12]
  have h31 : c31 ηr = 0 := by simp [c31, s13]
  have hm2 : m2 ηr = 1 := by simp [m2, s22, h21]
  have h32 : c32 ηr = 0 := by simp [c32, s23, h31]
  have hm3 : m3 ηr = 1 := by simp [m3, s33, h31, h32]
  refine ⟨by simp [e], by rw [s11]; norm_num, by rw [hm2]; norm_num, by rw [hm3]; norm_num⟩

end

end GU.Library
