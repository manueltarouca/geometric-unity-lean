import GU.Bundle.ChimReduction

/-!
# Frames adapted to the chimeric splitting `C = V ⊕ H*`

A frame `h : ℝ¹⁴ →L CFib` is **adapted** if it sends the horizontal basis vectors (`SH`; their
`Φ`-images lie in `H*`, `ΦL_horiz`) into `H*` and the others into `V` (`Adapted`). `AFr` = adapted
orthonormal frames, a canonically defined subset of `OFr`.
* **`exists_adapted_frame`**: over every (1,3) point `y` (the `Y13` predicate) there is an adapted
  orthonormal frame, namely `TP_P ∘ Φ` (`TP_isometry`; `TP` preserves `V` and `H*`).
* **`ractM_mem_AFr`**: isometries fixing `H*` pointwise preserve adapted frames; in particular the
  `Φ`-aligned Pati–Salam groups (`ractM_mem_AFr_PS6'`, `_PS4'`).
**Not shown**: stability under the full block group `O(6,4) × O(1,3)`, fibrewise transitivity of
that group, smoothness, or any principal-bundle structure; so this is not (yet) a reduction of the
structure group in the bundle-theoretic sense.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric
open scoped ContDiff

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- A frame adapted to `V ⊕ H*`. -/
def Adapted (h : HomF) : Prop :=
  (∀ j ∈ SH, (h (Pi.single j 1)).1 = 0) ∧ (∀ j ∉ SH, (h (Pi.single j 1)).2 = 0)

/-- Adapted orthonormal frames. -/
def AFr (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Set (HomTotM X) :=
  {q | q ∈ OFr X ∧ Adapted (show HomF from q.2)}

lemma TP_fst_zero (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) {u : CFib} (hu : u.1 = 0) :
    (TP P hP u).1 = 0 := by
  show symCoords (P * symMat u.1 * Pᵀ) = 0
  rw [hu]
  have : symMat (0 : Fin 10 → ℝ) = 0 := by ext i j; rfl
  rw [this, Matrix.mul_zero, Matrix.zero_mul]
  ext k; simp [symCoords]

lemma TP_snd_zero (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) {u : CFib} (hu : u.2 = 0) :
    (TP P hP u).2 = 0 := by
  show u.2.comp (toCLM P⁻¹) = 0
  rw [hu, ContinuousLinearMap.zero_comp]

/-- The frame `TP_P ∘ Φ`. -/
noncomputable def tpFrame (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) : HomF :=
  (LinearMap.toContinuousLinearMap (TP P hP).toLinearMap).comp (ΦL : R14 →L[ℝ] CFib)

lemma tpFrame_apply (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (x : R14) :
    tpFrame P hP x = TP P hP (ΦL x) := rfl

lemma tpFrame_adapted (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) : Adapted (tpFrame P hP) :=
  ⟨fun j hj => by rw [tpFrame_apply]; exact TP_fst_zero P hP (ΦL_horiz j hj),
   fun j hj => by rw [tpFrame_apply]; exact TP_snd_zero P hP (ΦL_vert j hj)⟩

/-- **Adapted orthonormal frames exist over every (1,3) point of `Y`.** -/
theorem exists_adapted_frame (y : Yobs X)
    (hy : ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ) :
    ∃ q : HomTotM X, q.proj = y ∧ q ∈ AFr X := by
  obtain ⟨P, hP, hG⟩ := hy
  refine ⟨⟨y, tpFrame P hP⟩, rfl, ?_, tpFrame_adapted P hP⟩
  show _ ∈ levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩
  rw [levelSet_Fframe]
  intro x x'
  show Bmod (Gpt y) (tpFrame P hP x) (tpFrame P hP x') = _
  rw [hG, tpFrame_apply, tpFrame_apply, TP_isometry, Bη_Φ]

lemma Bm_single (v : Fin 14 → ℝ) (h : Fin 14) :
    Bm v (Pi.single h 1) = v h * (if (h : ℕ) < 7 then 1 else -1) := by
  unfold Bm
  rw [mulVec_single_one]
  simp only [dotProduct, Matrix.col_apply, η77_apply]
  rw [Finset.sum_eq_single h (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- An isometry fixing `H*` pointwise keeps vertical basis vectors vertical. -/
lemma vert_coord_zero {g : O77} (hfix : ∀ h ∈ SH, Matrix.of (g : Mat 14) *ᵥ Pi.single h 1 = Pi.single h 1)
    {j : Fin 14} (hj : j ∉ SH) {h : Fin 14} (hh : h ∈ SH) :
    (Matrix.of (g : Mat 14) *ᵥ Pi.single j 1) h = 0 := by
  have hB := (mem_Orth_iff_Bm (g : Mat 14)).mp g.2 (Pi.single j 1) (Pi.single h 1)
  rw [hfix h hh, Bm_single, Bm_single] at hB
  have hjh : j ≠ h := fun e => hj (e ▸ hh)
  have hsign : (if (h : ℕ) < 7 then (1 : ℝ) else -1) ≠ 0 := by split_ifs <;> norm_num
  rw [Pi.single_apply, if_neg hjh.symm, zero_mul] at hB
  exact (mul_eq_zero.mp hB).resolve_right hsign

/-- **Isometries fixing `H*` pointwise preserve adapted frames.** -/
theorem ractM_mem_AFr {q : HomTotM X} (hq : q ∈ AFr X) {g : O77}
    (hfix : ∀ h ∈ SH, Matrix.of (g : Mat 14) *ᵥ Pi.single h 1 = Pi.single h 1) :
    ractM q g ∈ AFr X := by
  obtain ⟨hO, hH, hV⟩ := hq
  refine ⟨ractM_mem_OFr hO g, fun j hj => ?_, fun j hj => ?_⟩
  · show ((show HomF from q.2) (matCLM g (Pi.single j 1))).1 = 0
    rw [matCLM_apply, hfix j hj]; exact hH j hj
  · show ((show HomF from q.2) (matCLM g (Pi.single j 1))).2 = 0
    rw [matCLM_apply]
    set v := Matrix.of (g : Mat 14) *ᵥ Pi.single j 1
    rw [← Finset.univ_sum_single v, map_sum, Prod.snd_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ SH
    · have hz : v k = 0 := vert_coord_zero hfix hj hk
      rw [hz, Pi.single_zero, map_zero]; rfl
    · rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 14 → ℝ) by
        ext i; by_cases h : i = k <;> simp [h], map_smul, Prod.smul_snd, hV k hk, smul_zero]

/-- **The aligned Pati–Salam groups act on the adapted (reduced) frame bundle.** -/
theorem ractM_mem_AFr_PS6' {q : HomTotM X} (hq : q ∈ AFr X) {g : O77} (hg : g ∈ PS6') :
    ractM q g ∈ AFr X := ractM_mem_AFr hq fun _ hh => PS6'_fixes_H hg hh

theorem ractM_mem_AFr_PS4' {q : HomTotM X} (hq : q ∈ AFr X) {g : O77} (hg : g ∈ PS4') :
    ractM q g ∈ AFr X := ractM_mem_AFr hq fun _ hh => PS4'_fixes_H hg hh

end GU.Library
