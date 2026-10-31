import GU.Bundle.FramePrincipal
import GU.Bundle.AdaptedFrames

/-!
# Phase 3, item 3: the block group and its action on adapted frames

`Gblk ≤ O77`: matrices with no entries between the horizontal indices `SH = {6, 11, 12, 13}` and
the rest. `η₇₇` has signature (1,3) on `SH` and (6,4) on `SHᶜ = {0..5} ∪ {7..10}`
(`SH_signature`), so `Gblk` is the block group `O(6,4) × O(1,3)` in the `Φ` basis (this
identification is by these index counts; no `MulEquiv` is stated). Results:
* `Gblk` is closed (`isClosed_Gblk`) and preserves adapted frames (`ractM_mem_AFr_blk`);
* an `O77`-element relating two adapted frames lies in `Gblk` (`mem_Gblk_of_ractM_mem_AFr`), so
  adapted frames over one point differ by `Gblk` (`adapted_fibre_transitive`);
* the aligned Pati–Salam groups lie in `Gblk` (`PS6'_le_Gblk`, `PS4'_le_Gblk`).
Freeness (`ractM_free`) and existence (`exists_adapted_frame`) are imported.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric
open scoped ContDiff Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Block condition: no entries between `SH` and its complement. -/
def IsBlk (g : Mat 14) : Prop := ∀ h j : Fin 14, (h ∈ SH ↔ j ∉ SH) → g h j = 0

/-- **Signature bookkeeping**: on `SH` the form `η₇₇` has one `+` and three `−` (signature
(1,3), the `H*` factor); on `SHᶜ` six `+` and four `−` (signature (6,4), the `V` factor). -/
theorem SH_signature :
    (SH.filter (fun i : Fin 14 => (i : ℕ) < 7)).card = 1 ∧
    (SH.filter (fun i : Fin 14 => ¬ (i : ℕ) < 7)).card = 3 ∧
    (SHᶜ.filter (fun i : Fin 14 => (i : ℕ) < 7)).card = 6 ∧
    (SHᶜ.filter (fun i : Fin 14 => ¬ (i : ℕ) < 7)).card = 4 := by decide

/-- Sign of `η₇₇`. -/
noncomputable def sgn77 (i : Fin 14) : ℝ := if (i : ℕ) < 7 then 1 else -1

lemma invM_apply (A : Mat 14) (h j : Fin 14) :
    invM η77 A h j = sgn77 h * A j h * sgn77 j := by
  have e : ∀ i j, η77 i j = if i = j then (if (i : ℕ) < 7 then (1 : ℝ) else -1) else 0 :=
    η77_apply
  show (Matrix.of η77 * (Matrix.of A)ᵀ * Matrix.of η77) h j = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, e, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_zero, Finset.sum_ite_eq',
    sgn77]

lemma isBlk_mul {A B : Mat 14} (hA : IsBlk A) (hB : IsBlk B) : IsBlk (mulM A B) := by
  intro h j hhj
  rw [mulM_eq]
  show ∑ k, A h k * B k j = 0
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ SH
  · by_cases hh : h ∈ SH
    · rw [hB k j (by tauto), mul_zero]
    · rw [hA h k (by tauto), zero_mul]
  · by_cases hh : h ∈ SH
    · rw [hA h k (by tauto), zero_mul]
    · rw [hB k j (by tauto), mul_zero]

lemma isBlk_one : IsBlk (Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)) := fun h j hhj => by
  show (Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)) h j = 0
  have hne : h ≠ j := by rintro rfl; tauto
  simp [hne]

lemma isBlk_η77 : IsBlk η77 := fun h j hhj => by
  have hne : h ≠ j := by rintro rfl; tauto
  have := η77_apply h j
  rw [if_neg hne] at this
  exact this

lemma isBlk_add {A B : Mat 14} (hA : IsBlk A) (hB : IsBlk B) : IsBlk (A + B) := fun h j hhj => by
  show A h j + B h j = 0
  rw [hA h j hhj, hB h j hhj, add_zero]

/-- **The block subgroup** `Gblk ≤ O77`: block-diagonal for `SH ⊔ SHᶜ`, i.e. `O(6,4) × O(1,3)` in
the `Φ` basis (`SH_signature`). -/
noncomputable def Gblk : Subgroup O77 where
  carrier := {g | IsBlk (g : Mat 14)}
  one_mem' := isBlk_one
  mul_mem' := fun {a b} ha hb => isBlk_mul ha hb
  inv_mem' := fun {a} ha h j hhj => by
    show (invM η77 (a : Mat 14)) h j = 0
    rw [invM_apply, ha j h (by tauto), mul_zero, zero_mul]

lemma mem_Gblk {g : O77} : g ∈ Gblk ↔ IsBlk (g : Mat 14) := Iff.rfl

lemma mulVec_single_apply (g : Mat 14) (j k : Fin 14) :
    (Matrix.of g *ᵥ Pi.single j 1) k = g k j := by
  rw [mulVec_single_one]; rfl

/-- An adapted frame sends vectors supported off `SH` into `V`. -/
lemma adapted_snd {h : HomF} (ha : Adapted h) {v : Fin 14 → ℝ} (hv : ∀ k ∈ SH, v k = 0) :
    (h v).2 = 0 := by
  rw [← Finset.univ_sum_single v, map_sum, Prod.snd_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ SH
  · rw [hv k hk, Pi.single_zero, map_zero]; rfl
  · rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 14 → ℝ) by
      ext i; by_cases e : i = k <;> simp [e], map_smul, Prod.smul_snd, ha.2 k hk, smul_zero]

/-- An adapted frame sends vectors supported on `SH` into `H*`. -/
lemma adapted_fst {h : HomF} (ha : Adapted h) {v : Fin 14 → ℝ} (hv : ∀ k ∉ SH, v k = 0) :
    (h v).1 = 0 := by
  rw [← Finset.univ_sum_single v, map_sum, Prod.fst_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ SH
  · rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 14 → ℝ) by
      ext i; by_cases e : i = k <;> simp [e], map_smul, Prod.smul_fst, ha.1 k hk, smul_zero]
  · rw [hv k hk, Pi.single_zero, map_zero]; rfl

/-- Block matrices preserve adaptedness. -/
lemma adapted_comp_blk {h : HomF} (ha : Adapted h) {g : Mat 14} (hg : IsBlk g) :
    Adapted (h.comp (matCLM g)) :=
  ⟨fun j hj => adapted_fst ha fun k hk => by
    show (Matrix.of g *ᵥ Pi.single j 1) k = 0; rw [mulVec_single_apply]; exact hg k j (by tauto),
   fun j hj => adapted_snd ha fun k hk => by
    show (Matrix.of g *ᵥ Pi.single j 1) k = 0; rw [mulVec_single_apply]; exact hg k j (by tauto)⟩

/-- **The block group preserves adapted frames.** -/
theorem ractM_mem_AFr_blk {q : HomTotM X} (hq : q ∈ AFr X) {g : O77} (hg : g ∈ Gblk) :
    ractM q g ∈ AFr X :=
  ⟨ractM_mem_OFr hq.1 g, adapted_comp_blk hq.2 hg⟩

/-- Orthonormal frames are injective. -/
lemma frame_injective {q : HomTotM X} (hq : q ∈ orthoSetM) :
    Function.Injective (show HomF from q.2) := by
  rw [mem_orthoSetM_iff_mat] at hq
  set M := Matrix.of (homMat.symm (show HomF from q.2))
  have hM : Mᵀ * Matrix.of (Gchim (((q.proj : Sym2TX X).2 : Fin 10 → ℝ))) * M = Matrix.of η77 := by
    rw [← bil_eq_mat]; exact congrArg Matrix.of hq
  have hu : IsUnit M.det := isUnit_frame hM
  intro x y hxy
  have hxy' : homMat (homMat.symm (show HomF from q.2)) x =
      homMat (homMat.symm (show HomF from q.2)) y := by
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact hxy
  rw [homMat_apply, homMat_apply] at hxy'
  have h2 : M *ᵥ x = M *ᵥ y := ΦL.injective hxy'
  have := congrArg (M⁻¹ *ᵥ ·) h2
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu] using this

/-- If `g ∈ O77` carries an adapted frame to an adapted frame, then `g ∈ Gblk`. With
`O77`-transitivity this gives `Gblk`-transitivity (`adapted_fibre_transitive`). -/
theorem mem_Gblk_of_ractM_mem_AFr {q : HomTotM X} (hq : q ∈ AFr X) {g : O77}
    (hg : ractM q g ∈ AFr X) : g ∈ Gblk := by
  obtain ⟨hO, ha⟩ := hq
  have hO' : q ∈ orthoSetM := by rw [← levelSet_Fframe]; exact hO
  have ha' := hg.2
  set h := (show HomF from q.2)
  intro k j hkj
  set v := Matrix.of (g : Mat 14) *ᵥ Pi.single j 1
  have hv : ∀ k, v k = (g : Mat 14) k j := mulVec_single_apply _ j
  have hhv : h v = ((show HomF from (ractM q g).2) (Pi.single j 1)) := rfl
  -- split `v` into its `SH` and off-`SH` parts
  let vH : Fin 14 → ℝ := fun i => if i ∈ SH then v i else 0
  let vV : Fin 14 → ℝ := fun i => if i ∈ SH then 0 else v i
  have hsplit : v = vH + vV := by ext i; by_cases e : i ∈ SH <;> simp [vH, vV, e]
  by_cases hj : j ∈ SH
  · -- then `k ∉ SH`; the `V`-part of `h v` vanishes, so `vV = 0`
    have hk : k ∉ SH := by tauto
    have h1 : (h v).1 = 0 := by rw [hhv]; exact ha'.1 j hj
    have h1' : (h vV).1 = 0 := by
      have := h1
      rw [hsplit, map_add, Prod.fst_add, adapted_fst ha (v := vH) (fun i hi => by simp [vH, hi]),
        zero_add] at this
      exact this
    have h2' : (h vV).2 = 0 := adapted_snd ha fun i hi => by simp [vV, hi]
    have h0 : vV = 0 := frame_injective hO' ((Prod.ext h1' h2').trans (map_zero h).symm)
    have := congrFun h0 k
    simp only [vV, hk, Pi.zero_apply] at this
    rw [← hv]; exact this
  · have hk : k ∈ SH := by tauto
    have h1 : (h v).2 = 0 := by rw [hhv]; exact ha'.2 j hj
    have h1' : (h vH).2 = 0 := by
      have := h1
      rw [hsplit, map_add, Prod.snd_add, adapted_snd ha (v := vV) (fun i hi => by simp [vV, hi]),
        add_zero] at this
      exact this
    have h2' : (h vH).1 = 0 := adapted_fst ha fun i hi => by simp [vH, hi]
    have h0 : vH = 0 := frame_injective hO' ((Prod.ext h2' h1').trans (map_zero h).symm)
    have := congrFun h0 k
    simp only [vH, hk, Pi.zero_apply] at this
    rw [← hv]; exact this

/-- **Fibrewise transitivity of `Gblk` on adapted frames.** -/
theorem adapted_fibre_transitive {q q' : HomTotM X} (hq : q ∈ AFr X) (hq' : q' ∈ AFr X)
    (hp : q.proj = q'.proj) : ∃ g ∈ Gblk, ractM q g = q' := by
  have h1 : q ∈ orthoSetM := by rw [← levelSet_Fframe]; exact hq.1
  have h2 : q' ∈ orthoSetM := by rw [← levelSet_Fframe]; exact hq'.1
  obtain ⟨g, hg⟩ := ractM_transitive' h1 h2 hp
  exact ⟨g, mem_Gblk_of_ractM_mem_AFr hq (hg ▸ hq'), hg⟩

/-- `Gblk` is closed in `O77`. -/
theorem isClosed_Gblk : IsClosed (Gblk : Set O77) := by
  have : (Gblk : Set O77) = ⋂ h : Fin 14, ⋂ j : Fin 14, ⋂ (_ : (h ∈ SH ↔ j ∉ SH)),
      {g : O77 | (g : Mat 14) h j = 0} := by
    ext g; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact Iff.rfl
  rw [this]
  refine isClosed_iInter fun h => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_apply_apply h j).comp continuous_subtype_val) continuous_const

/-- Elements fixing `H*` pointwise are block. -/
lemma blk_of_fixes_H {g : O77}
    (hfix : ∀ h ∈ SH, Matrix.of (g : Mat 14) *ᵥ Pi.single h 1 = Pi.single h 1) : g ∈ Gblk := by
  intro k j hkj
  by_cases hj : j ∈ SH
  · have hk : k ∉ SH := by tauto
    have := congrFun (hfix j hj) k
    rw [mulVec_single_apply, Pi.single_apply] at this
    simpa [show k ≠ j from fun e => hk (e ▸ hj)] using this
  · have hk : k ∈ SH := by tauto
    rw [← mulVec_single_apply (g : Mat 14) j k]; exact vert_coord_zero hfix hj hk

/-- **The aligned Pati–Salam groups lie in the block group.** -/
theorem PS6'_le_Gblk : PS6' ≤ Gblk := fun _ hg => blk_of_fixes_H fun _ hh => PS6'_fixes_H hg hh
theorem PS4'_le_Gblk : PS4' ≤ Gblk := fun _ hg => blk_of_fixes_H fun _ hh => PS4'_fixes_H hg hh

end GU.Library
