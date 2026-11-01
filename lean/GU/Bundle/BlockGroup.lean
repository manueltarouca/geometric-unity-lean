import GU.Bundle.AdaptedGram

/-!
# The block Lie group `O(6,4) × O(1,3)` and its block homomorphism into `O(7,7)`

`O64 = O(η₆₄)`, `O13 = O(η₁₃)` are Lie groups (`lieGroup_orth`); `Gp = O64 × O13` is a Lie group
(product). `e14 : Fin 10 ⊕ Fin 4 ≃ Fin 14` sends the summands to `SHᶜ` and `SH` (order preserving,
`vI`, `hI`), and `blkM A B = (fromBlocks A 0 0 B)` reindexed by `e14`. Then:
* `η₇₇ = blkM η₆₄ η₁₃` (`η77_blk`), so `blkM` maps `O64 × O13` into `O77`;
* **`ιB : Gp →* O77`**, injective (`ιB_injective`), smooth (`contMDiff_ιB`), with range the closed
  subgroup `Gblk` (`range_ιB`); a block inverse `ιinv` with `ιB (ιinv g) = g` on `Gblk`
  (`ιB_ιinv`), multiplicative there (`ιinv_mul`), and smooth along maps with values in `Gblk`
  (`contMDiffOn_ιinv_comp`). (That `ιB` is an immersion is not stated.)
-/

namespace GU.Library

open Matrix GU
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### The groups -/

noncomputable abbrev η64 : Mat 10 := ηSig 6 4
noncomputable abbrev η13 : Mat 4 := ηSig 1 3
abbrev O64 := Orth η64 (ηSig_mem 6 4)
abbrev O13 := Orth η13 (ηSig_mem 1 3)

noncomputable instance : Group O64 := orthGroup (ηSig_mem 6 4) (ηSig_sq 6 4)
noncomputable instance : ChartedSpace (Fin (fibreDim (Mat 10) (symS 10)) → ℝ) O64 :=
  smoothLevelCharted (orth_submersive _ (ηSig_mem 6 4) (ηSig_sq 6 4))
instance : LieGroup 𝓘(ℝ, Fin (fibreDim (Mat 10) (symS 10)) → ℝ) ∞ O64 :=
  lieGroup_orth (ηSig_mem 6 4) (ηSig_sq 6 4)

noncomputable instance : Group O13 := orthGroup (ηSig_mem 1 3) (ηSig_sq 1 3)
noncomputable instance : ChartedSpace (Fin (fibreDim (Mat 4) (symS 4)) → ℝ) O13 :=
  smoothLevelCharted (orth_submersive _ (ηSig_mem 1 3) (ηSig_sq 1 3))
instance : LieGroup 𝓘(ℝ, Fin (fibreDim (Mat 4) (symS 4)) → ℝ) ∞ O13 :=
  lieGroup_orth (ηSig_mem 1 3) (ηSig_sq 1 3)

/-- **The block group** `O(6,4) × O(1,3)`. -/
abbrev Gp := O64 × O13

/-- Its model with corners. -/
abbrev IGp := 𝓘(ℝ, Fin (fibreDim (Mat 10) (symS 10)) → ℝ).prod 𝓘(ℝ, Fin (fibreDim (Mat 4) (symS 4)) → ℝ)

example : LieGroup IGp ∞ Gp := inferInstance

/-! ### Block matrices -/

/-- `Fin 10 ⊕ Fin 4 ≃ Fin 14` onto `SHᶜ ⊕ SH`. -/
def e14 : Fin 10 ⊕ Fin 4 ≃ Fin 14 where
  toFun := Sum.elim vI hI
  invFun i := if i ∈ SH then Sum.inr (hInv i) else Sum.inl (vInv i)
  left_inv x := by rcases x with a | a <;> revert a <;> decide
  right_inv i := by revert i; decide

lemma e14_symm_of_mem {i : Fin 14} (hi : i ∈ SH) : e14.symm i = Sum.inr (hInv i) := by
  simp only [e14, Equiv.coe_fn_symm_mk, hi, if_true]
lemma e14_symm_of_not_mem {i : Fin 14} (hi : i ∉ SH) : e14.symm i = Sum.inl (vInv i) := by
  simp only [e14, Equiv.coe_fn_symm_mk, hi, if_false]

/-- The block-diagonal matrix with blocks `A` (on `SHᶜ`) and `B` (on `SH`). -/
def blkM (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 14) (Fin 14) ℝ :=
  (fromBlocks A 0 0 B).submatrix e14.symm e14.symm

lemma blkM_mul (A A' : Matrix (Fin 10) (Fin 10) ℝ) (B B' : Matrix (Fin 4) (Fin 4) ℝ) :
    blkM A B * blkM A' B' = blkM (A * A') (B * B') := by
  unfold blkM
  rw [submatrix_mul_equiv, fromBlocks_multiply]; simp

lemma blkM_transpose (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (blkM A B)ᵀ = blkM Aᵀ Bᵀ := by
  unfold blkM; rw [transpose_submatrix, fromBlocks_transpose]; simp

lemma blkM_one : blkM 1 1 = 1 := by
  unfold blkM; rw [fromBlocks_one, submatrix_one_equiv]

lemma blkM_inj {A A' : Matrix (Fin 10) (Fin 10) ℝ} {B B' : Matrix (Fin 4) (Fin 4) ℝ}
    (h : blkM A B = blkM A' B') : A = A' ∧ B = B' := by
  have h' : fromBlocks A 0 0 B = fromBlocks A' 0 0 B' := by
    have := congrArg (fun M => M.submatrix e14 e14) h
    simpa [blkM] using this
  exact ⟨(fromBlocks_inj.mp h').1, (fromBlocks_inj.mp h').2.2.2⟩

lemma blkM_vv (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 10) :
    blkM A B (vI a) (vI b) = A a b := by
  simp [blkM, e14_symm_of_not_mem (vI_not_mem a), e14_symm_of_not_mem (vI_not_mem b), vInv_vI]
lemma blkM_hh (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4) :
    blkM A B (hI a) (hI b) = B a b := by
  simp [blkM, e14_symm_of_mem (hI_mem a), e14_symm_of_mem (hI_mem b), hInv_hI]

lemma isBlk_blkM (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    IsBlk (Matrix.of.symm (blkM A B)) := by
  intro i j hij
  show blkM A B i j = 0
  by_cases hi : i ∈ SH
  · have hj : j ∉ SH := hij.mp hi
    simp [blkM, e14_symm_of_mem hi, e14_symm_of_not_mem hj]
  · have hj : j ∈ SH := by tauto
    simp [blkM, e14_symm_of_mem hj, e14_symm_of_not_mem hi]

/-- `η₇₇` is block-diagonal with blocks `η₆₄`, `η₁₃`. -/
lemma η77_blk : Matrix.of η77 = blkM (Matrix.of η64) (Matrix.of η13) := by
  have h1 : Matrix.of η77 = Matrix.diagonal fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1 := rfl
  have h2 : Matrix.of η64 = Matrix.diagonal fun i : Fin 10 => if (i : ℕ) < 6 then (1 : ℝ) else -1 := rfl
  have h3 : Matrix.of η13 = Matrix.diagonal fun i : Fin 4 => if (i : ℕ) < 1 then (1 : ℝ) else -1 := rfl
  rw [h1, h2, h3, blkM, fromBlocks_diagonal, submatrix_diagonal_equiv]
  congr 1; funext i
  by_cases hi : i ∈ SH
  · rw [Function.comp_apply, e14_symm_of_mem hi, Sum.elim_inr]
    have h := (show ∀ i : Fin 14, i ∈ SH → ((i : ℕ) < 7 ↔ ((hInv i : ℕ) < 1)) by decide) i hi
    simp only [h]
  · rw [Function.comp_apply, e14_symm_of_not_mem hi, Sum.elim_inl]
    have h := (show ∀ i : Fin 14, i ∉ SH → ((i : ℕ) < 7 ↔ ((vInv i : ℕ) < 6)) by decide) i hi
    simp only [h]

/-- Block matrices of orthogonal blocks are orthogonal, and conversely. -/
lemma blkM_orth_iff (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (blkM A B)ᵀ * Matrix.of η77 * blkM A B = Matrix.of η77 ↔
      Aᵀ * Matrix.of η64 * A = Matrix.of η64 ∧ Bᵀ * Matrix.of η13 * B = Matrix.of η13 := by
  rw [η77_blk, blkM_transpose, blkM_mul, blkM_mul]
  exact ⟨fun h => blkM_inj h, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

lemma blkM_apply (A : Matrix (Fin 10) (Fin 10) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 14) :
    blkM A B i j = if i ∈ SH then (if j ∈ SH then B (hInv i) (hInv j) else 0)
      else (if j ∈ SH then 0 else A (vInv i) (vInv j)) := by
  by_cases hi : i ∈ SH <;> by_cases hj : j ∈ SH <;>
    simp [blkM, hi, hj, e14_symm_of_mem, e14_symm_of_not_mem]

/-! ### The embedding `ιB : O(6,4) × O(1,3) → O(7,7)` -/

/-- The block matrix of `g ∈ Gp`. -/
def ιBmat (g : Gp) : Mat 14 :=
  Matrix.of.symm (blkM (Matrix.of (g.1 : Mat 10)) (Matrix.of (g.2 : Mat 4)))

lemma ιBmat_mem (g : Gp) : ιBmat g ∈ O77 := by
  rw [mem_Orth_iff_mat]
  show (blkM _ _)ᵀ * Matrix.of η77 * blkM _ _ = Matrix.of η77
  rw [blkM_orth_iff]
  exact ⟨(mem_Orth_iff_mat _ (ηSig_mem 6 4) _).mp g.1.2, (mem_Orth_iff_mat _ (ηSig_mem 1 3) _).mp g.2.2⟩

/-- **The block homomorphism** `O(6,4) × O(1,3) →* O(7,7)` (injective, `ιB_injective`). -/
def ιB : Gp →* O77 where
  toFun g := ⟨ιBmat g, ιBmat_mem g⟩
  map_one' := by
    apply Subtype.ext
    show Matrix.of.symm (blkM (Matrix.of (Matrix.of.symm 1)) (Matrix.of (Matrix.of.symm 1))) =
      Matrix.of.symm 1
    simp only [Equiv.apply_symm_apply, blkM_one]
  map_mul' g h := by
    apply Subtype.ext
    show Matrix.of.symm (blkM (Matrix.of (mulM (g.1 : Mat 10) h.1)) (Matrix.of (mulM (g.2 : Mat 4) h.2))) =
      mulM (ιBmat g) (ιBmat h)
    simp only [mulM, ιBmat, Equiv.apply_symm_apply, blkM_mul]

lemma ιB_val (g : Gp) : ((ιB g : O77) : Mat 14) = ιBmat g := rfl

lemma ιB_injective : Function.Injective ιB := by
  intro g h hgh
  have := blkM_inj (Matrix.of.symm.injective (congrArg Subtype.val hgh))
  exact Prod.ext (Subtype.ext (Matrix.of.injective this.1)) (Subtype.ext (Matrix.of.injective this.2))

lemma ιB_mem_Gblk (g : Gp) : ιB g ∈ Gblk := isBlk_blkM _ _

/-! ### The block inverse -/

/-- Reindexed matrix of `g`. -/
def reixM (g : Mat 14) : Matrix (Fin 10 ⊕ Fin 4) (Fin 10 ⊕ Fin 4) ℝ :=
  (Matrix.of g).submatrix e14 e14

lemma of_eq_blkM {g : Mat 14} (hg : IsBlk g) :
    Matrix.of g = blkM (reixM g).toBlocks₁₁ (reixM g).toBlocks₂₂ := by
  have h12 : (reixM g).toBlocks₁₂ = 0 := by
    ext a b; exact hg (vI a) (hI b) (by simp [vI_not_mem, hI_mem])
  have h21 : (reixM g).toBlocks₂₁ = 0 := by
    ext a b; exact hg (hI a) (vI b) (by simp [vI_not_mem, hI_mem])
  unfold blkM
  rw [← h12, ← h21, fromBlocks_toBlocks]
  ext i j; simp [reixM]

lemma blocks_orth {g : O77} (hg : g ∈ Gblk) :
    ((reixM g).toBlocks₁₁)ᵀ * Matrix.of η64 * (reixM g).toBlocks₁₁ = Matrix.of η64 ∧
    ((reixM g).toBlocks₂₂)ᵀ * Matrix.of η13 * (reixM g).toBlocks₂₂ = Matrix.of η13 := by
  have h := (mem_Orth_iff_mat _ (ηSig_mem 7 7) _).mp g.2
  rw [of_eq_blkM hg] at h
  exact (blkM_orth_iff _ _).mp h

open Classical in
/-- **The block inverse** `Gblk → O(6,4) × O(1,3)` (`1` off `Gblk`). -/
def ιinv (g : O77) : Gp :=
  if hg : g ∈ Gblk then
    (⟨Matrix.of.symm (reixM g).toBlocks₁₁, (mem_Orth_iff_mat _ (ηSig_mem 6 4) _).mpr (blocks_orth hg).1⟩,
     ⟨Matrix.of.symm (reixM g).toBlocks₂₂, (mem_Orth_iff_mat _ (ηSig_mem 1 3) _).mpr (blocks_orth hg).2⟩)
  else 1

lemma ιB_ιinv {g : O77} (hg : g ∈ Gblk) : ιB (ιinv g) = g := by
  apply Subtype.ext
  rw [ιB_val, ιinv, dif_pos hg]
  show Matrix.of.symm (blkM (Matrix.of (Matrix.of.symm _)) (Matrix.of (Matrix.of.symm _))) = _
  simp only [Equiv.apply_symm_apply]
  rw [← of_eq_blkM hg]; rfl

lemma ιinv_ιB (g : Gp) : ιinv (ιB g) = g :=
  ιB_injective (ιB_ιinv (ιB_mem_Gblk g))

lemma ιinv_mul {g h : O77} (hg : g ∈ Gblk) (hh : h ∈ Gblk) : ιinv (g * h) = ιinv g * ιinv h :=
  ιB_injective (by rw [map_mul, ιB_ιinv hg, ιB_ιinv hh, ιB_ιinv (Gblk.mul_mem hg hh)])

lemma ιinv_one : ιinv (1 : O77) = 1 := ιB_injective (by rw [map_one, ιB_ιinv Gblk.one_mem])

theorem range_ιB : ιB.range = Gblk := by
  ext g
  exact ⟨fun ⟨x, hx⟩ => hx ▸ ιB_mem_Gblk x, fun hg => ⟨ιinv g, ιB_ιinv hg⟩⟩

/-! ### Smoothness -/

theorem contMDiff_ιB : ContMDiff IGp 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ ιB := by
  rw [contMDiff_levelSet_iff (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))]
  have hO1 : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 10) (symS 10)) → ℝ) 𝓘(ℝ, Mat 10) ∞
      (Subtype.val : O64 → Mat 10) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 6 4) (ηSig_sq 6 4))
  have hO2 : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 4) (symS 4)) → ℝ) 𝓘(ℝ, Mat 4) ∞
      (Subtype.val : O13 → Mat 4) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 1 3) (ηSig_sq 1 3))
  have hv1 : ContMDiff IGp 𝓘(ℝ, Mat 10) ∞ (fun g : Gp => (g.1 : Mat 10)) := hO1.comp contMDiff_fst
  have hv2 : ContMDiff IGp 𝓘(ℝ, Mat 4) ∞ (fun g : Gp => (g.2 : Mat 4)) := hO2.comp contMDiff_snd
  refine contMDiff_pi_space.mpr fun i => contMDiff_pi_space.mpr fun j => ?_
  have e : (fun g : Gp => ((ιB g : O77) : Mat 14) i j) = fun g =>
      if i ∈ SH then (if j ∈ SH then (g.2 : Mat 4) (hInv i) (hInv j) else 0)
      else (if j ∈ SH then 0 else (g.1 : Mat 10) (vInv i) (vInv j)) := by
    funext g; exact blkM_apply _ _ i j
  rw [e]
  split_ifs
  · exact contMDiff_pi_space.mp (contMDiff_pi_space.mp hv2 _) _
  · exact contMDiff_const
  · exact contMDiff_const
  · exact contMDiff_pi_space.mp (contMDiff_pi_space.mp hv1 _) _

/-- **Smoothness of the block inverse** along maps with values in `Gblk`. -/
theorem contMDiffOn_ιinv_comp {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HM] [TopologicalSpace M] [ChartedSpace HM M] {I : ModelWithCorners ℝ EM HM}
    [IsManifold I ∞ M] {F : M → O77} {t : Set M} (hF : ContMDiffOn I 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ F t)
    (hmem : ∀ x ∈ t, F x ∈ Gblk) : ContMDiffOn I IGp ∞ (fun x => ιinv (F x)) t := by
  have hO : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Mat 14) ∞
      (Subtype.val : O77 → Mat 14) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
  have hv := hO.comp_contMDiffOn hF
  have hent : ∀ i j : Fin 14, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => (F x : Mat 14) i j) t := fun i j =>
    contMDiffOn_pi_space.mp (contMDiffOn_pi_space.mp hv i) j
  refine ContMDiffOn.prodMk ?_ ?_
  · rw [contMDiffOn_levelSet_iff (orth_submersive _ (ηSig_mem 6 4) (ηSig_sq 6 4))]
    refine (contMDiffOn_pi_space.mpr fun a => contMDiffOn_pi_space.mpr fun b => hent (vI a) (vI b)).congr
      fun x hx => ?_
    show ((ιinv (F x)).1 : Mat 10) = fun a b => (F x : Mat 14) (vI a) (vI b)
    rw [ιinv, dif_pos (hmem x hx)]; rfl
  · rw [contMDiffOn_levelSet_iff (orth_submersive _ (ηSig_mem 1 3) (ηSig_sq 1 3))]
    refine (contMDiffOn_pi_space.mpr fun a => contMDiffOn_pi_space.mpr fun b => hent (hI a) (hI b)).congr
      fun x hx => ?_
    show ((ιinv (F x)).2 : Mat 4) = fun a b => (F x : Mat 14) (hI a) (hI b)
    rw [ιinv, dif_pos (hmem x hx)]; rfl

end

end GU.Library
