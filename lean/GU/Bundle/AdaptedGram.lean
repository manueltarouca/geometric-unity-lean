/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.AdaptedReduction

/-!
# Chart-invariant Gram functions of the `V` and `H*` parts

`BHf G u v = covec u.2 ⬝ G covec v.2` is the `H*` part of the chimeric form (`Bmod = BV + BH`,
`Bmod_eq_split`); it is covariant by itself (`BHf_covariant`), so its Gram entries on frames are
chart independent (`gramH_triv`) and smooth in total-space charts (`gramH_chart`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The `H*` part of the chimeric form. -/
noncomputable def BHf (G : Matrix (Fin 4) (Fin 4) ℝ) (u v : CFib) : ℝ :=
  covec u.2 ⬝ᵥ (G *ᵥ covec v.2)

/-- The `V` part of the chimeric form. -/
noncomputable def BVf (G : Matrix (Fin 4) (Fin 4) ℝ) (x y : Fin 10 → ℝ) : ℝ :=
  chimY G (symMat x, 0) (symMat y, 0)

lemma Bmod_eq_split (G : Matrix (Fin 4) (Fin 4) ℝ) (u v : CFib) :
    Bmod G u v = BVf G u.1 v.1 + BHf G u v := by
  simp [Bmod, BVf, BHf, chimY]

lemma dot_conj (B Q : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4 → ℝ) :
    (B *ᵥ a) ⬝ᵥ (Q *ᵥ (B *ᵥ b)) = a ⬝ᵥ ((Bᵀ * Q * B) *ᵥ b) := by
  rw [← vecMul_transpose B a, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- **The `H*` part is covariant.** -/
theorem BHf_covariant (P G : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (u v : CFib) :
    BHf (P * G * Pᵀ) (TP P hP u) (TP P hP v) = BHf G u v := by
  have hd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hc : ∀ w : CFib, covec (TP P hP w).2 = (P⁻¹)ᵀ *ᵥ covec w.2 := fun w => covec_comp _ _
  unfold BHf
  rw [hc, hc, dot_conj, transpose_transpose]
  have h1 : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have h2 : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  congr 2
  calc P⁻¹ * (P * G * Pᵀ) * (P⁻¹)ᵀ = (P⁻¹ * P) * G * (Pᵀ * (P⁻¹)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

lemma gramH_localTriv (i : atlas (Fin 4 → ℝ) X) (p : HomTot X) (hp : πY p.proj ∈ (Zt X).baseSet i)
    (u w : CFib) :
    BHf (Gi i p.proj) ((((frameCore (X := X)).localTriv i p).2 : EndC) u)
      ((((frameCore (X := X)).localTriv i p).2 : EndC) w) =
    BHf (Gpt p.proj) ((show EndC from p.2) u) ((show EndC from p.2) w) := by
  have hx : πY p.proj ∈ (Zt X).baseSet ((Zt X).indexAt (πY p.proj)) ∩ (Zt X).baseSet i :=
    ⟨(Zt X).mem_baseSet_at _, hp⟩
  rw [VectorBundleCore.localTriv_apply, Gi_eq]
  show BHf _ (gX ((Zt X).indexAt (πY p.proj)) i _ _) (gX ((Zt X).indexAt (πY p.proj)) i _ _) = _
  rw [gX_eq_TP _ _ _ hx, gX_eq_TP _ _ _ hx]
  exact BHf_covariant _ _ _ _ _

/-- **`H*`-Gram entries in a `HomTotM` trivialisation.** -/
lemma gramH_triv (y0 : Yobs X) (q : HomTotM X)
    (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) (x x' : R14) :
    BHf (Gpt q.proj) ((show HomF from q.2) x) ((show HomF from q.2) x') =
      BHf (Gi (achart (Fin 4 → ℝ) (πY y0)) q.proj)
        (((trivializationAt HomF (HomCb (X := X)) y0) q).2 x)
        (((trivializationAt HomF (HomCb (X := X)) y0) q).2 x') := by
  have hi : πY q.proj ∈ (Zt X).baseSet (achart (Fin 4 → ℝ) (πY y0)) := by
    rw [Cb_baseSet] at hq; exact hq
  have ht := triv_ofM y0 q hq
  have h1 : ∀ z : R14, ((trivializationAt HomF (HomCb (X := X)) y0) q).2 z =
      (((frameCore (X := X)).localTriv (achart (Fin 4 → ℝ) (πY y0)) (ofM q)).2 : EndC) (ΦL z) := by
    intro z; rw [ht]; simp
  have h2 : ∀ z : R14, (show HomF from q.2) z = (show EndC from (ofM q).2) (ΦL z) := by
    intro z; show _ = (show HomF from q.2) (ΦL.symm (ΦL z)); rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [h1, h1, h2, h2]
  exact (gramH_localTriv (achart (Fin 4 → ℝ) (πY y0)) (ofM q) hi _ _).symm

/-! ### Gram functions on `HomTotM` and their chart formulas -/

/-- `H*`-Gram entries of a frame. -/
noncomputable def gramH (q : HomTotM X) (i j : Fin 14) : ℝ :=
  BHf (Gpt q.proj) ((show HomF from q.2) (Pi.single i 1)) ((show HomF from q.2) (Pi.single j 1))

/-- Full chimeric Gram entries of a frame. -/
noncomputable def gramB (q : HomTotM X) (i j : Fin 14) : ℝ :=
  Bmod (Gpt q.proj) ((show HomF from q.2) (Pi.single i 1)) ((show HomF from q.2) (Pi.single j 1))

lemma proj_mem_Cb_baseSet (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    q.proj ∈ (trivializationAt CFib (Cb (X := X)) a.proj).baseSet := by
  have hsrc := hq
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hsrc
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_univ, and_true] at hsrc
  exact ((Trivialization.mem_source _).mp hsrc.1).2

lemma chart_snd (a q : HomTotM X) :
    (show HomF from (chartAt HomModel a q).2) =
      ((trivializationAt HomF (HomCb (X := X)) a.proj) q).2 := by
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a]; rfl

/-- **Chart formula for the `H*`-Gram.** -/
lemma gramH_chart (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) (i j : Fin 14) :
    gramH q i j = BHf (symMat (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a q).1).2)
      ((show HomF from (chartAt HomModel a q).2) (Pi.single i 1))
      ((show HomF from (chartAt HomModel a q).2) (Pi.single j 1)) := by
  unfold gramH
  rw [gramH_triv a.proj q (proj_mem_Cb_baseSet a q hq), Gi_chart, chart_snd,
    chart_fst a q hq]

/-- **Chart formula for the full Gram.** -/
lemma gramB_chart (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) (i j : Fin 14) :
    gramB q i j = Bmod (symMat (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel a q).1).2)
      ((show HomF from (chartAt HomModel a q).2) (Pi.single i 1))
      ((show HomF from (chartAt HomModel a q).2) (Pi.single j 1)) := by
  unfold gramB
  rw [gram_triv a.proj q (proj_mem_Cb_baseSet a q hq), Gi_chart, chart_snd,
    chart_fst a q hq]

/-- Smoothness of the chart expression of `BHf`. -/
lemma contDiff_BHf_chart (i j : Fin 14) :
    ContDiff ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF =>
      BHf (symMat p.1.2) (p.2 (Pi.single i 1)) (p.2 (Pi.single j 1))) := by
  have hc : ∀ (k : Fin 14) (l : Fin 4), ContDiff ℝ ∞
      (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => (p.2 (Pi.single k 1)).2 (Pi.single l 1)) :=
    fun k l => by
      have : (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => (p.2 (Pi.single k 1)).2 (Pi.single l 1))
          = (ContinuousLinearMap.apply ℝ ℝ (Pi.single l (1 : ℝ))).comp
            ((ContinuousLinearMap.snd ℝ (Fin 10 → ℝ) _).comp
              ((ContinuousLinearMap.apply ℝ CFib (Pi.single k (1 : ℝ))).comp
                (ContinuousLinearMap.snd ℝ ((Fin 4 → ℝ) × (Fin 10 → ℝ)) HomF))) := rfl
      rw [this]; exact ContinuousLinearMap.contDiff _
  have hs : ∀ m : Fin 10, ContDiff ℝ ∞
      (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => p.1.2 m) := fun m => by
    have : (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => p.1.2 m) =
      ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) m).comp
      ((ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) (Fin 10 → ℝ)).comp
        (ContinuousLinearMap.fst ℝ ((Fin 4 → ℝ) × (Fin 10 → ℝ)) HomF))) := rfl
    rw [this]; exact ContinuousLinearMap.contDiff _
  simp only [BHf, dotProduct, mulVec, covec, symMat, Matrix.of_apply]
  exact ContDiff.sum fun k _ => (hc i k).mul (ContDiff.sum fun l _ => (hs _).mul (hc j l))

/-! ### Index enumerations `SHᶜ ≅ Fin 10`, `SH ≅ Fin 4` (order preserving) -/

/-- The vertical indices `0..5, 7..10`. -/
def vI : Fin 10 → Fin 14 := ![0, 1, 2, 3, 4, 5, 7, 8, 9, 10]
/-- The horizontal indices `6, 11, 12, 13`. -/
def hI : Fin 4 → Fin 14 := ![6, 11, 12, 13]
/-- Inverse of `vI` on `SHᶜ`. -/
def vInv : Fin 14 → Fin 10 := ![0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 0, 0, 0]
/-- Inverse of `hI` on `SH`. -/
def hInv : Fin 14 → Fin 4 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3]

lemma vI_not_mem (a : Fin 10) : vI a ∉ SH := by revert a; decide
lemma hI_mem (b : Fin 4) : hI b ∈ SH := by revert b; decide
lemma vInv_vI (a : Fin 10) : vInv (vI a) = a := by revert a; decide
lemma hInv_hI (b : Fin 4) : hInv (hI b) = b := by revert b; decide
lemma vI_vInv {i : Fin 14} (hi : i ∉ SH) : vI (vInv i) = i := by revert i; decide
lemma hI_hInv {i : Fin 14} (hi : i ∈ SH) : hI (hInv i) = i := by revert i; decide
lemma vI_injective : Function.Injective vI := fun a b h => by
  rw [← vInv_vI a, h, vInv_vI]
lemma hI_injective : Function.Injective hI := fun a b h => by
  rw [← hInv_hI a, h, hInv_hI]

/-! ### The open set `Ω` -/

/-- Opaque determinants (avoid `isDefEq` unfolding `Matrix.det`). -/
irreducible_def dt4 (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := M.det
irreducible_def dt10 (M : Matrix (Fin 10) (Fin 10) ℝ) : ℝ := M.det

lemma continuous_dt4 : Continuous dt4 := by
  have : dt4 = fun M => M.det := funext fun M => dt4_def M
  rw [this]; exact continuous_id.matrix_det
lemma continuous_dt10 : Continuous dt10 := by
  have : dt10 = fun M => M.det := funext fun M => dt10_def M
  rw [this]; exact continuous_id.matrix_det

/-- `H*`-Gram on the horizontal legs. -/
noncomputable def gH4 (q : HomTotM X) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => gramH q (hI a) (hI b)

/-- `V`-Gram on the vertical legs. -/
noncomputable def gV10 (q : HomTotM X) : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.of fun a b => gramB q (vI a) (vI b) - gramH q (vI a) (vI b)

/-- Frames whose horizontal legs have nondegenerate `H*`-Gram and whose vertical legs have
nondegenerate `V`-Gram. -/
def Ωset (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Set (HomTotM X) :=
  {q | dt4 (gH4 q) ≠ 0 ∧ dt10 (gV10 q) ≠ 0}

/-- Chart expression of `gH4`/`gV10`. -/
noncomputable def gH4c (p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => BHf (symMat p.1.2) (p.2 (Pi.single (hI a) 1)) (p.2 (Pi.single (hI b) 1))

noncomputable def gV10c (p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.of fun a b => bil (Gchim p.1.2) (homMat.symm p.2) (homMat.symm p.2) (vI a) (vI b) -
    BHf (symMat p.1.2) (p.2 (Pi.single (vI a) 1)) (p.2 (Pi.single (vI b) 1))

lemma continuous_gH4c : Continuous gH4c :=
  continuous_pi fun a => continuous_pi fun b => (contDiff_BHf_chart (hI a) (hI b)).continuous

lemma continuousOn_gV10c :
    ContinuousOn gV10c {p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF | p.1.2 ∈ nondeg} := by
  have hb : ContinuousOn (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF =>
      bil (Gchim p.1.2) (homMat.symm p.2) (homMat.symm p.2))
      {p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF | p.1.2 ∈ nondeg} := by
    have hG : ContDiffOn ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => Gchim p.1.2)
        {p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF | p.1.2 ∈ nondeg} :=
      contDiffOn_Gchim.comp (contDiff_snd.comp contDiff_fst).contDiffOn fun p hp => hp
    have hM : ContDiff ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => homMat.symm p.2) :=
      contDiff_homMat_symm.comp contDiff_snd
    have : (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF =>
        bil (Gchim p.1.2) (homMat.symm p.2) (homMat.symm p.2)) =
        bilFull ∘ fun p => (Gchim p.1.2, homMat.symm p.2) := rfl
    rw [this]
    exact (contDiff_bilFull.comp_contDiffOn (hG.prodMk hM.contDiffOn)).continuousOn
  refine continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b => ?_
  exact ((continuous_apply_apply (vI a) (vI b)).comp_continuousOn hb).sub
    (contDiff_BHf_chart (vI a) (vI b)).continuous.continuousOn

lemma gH4_chart (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    gH4 q = gH4c (show ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF from chartAt HomModel a q) := by
  ext i j; exact gramH_chart a q hq _ _

lemma gV10_chart (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    gV10 q = gV10c (show ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF from chartAt HomModel a q) := by
  ext i j
  simp only [gV10, gV10c, Matrix.of_apply]
  rw [gramB_chart a q hq, gramH_chart a q hq, bil_homMat_entry]

/-- The chart-`a` determinant pair. -/
noncomputable def dΩ (a q : HomTotM X) : ℝ × ℝ :=
  (dt4 (gH4c (show ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF from chartAt HomModel a q)),
   dt10 (gV10c (show ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF from chartAt HomModel a q)))

lemma mem_Ωset_iff_dΩ (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    q ∈ Ωset X ↔ (dΩ a q).1 ≠ 0 ∧ (dΩ a q).2 ≠ 0 := by
  show dt4 (gH4 q) ≠ 0 ∧ dt10 (gV10 q) ≠ 0 ↔ _
  rw [gH4_chart a q hq, gV10_chart a q hq]; rfl

lemma continuousOn_dΩ (a : HomTotM X) : ContinuousOn (dΩ a) (chartAt HomModel a).source := by
  set c := chartAt HomModel a
  have hφ : ContinuousOn (fun q => (show ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF from c q)) c.source :=
    c.continuousOn
  have h1 := (continuous_dt4.comp continuous_gH4c).comp_continuousOn hφ
  have hV := continuousOn_gV10c.comp hφ fun q hq => chart_target_nondeg a (c.map_source hq)
  exact h1.prodMk (continuous_dt10.comp_continuousOn hV)

/-- **`Ω` is open.** -/
theorem isOpen_Ωset : IsOpen (Ωset X) := by
  rw [isOpen_iff_forall_mem_open]
  intro q0 hq0
  refine ⟨(chartAt HomModel q0).source ∩ dΩ q0 ⁻¹' {x | x.1 ≠ 0 ∧ x.2 ≠ 0}, ?_, ?_, ?_⟩
  · rintro q ⟨hq, h⟩
    exact (mem_Ωset_iff_dΩ q0 q hq).mpr h
  · exact (continuousOn_dΩ q0).isOpen_inter_preimage (chartAt HomModel q0).open_source
      ((isOpen_ne_fun continuous_fst continuous_const).inter
        (isOpen_ne_fun continuous_snd continuous_const))
  · exact ⟨mem_chart_source _ q0, (mem_Ωset_iff_dΩ q0 q0 (mem_chart_source _ q0)).mp hq0⟩

/-! ### The level set inside `Ω` is exactly `AFr` -/

/-- A vector `K`-orthogonal to `n` vectors with nondegenerate Gram matrix vanishes. -/
lemma eq_zero_of_gram {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → Fin n → ℝ)
    (hd : (Matrix.of fun i j => a i ⬝ᵥ (K *ᵥ a j)).det ≠ 0) {b : Fin n → ℝ}
    (hb : ∀ i, a i ⬝ᵥ (K *ᵥ b) = 0) : b = 0 := by
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of a
  have hG : (Matrix.of fun i j => a i ⬝ᵥ (K *ᵥ a j)) = B * K * Bᵀ := by
    ext i j
    simp only [B, Matrix.of_apply, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rw [hG, Matrix.det_mul] at hd
  have h1 : (B * K).det ≠ 0 := fun h => hd (by rw [h, zero_mul])
  have hu : IsUnit (B * K) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h1)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
  funext i; exact hb i

lemma symMat_add' (x y : Fin 10 → ℝ) : symMat (x + y) = symMat x + symMat y := by
  ext i j; simp [symMat]
lemma symMat_smul' (r : ℝ) (x : Fin 10 → ℝ) : symMat (r • x) = r • symMat x := by
  ext i j; simp [symMat]

/-- `BVf G` as a bilinear map. -/
noncomputable def BVL (G : Matrix (Fin 4) (Fin 4) ℝ) :
    (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (BVf G)
    (fun x x' y => by
      simp only [BVf, chimY, symMat_add', Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
        zero_dotProduct]; ring)
    (fun r x y => by
      simp only [BVf, chimY, symMat_smul', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        zero_dotProduct, smul_eq_mul]; ring)
    (fun x y y' => by
      simp only [BVf, chimY, symMat_add', Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
        zero_dotProduct, mulVec_zero, dotProduct_zero]; ring)
    (fun r x y => by
      simp only [BVf, chimY, symMat_smul', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        zero_dotProduct, smul_eq_mul]; ring)

lemma BVf_eq_dot (G : Matrix (Fin 4) (Fin 4) ℝ) (x y : Fin 10 → ℝ) :
    BVf G x y = x ⬝ᵥ (LinearMap.toMatrix₂' ℝ (BVL G) *ᵥ y) := by
  rw [← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']; rfl

lemma BHf_comm (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.IsSymm) (u v : CFib) :
    BHf G u v = BHf G v u := by
  unfold BHf
  rw [dotProduct_mulVec, ← mulVec_transpose, hG.eq, dotProduct_comm]

lemma covec_eq_zero {p : (Fin 4 → ℝ) →L[ℝ] ℝ} (h : covec p = 0) : p = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 4 → ℝ) by
    ext i; by_cases e : i = k <;> simp [e], map_smul]
  have := congrFun h k
  simp only [covec, Pi.zero_apply] at this
  rw [this, smul_zero]

lemma η77_apply' (i j : Fin 14) :
    η77 i j = if i = j then (if (i : ℕ) < 7 then 1 else -1) else 0 := η77_apply i j

lemma gramB_ortho {q : HomTotM X} (hq : q ∈ OFr X) (i j : Fin 14) : gramB q i j = η77 i j := by
  have hO : q ∈ orthoSetM := by rw [← levelSet_Fframe]; exact hq
  rw [mem_orthoSetM_iff_mat] at hO
  have := congrFun (congrFun hO i) j
  exact (bil_homMat_entry _ q.2 i j).symm.trans this

lemma Gpt_symm (y : Yobs X) : (Gpt y).IsSymm := symMat_isSymm _

/-- **Level points in `Ω` are adapted.** -/
theorem mem_AFr_of_level {q : HomTotM X} (hq : q ∈ OFr X) (hΩ : q ∈ Ωset X)
    (h0 : ∀ a b, gramH q (vI a) (hI b) = 0) : q ∈ AFr X := by
  set h := (show HomF from q.2)
  set K := Gpt q.proj
  -- the `H*` legs of vertical vectors vanish
  have hV : ∀ j ∉ SH, (h (Pi.single j 1)).2 = 0 := by
    intro j hj
    apply covec_eq_zero
    refine eq_zero_of_gram K (fun a => covec (h (Pi.single (hI a) 1)).2) ?_ fun a => ?_
    · have := hΩ.1; rw [dt4_def] at this; exact this
    · have := h0 (vInv j) a
      rw [vI_vInv hj] at this
      show BHf K (h (Pi.single (hI a) 1)) (h (Pi.single j 1)) = 0
      rw [BHf_comm K (Gpt_symm _)]; exact this
  refine ⟨hq, fun i hi => ?_, hV⟩
  -- the `V` legs of horizontal vectors vanish
  refine eq_zero_of_gram (LinearMap.toMatrix₂' ℝ (BVL K)) (fun a => (h (Pi.single (vI a) 1)).1) ?_
    fun a => ?_
  · have := hΩ.2; rw [dt10_def] at this
    convert this using 2
    ext a b
    simp only [gV10, Matrix.of_apply, gramB, gramH, Bmod_eq_split, ← BVf_eq_dot]
    ring
  · rw [← BVf_eq_dot]
    have e1 := gramB_ortho hq (vI a) i
    have hne : vI a ≠ i := fun e => vI_not_mem a (e ▸ hi)
    rw [η77_apply', if_neg hne] at e1
    unfold gramB at e1
    rw [Bmod_eq_split] at e1
    have e2 : BHf K (h (Pi.single (vI a) 1)) (h (Pi.single i 1)) = 0 := by
      unfold BHf; rw [hV _ (vI_not_mem a)]
      have : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext; simp [covec]
      rw [this, zero_dotProduct]
    rw [e2, add_zero] at e1
    exact e1

/-- **Adapted frames lie in `Ω` and on the level.** -/
theorem level_of_mem_AFr {q : HomTotM X} (hq : q ∈ AFr X) :
    q ∈ Ωset X ∧ ∀ a b, gramH q (vI a) (hI b) = 0 := by
  obtain ⟨hO, ha⟩ := hq
  set h := (show HomF from q.2)
  set K := Gpt q.proj
  have hc0 : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext; simp [covec]
  have hBH0 : ∀ j ∉ SH, ∀ k, gramH q j k = 0 := fun j hj k => by
    unfold gramH BHf; rw [ha.2 j hj, hc0, zero_dotProduct]
  have hBV0 : ∀ i ∈ SH, ∀ y, BVf K (h (Pi.single i 1)).1 y = 0 := fun i hi y => by
    rw [ha.1 i hi]
    have : symMat (0 : Fin 10 → ℝ) = 0 := by ext; simp [symMat]
    simp [BVf, chimY, this]
  have hsgn : ∀ i : Fin 14, η77 i i ≠ 0 := fun i => by
    rw [η77_apply', if_pos rfl]; split_ifs <;> norm_num
  refine ⟨⟨?_, ?_⟩, fun a b => hBH0 _ (vI_not_mem a) _⟩
  · have e : gH4 q = Matrix.diagonal fun a => η77 (hI a) (hI a) := by
      ext a b
      simp only [gH4, Matrix.of_apply, Matrix.diagonal_apply]
      have : gramH q (hI a) (hI b) = gramB q (hI a) (hI b) := by
        unfold gramB; rw [Bmod_eq_split, hBV0 _ (hI_mem a), zero_add]; rfl
      rw [this, gramB_ortho hO, η77_apply']
      by_cases hab : a = b
      · subst hab; simp [η77_apply']
      · rw [if_neg (fun e => hab (hI_injective e)), if_neg hab]
    rw [dt4_def, e, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hsgn _
  · have e : gV10 q = Matrix.diagonal fun a => η77 (vI a) (vI a) := by
      ext a b
      simp only [gV10, Matrix.of_apply, Matrix.diagonal_apply]
      rw [hBH0 _ (vI_not_mem a), sub_zero, gramB_ortho hO, η77_apply']
      by_cases hab : a = b
      · subst hab; simp [η77_apply']
      · rw [if_neg (fun e => hab (vI_injective e)), if_neg hab]
    rw [dt10_def, e, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hsgn _

end GU.Library
