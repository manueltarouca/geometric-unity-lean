/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.AdaptedBundle

/-!
# Smooth local adapted sections

* **`exists_local_frames_blk`**: the implicit-function construction of `exists_local_frames`
  restricted to block-symmetric `S` (projection `blkProj`): a block-diagonal analytic family
  `H(b)` with `H(b₀) = η₇₇` has block-diagonal analytic local frames `N(b)`.
* Chart fibre coordinates are `T ∘ q.2` with `T` the trivialisation of `C = V ⊕ H*`, which acts
  componentwise (`triv_fst_eq_zero_iff`, `triv_snd_eq_zero_iff`), so adaptedness is chart-invariant
  (`adapted_chart_iff`).
* The Gram matrix of an adapted frame is block-diagonal for every fibre metric (`Bmod_VH`), so
  **`exists_local_section_adapted`**: smooth local sections of `OFr` with values in `AFr`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-! ### Block-symmetric matrices -/

lemma isBlk_bil {H N : Mat 14} (hH : IsBlk H) (hN : IsBlk N) : IsBlk (bil H N N) := by
  intro i j hij
  rw [bil_apply]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hk : (k ∈ SH ↔ i ∈ SH)
  · by_cases hl : (k ∈ SH ↔ l ∈ SH)
    · rw [hN l j (by tauto), mul_zero]
    · rw [hH k l (by tauto), mul_zero, zero_mul]
  · rw [hN k i (by tauto), zero_mul, zero_mul]

lemma isBlk_symP {A : Mat 14} (hA : IsBlk A) : IsBlk (symP 14 A : Mat 14) := by
  intro i j hij
  show (A i j + A j i) / 2 = 0
  rw [hA i j hij, hA j i (by tauto)]; simp

lemma isBlk_Nf {S : Mat 14} (hS : IsBlk S) : IsBlk (Nf η77 (symP 14 S)) := by
  have hS' := isBlk_symP hS
  have : Nf η77 (symP 14 S) = Matrix.of.symm 1 + mulM η77 (symP 14 S : Mat 14) := by
    apply Matrix.of.injective; rfl
  rw [this]
  exact isBlk_add isBlk_one (isBlk_mul isBlk_η77 hS')

/-- Block-symmetric matrices. -/
def symBlk : Submodule ℝ (Mat 14) where
  carrier := {A | A ∈ symS 14 ∧ IsBlk A}
  add_mem' {a b} ha hb := ⟨(symS 14).add_mem ha.1 hb.1, isBlk_add ha.2 hb.2⟩
  zero_mem' := ⟨(symS 14).zero_mem, fun _ _ _ => rfl⟩
  smul_mem' r a ha := ⟨(symS 14).smul_mem r ha.1, fun i j hij => by
    show r * a i j = 0
    rw [ha.2 i j hij, mul_zero]⟩

/-- The inclusion `symBlk → symS`. -/
noncomputable def ιBlk : symBlk →L[ℝ] symS 14 :=
  ⟨Submodule.inclusion (fun _ h => h.1), LinearMap.continuous_of_finiteDimensional _⟩

lemma ιBlk_val (S : symBlk) : ((ιBlk S : symS 14) : Mat 14) = S := rfl

/-- The block mask. -/
def blkMask (A : Mat 14) : Mat 14 := fun i j => if (i ∈ SH ↔ j ∈ SH) then A i j else 0

lemma blkMask_mem (S : symS 14) : blkMask (S : Mat 14) ∈ symBlk := by
  refine ⟨fun i j => ?_, fun i j hij => ?_⟩
  · unfold blkMask
    by_cases h : (i ∈ SH ↔ j ∈ SH)
    · rw [if_pos h, if_pos h.symm, S.2 i j]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  · unfold blkMask; rw [if_neg (by tauto)]

/-- Projection onto block-symmetric matrices. -/
noncomputable def blkProjL : symS 14 →ₗ[ℝ] symBlk where
  toFun S := ⟨blkMask (S : Mat 14), blkMask_mem S⟩
  map_add' S T := by
    ext i j; simp only [blkMask, Submodule.coe_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' r S := by
    ext i j; simp only [blkMask, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; split_ifs <;> simp

noncomputable def blkProj : symS 14 →L[ℝ] symBlk :=
  ⟨blkProjL, LinearMap.continuous_of_finiteDimensional _⟩

lemma blkProj_val (S : symS 14) : ((blkProj S : symBlk) : Mat 14) = blkMask (S : Mat 14) := rfl

lemma blkMask_of_isBlk {A : Mat 14} (hA : IsBlk A) : blkMask A = A := by
  funext i j; unfold blkMask
  by_cases h : (i ∈ SH ↔ j ∈ SH)
  · rw [if_pos h]
  · rw [if_neg h, hA i j (by tauto)]

lemma blkProj_ιBlk (S : symBlk) : blkProj (ιBlk S) = S :=
  Subtype.ext (blkMask_of_isBlk S.2.2)

section IFT

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- **Block-diagonal local frames**: a block-diagonal analytic symmetric family `H(b)` with
`H(b₀) = η₇₇` has analytic, block-diagonal `N(b)` near `b₀` with `N(b)ᵀ H(b) N(b) = η₇₇`. -/
theorem exists_local_frames_blk (H : B → Mat 14) (b0 : B) (hH : ContDiffAt ℝ ω H b0)
    (hsym : ∀ b, H b ∈ symS 14) (hblk : ∀ b, IsBlk (H b)) (h0 : H b0 = η77) :
    ∃ U ∈ nhds b0, ∃ N : B → Mat 14, ContDiffOn ℝ ω N U ∧ (∀ b, IsBlk (N b)) ∧
      ∀ b ∈ U, bil (H b) (N b) (N b) = η77 := by
  set ι : symBlk →L[ℝ] symS 14 := ιBlk
  set f : B × symBlk → symBlk := fun p => blkProj (orthF (H p.1) (Nf η77 (ι p.2))) with hfdef
  have cdf : ContDiffAt ℝ ω f (b0, 0) := by
    have hpair : ContDiffAt ℝ ω (fun p : B × symBlk => (H p.1, Nf η77 (ι p.2))) (b0, 0) :=
      (hH.comp _ contDiffAt_fst).prodMk
        (((contDiff_Nf η77).comp ι.contDiff).contDiffAt.comp _ contDiffAt_snd)
    have hfeq : f = ⇑blkProj ∘ ⇑(symP 14) ∘ bilFull ∘
        (fun p : B × symBlk => (H p.1, Nf η77 (ι p.2))) := rfl
    rw [hfeq]
    exact blkProj.contDiff.contDiffAt.comp _
      ((symP 14).contDiff.contDiffAt.comp _ (contDiff_bilFull.contDiffAt.comp _ hpair))
  have hf : HasFDerivAt f (fderiv ℝ f (b0, 0)) (b0, 0) :=
    (cdf.differentiableAt (by simp)).hasFDerivAt
  have hinc : HasFDerivAt (fun S : symBlk => (b0, S)) (ContinuousLinearMap.inr ℝ B symBlk) 0 :=
    (hasFDerivAt_const b0 0).prodMk (hasFDerivAt_id 0)
  have h1 := hf.comp (0 : symBlk) hinc
  have hι0 : ι 0 = 0 := map_zero ι
  have hNι : HasFDerivAt (fun S : symBlk => Nf η77 (ι S)) ((Lη η77).comp ι) 0 :=
    (hasFDerivAt_Nf η77 (ι 0)).comp 0 ι.hasFDerivAt
  have hO : HasFDerivAt (orthF η77) (fderiv ℝ (orthF η77) (Nf η77 0)) (Nf η77 (ι 0)) := by
    rw [hι0]
    exact ((orthF_contDiff η77).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 := blkProj.hasFDerivAt.comp (0 : symBlk) (hO.comp (0 : symBlk) hNι)
  have hfun : (f ∘ fun S : symBlk => (b0, S)) =
      ⇑blkProj ∘ (orthF η77 ∘ fun S : symBlk => Nf η77 (ι S)) := by
    funext S; simp only [Function.comp_apply, hfdef, h0]
  rw [hfun] at h1
  have hD : fderiv ℝ f (b0, 0) ∘L ContinuousLinearMap.inr ℝ B symBlk =
      (2 : ℝ) • ContinuousLinearMap.id ℝ symBlk := by
    rw [h1.unique h2]
    refine ContinuousLinearMap.ext fun S => ?_
    simp only [ContinuousLinearMap.comp_apply]
    rw [deriv_orthF_Nf η77 (ηSig_mem 7 7) (ηSig_sq 7 7) (ι S), map_smul]
    show (2 : ℝ) • blkProj (ιBlk S) = _
    rw [blkProj_ιBlk]; rfl
  have if₂ : (fderiv ℝ f (b0, 0) ∘L ContinuousLinearMap.inr ℝ B symBlk).IsInvertible := by
    rw [hD]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ symBlk 2 two_ne_zero).toContinuousLinearEquiv, ?_⟩
    ext S; rfl
  have pn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hψ := cdf.contDiffAt_implicitFunction pn if₂
  obtain ⟨U1, hU1, hon⟩ := hψ.contDiffOn (m := ω) le_rfl (by simp)
  have hev := cdf.eventually_apply_implicitFunction pn if₂
  set ψ := cdf.implicitFunction pn if₂
  refine ⟨U1 ∩ {b | f (b, ψ b) = f (b0, 0)}, Filter.inter_mem hU1 hev,
    fun b => Nf η77 (ι (ψ b)),
    ((contDiff_Nf η77).comp ι.contDiff).comp_contDiffOn (hon.mono Set.inter_subset_left),
    fun b => ?_, ?_⟩
  · show IsBlk (Nf η77 (ι (ψ b)))
    have : (ι (ψ b) : symS 14) = symP 14 ((ι (ψ b) : symS 14) : Mat 14) :=
      (Subtype.ext (symP_of_mem (ι (ψ b)).2)).symm
    rw [this]; exact isBlk_Nf (ψ b).2.2
  rintro b ⟨-, hb⟩
  have hNb : IsBlk (Nf η77 (ι (ψ b))) := by
    have : (ι (ψ b) : symS 14) = symP 14 ((ι (ψ b) : symS 14) : Mat 14) :=
      (Subtype.ext (symP_of_mem (ι (ψ b)).2)).symm
    rw [this]; exact isBlk_Nf (ψ b).2.2
  have hblkO : IsBlk (orthF (H b) (Nf η77 (ι (ψ b))) : Mat 14) :=
    isBlk_symP (isBlk_bil (hblk b) hNb)
  have hb' : orthF (H b) (Nf η77 (ι (ψ b))) = ⟨η77, ηSig_mem 7 7⟩ := by
    have e1 := congrArg (fun S : symBlk => (S : Mat 14)) hb
    simp only [hfdef, h0, blkProj_val, map_zero] at e1
    rw [orthF_Nf_zero η77 (ηSig_mem 7 7)] at e1
    apply Subtype.ext
    rw [← blkMask_of_isBlk hblkO, e1]
    exact blkMask_of_isBlk isBlk_η77
  exact bil_of_orthF_eq (hsym b) (ηSig_mem 7 7) hb'

end IFT

/-! ### Adaptedness is chart-invariant; Gram matrices of adapted frames are block -/

/-- `V ⊥ H*` for every chimeric fibre metric. -/
lemma Bmod_VH (G : Matrix (Fin 4) (Fin 4) ℝ) {u v : CFib} (hu : u.2 = 0) (hv : v.1 = 0) :
    Bmod G u v = 0 := by
  have h1 : symMat (0 : Fin 10 → ℝ) = 0 := by ext i j; simp [symMat]
  have h2 : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext i; simp [covec]
  simp [Bmod, chimY, hu, hv, h1, h2]

lemma Bmod_HV (G : Matrix (Fin 4) (Fin 4) ℝ) {u v : CFib} (hu : u.1 = 0) (hv : v.2 = 0) :
    Bmod G u v = 0 := by
  have h1 : symMat (0 : Fin 10 → ℝ) = 0 := by ext i j; simp [symMat]
  have h2 : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext i; simp [covec]
  simp [Bmod, chimY, hu, hv, h1, h2]

/-- **The Gram matrix of an adapted frame is block-diagonal**, for every fibre metric. -/
lemma isBlk_gram (s : Fin 10 → ℝ) {h : HomF} (ha : Adapted h) :
    IsBlk (bil (Gchim s) (homMat.symm h) (homMat.symm h)) := by
  intro i j hij
  rw [bil_homMat_entry]
  by_cases hi : i ∈ SH
  · exact Bmod_HV _ (ha.1 i hi) (ha.2 j (by tauto))
  · exact Bmod_VH _ (ha.2 i hi) (ha.1 j (by tauto))

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The fibre trivialisation of `C` at `z`, as a map `CFib → CFib`. -/
noncomputable def Tz (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    CFib ≃L[ℝ] CFib :=
  (trivializationAt CFib (Cb (X := X)) y).continuousLinearEquivAt ℝ z hz

lemma Tz_fst_zero (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet)
    (w : (Fin 4 → ℝ) →L[ℝ] ℝ) : (Tz y z hz ((0 : Fin 10 → ℝ), w)).1 = 0 := by
  show (((trivializationAt CFib (Cb (X := X)) y).continuousLinearEquivAt ℝ z hz
      (show Cb (X := X) z from ((0 : Fin 10 → ℝ), w)) : CFib)).1 = 0
  rw [Trivialization.continuousLinearEquivAt_apply]
  have hz' := hz
  rw [show (trivializationAt CFib (Cb (X := X)) y) = (trivializationAt _ (Vb (X := X)) y).prod
    (trivializationAt _ (Hb (X := X)) y) from rfl] at hz' ⊢
  show (((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y).prod (trivializationAt _ (Hb (X := X)) y))
    ⟨z, ((0 : Vb (X := X) z), (w : Hb (X := X) z))⟩).2.1 = 0
  erw [Trivialization.prod_apply]
  exact congrArg Prod.snd ((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y).zeroSection ℝ hz'.1)

lemma Tz_snd_zero (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet)
    (v : Fin 10 → ℝ) : (Tz y z hz (v, (0 : (Fin 4 → ℝ) →L[ℝ] ℝ))).2 = 0 := by
  show (((trivializationAt CFib (Cb (X := X)) y).continuousLinearEquivAt ℝ z hz
      (show Cb (X := X) z from (v, (0 : (Fin 4 → ℝ) →L[ℝ] ℝ))) : CFib)).2 = 0
  rw [Trivialization.continuousLinearEquivAt_apply]
  have hz' := hz
  rw [show (trivializationAt CFib (Cb (X := X)) y) = (trivializationAt _ (Vb (X := X)) y).prod
    (trivializationAt _ (Hb (X := X)) y) from rfl] at hz' ⊢
  show (((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y).prod (trivializationAt _ (Hb (X := X)) y))
    ⟨z, ((v : Vb (X := X) z), (0 : Hb (X := X) z))⟩).2.2 = 0
  erw [Trivialization.prod_apply]
  exact congrArg Prod.snd ((trivializationAt _ (Hb (X := X)) y).zeroSection ℝ hz'.2)

lemma Tz_fst_eq_zero_iff (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet)
    (u : CFib) : (Tz y z hz u).1 = 0 ↔ u.1 = 0 := by
  set T := Tz y z hz
  have hsplit : u = (u.1, 0) + (0, u.2) := by ext <;> simp
  constructor
  · intro h
    have h1 : (T (u.1, 0)).1 = 0 := by
      have := h
      rw [hsplit, map_add, Prod.fst_add, Tz_fst_zero, add_zero] at this
      exact this
    have h0 : T (u.1, 0) = 0 := Prod.ext h1 (Tz_snd_zero y z hz u.1)
    have := congrArg Prod.fst ((map_eq_zero_iff T T.injective).mp h0)
    exact this
  · intro h
    rw [show u = (0, u.2) from Prod.ext h rfl]
    exact Tz_fst_zero y z hz u.2

lemma Tz_snd_eq_zero_iff (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet)
    (u : CFib) : (Tz y z hz u).2 = 0 ↔ u.2 = 0 := by
  set T := Tz y z hz
  have hsplit : u = (u.1, 0) + (0, u.2) := by ext <;> simp
  constructor
  · intro h
    have h1 : (T (0, u.2)).2 = 0 := by
      have := h
      rw [hsplit, map_add, Prod.snd_add, Tz_snd_zero, zero_add] at this
      exact this
    have h0 : T (0, u.2) = 0 := Prod.ext (Tz_fst_zero y z hz u.2) h1
    have := congrArg Prod.snd ((map_eq_zero_iff T T.injective).mp h0)
    exact this
  · intro h
    rw [show u = (u.1, 0) from Prod.ext rfl h]
    exact Tz_snd_zero y z hz u.1

lemma adapted_Tz_iff (y z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet)
    (h : HomF) : Adapted ((Tz y z hz : CFib →L[ℝ] CFib).comp h) ↔ Adapted h :=
  ⟨fun ⟨h1, h2⟩ => ⟨fun j hj => (Tz_fst_eq_zero_iff y z hz _).mp (h1 j hj),
      fun j hj => (Tz_snd_eq_zero_iff y z hz _).mp (h2 j hj)⟩,
   fun ⟨h1, h2⟩ => ⟨fun j hj => (Tz_fst_eq_zero_iff y z hz _).mpr (h1 j hj),
      fun j hj => (Tz_snd_eq_zero_iff y z hz _).mpr (h2 j hj)⟩⟩

/-- **Adaptedness can be read in any total-space chart.** -/
lemma adapted_chart_iff (a q : HomTotM X) (hq : q ∈ (chartAt HomModel a).source) :
    Adapted (show HomF from (chartAt HomModel a q).2) ↔ Adapted (show HomF from q.2) := by
  have hsrc := hq
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hsrc
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_univ, and_true] at hsrc
  have hb : q.proj ∈ (trivializationAt CFib (Cb (X := X)) a.proj).baseSet :=
    ((Trivialization.mem_source _).mp hsrc.1).2
  have e : (show HomF from (chartAt HomModel a q).2) =
      ((trivializationAt HomF (HomCb (X := X)) a.proj) q).2 := by
    rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a]; rfl
  rw [e, triv_apply a.proj q hb]
  exact adapted_Tz_iff a.proj q.proj hb _

lemma homMat_mulM (M g : Mat 14) : homMat (mulM M g) = (homMat M).comp (matCLM g) := by
  have := homMat_symm_comp (homMat M) g
  rw [ContinuousLinearEquiv.symm_apply_apply] at this
  rw [← this, ContinuousLinearEquiv.apply_symm_apply]

/-- **Smooth local adapted sections** (in the base chart coordinates of an adapted frame `q₀`):
as `exists_local_section`, with values in `AFr`. -/
theorem exists_local_section_adapted (q0 : HomTotM X) (hq0 : q0 ∈ AFr X) :
    ∃ U ∈ nhds (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 q0).1),
      ∃ σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X,
        ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U ∧
        ∀ e ∈ U, σ e ∈ AFr X ∧ (chartAt HomModel q0 (σ e)).1 = e ∧
          σ e ∈ (chartAt HomModel q0).source := by
  set c := chartAt HomModel q0
  set p0 := c q0
  set e0 : (Fin 4 → ℝ) × (Fin 10 → ℝ) := (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p0.1)
  set M0 := homMat.symm (p0.2 : HomF)
  have hp0 : p0 ∈ c.target := c.map_source (mem_chart_source _ q0)
  have hq0' : c.symm p0 = q0 := c.left_inv (mem_chart_source _ q0)
  have hF0 : bil (Gchim e0.2) M0 M0 = η77 := by
    have h1 : Fframe (c.symm p0) = ⟨η77, ηSig_mem 7 7⟩ := by rw [hq0']; exact hq0.1
    rw [Fframe_chart q0 hp0] at h1
    exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h1
  have ha0 : Adapted (p0.2 : HomF) := (adapted_chart_iff q0 q0 (mem_chart_source _ q0)).mpr hq0.2
  have ha0' : Adapted (homMat M0) := by
    rw [show homMat M0 = (p0.2 : HomF) from ContinuousLinearEquiv.apply_symm_apply _ _]; exact ha0
  have hnd : e0.2 ∈ nondeg := chart_target_nondeg q0 hp0
  set H : (Fin 4 → ℝ) × (Fin 10 → ℝ) → Mat 14 := fun e => bil (Gchim e.2) M0 M0
  have hH : ContDiffAt ℝ ω H e0 := by
    have hG : ContDiffAt ℝ ω (fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) => Gchim e.2) e0 :=
      (contDiffOn_Gchim_omega.contDiffAt (isOpen_nondeg.mem_nhds hnd)).comp _ contDiffAt_snd
    have : H = bilFull ∘ fun e => (Gchim e.2, M0) := rfl
    rw [this]
    exact contDiff_bilFull.contDiffAt.comp _ (hG.prodMk contDiffAt_const)
  have hblk : ∀ e, IsBlk (H e) := fun e => isBlk_gram e.2 ha0
  obtain ⟨U1, hU1, N, hN, hNb, hNe⟩ := exists_local_frames_blk H e0 hH
    (fun e => bil_mem _ (Gchim_mem _) _) hblk hF0
  set ν : (Fin 4 → ℝ) × (Fin 10 → ℝ) → HomF := fun e => homMat (mulM M0 (N e))
  have hνa : ∀ e, Adapted (ν e) := fun e => by
    show Adapted (homMat (mulM M0 (N e)))
    rw [homMat_mulM]; exact adapted_comp_blk ha0' (hNb e)
  set T : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ)) := {e | pairHM e (p0.2 : HomF) ∈ c.target}
  have hT : T ∈ nhds e0 := by
    have hc : Continuous fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) => pairHM e (p0.2 : HomF) :=
      continuous_id.prodMk continuous_const
    exact (c.open_target.preimage hc).mem_nhds hp0
  have hTν : ∀ e ∈ T, pairHM e (ν e) ∈ c.target := fun e he =>
    (mem_chart_target_iff q0 e _ _).mp he
  refine ⟨U1 ∩ T, Filter.inter_mem hU1 hT, fun e => c.symm (pairHM e (ν e)), ?_, ?_⟩
  · have hpair : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞
        (fun e => pairHM e (ν e)) (U1 ∩ T) := by
      have h : ContDiffOn ℝ ∞ (fun e : (Fin 4 → ℝ) × (Fin 10 → ℝ) =>
          ((e, ν e) : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF)) (U1 ∩ T) := by
        refine contDiffOn_id.prodMk ?_
        have hm : ContDiffOn ℝ ∞ (fun e => mulM M0 (N e)) (U1 ∩ T) := by
          have hN' : ContDiffOn ℝ ∞ N (U1 ∩ T) :=
            ((hN.of_le (by exact le_top)) : ContDiffOn ℝ ∞ N U1).mono Set.inter_subset_left
          have : (fun e => mulM M0 (N e)) = fun e => mulCL 14 M0 (N e) := by
            funext e; exact mulM_eq _ _
          rw [this]
          exact ((mulCL 14 M0).contDiff.comp_contDiffOn hN')
        have hL : ContDiff ℝ ∞ (fun M : Mat 14 => homMat M) := by
          have : (fun M : Mat 14 => homMat M) = fun M => (ΦL : R14 →L[ℝ] CFib).comp (matL M) :=
            funext fun M => ContinuousLinearMap.ext fun x => rfl
          rw [this]
          exact contDiff_const.clm_comp matL.contDiff
        exact hL.comp_contDiffOn hm
      exact (show ContDiffOn ℝ ∞ (fun e => pairHM e (ν e)) (U1 ∩ T) from h).contMDiffOn
    exact (contMDiffOn_chart_symm (x := q0)).comp hpair fun e he => hTν e he.2
  · rintro e ⟨he1, he2⟩
    have hmem := hTν e he2
    have hsrc : c.symm (pairHM e (ν e)) ∈ c.source := c.map_target hmem
    refine ⟨⟨?_, ?_⟩, ?_, hsrc⟩
    · show Fframe (c.symm (pairHM e (ν e))) = ⟨η77, ηSig_mem 7 7⟩
      rw [Fframe_chart q0 hmem]
      apply Subtype.ext
      show (symP 14 (bil (Gchim e.2) (homMat.symm (ν e)) (homMat.symm (ν e))) : Mat 14) = η77
      have hb : bil (Gchim e.2) (homMat.symm (ν e)) (homMat.symm (ν e)) = η77 := by
        rw [show homMat.symm (ν e) = mulM M0 (N e) from homMat.symm_apply_apply _]
        apply Matrix.of.injective
        rw [bil_mulM]
        have := congrArg Matrix.of (hNe e he1)
        rw [bil_eq_mat] at this
        exact this
      rw [hb, symP_of_mem (ηSig_mem 7 7)]
    · refine (adapted_chart_iff q0 _ hsrc).mp ?_
      rw [c.right_inv hmem]; exact hνa e
    · rw [c.right_inv hmem]; rfl

end GU.Library
