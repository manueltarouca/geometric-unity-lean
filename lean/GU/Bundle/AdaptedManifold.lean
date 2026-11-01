import GU.Bundle.BlockGroup

/-!
# The adapted frames are a smooth submanifold

On the open set `Ω ⊆ HomTotM` (`isOpen_Ωset`) the map
`fA q = (Fframe q, (H*-Gram q)(vI a, hI b))` has level set `fA⁻¹(η₇₇, 0) = AFr`
(`mem_AFr_of_level`, `level_of_mem_AFr`), and the level is regular (`fA_regular`): in charts
`fA = F3b ∘ Lchart`, and the derivative of `F3b` in the frame direction `M ↦ M + M Y` is onto
(`F3b_surj`; with `Y = η Z`, the frame part is `Z + Zᵀ` and the off-block `H*`-Gram part is
`Z_{hI b, vI a}`). So **`AFrM`** (the level set) is a smooth manifold (`isManifold_AFrM`), and its
inclusion into `HomTotM` is smooth.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The codomain of `fA`. -/
abbrev FA := symS 14 × (Fin 10 → Fin 4 → ℝ)

lemma covec_add' (p p' : (Fin 4 → ℝ) →L[ℝ] ℝ) : covec (p + p') = covec p + covec p' := by
  ext i; simp [covec]
lemma covec_smul' (r : ℝ) (p : (Fin 4 → ℝ) →L[ℝ] ℝ) : covec (r • p) = r • covec p := by
  ext i; simp [covec]
lemma covec_zero' : covec (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by ext i; simp [covec]

/-- Linearity of `BHf` in the first slot along a frame. -/
lemma BHf_lin_left (G : Matrix (Fin 4) (Fin 4) ℝ) (h : HomF) (v : R14) (u : CFib) :
    BHf G (h v) u = ∑ k, v k * BHf G (h (Pi.single k 1)) u := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  have hc : ∀ (s : Finset (Fin 14)) (f : Fin 14 → (Fin 4 → ℝ) →L[ℝ] ℝ),
      covec (∑ k ∈ s, f k) = ∑ k ∈ s, covec (f k) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [covec_zero']
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, covec_add', ih]
  unfold BHf
  rw [Prod.snd_sum, hc, sum_dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Pi.single k (v k) = v k • (Pi.single k 1 : R14) by
    ext i; by_cases e : i = k <;> simp [e], map_smul, Prod.smul_snd, covec_smul', smul_dotProduct,
    smul_eq_mul]

/-! ### The chart map `F3b` -/

/-- The bilinear off-block `H*`-Gram. -/
def β₀ (s : Fin 10 → ℝ) : Mat 14 →ₗ[ℝ] Mat 14 →ₗ[ℝ] (Fin 10 → Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun A C => fun a b =>
      BHf (symMat s) (homMat A (Pi.single (vI a) 1)) (homMat C (Pi.single (hI b) 1)))
    (fun A A' C => by
      funext a b
      simp only [map_add, ContinuousLinearMap.add_apply, Prod.snd_add, covec_add', BHf,
        add_dotProduct, Pi.add_apply])
    (fun r A C => by
      funext a b
      simp only [map_smul, ContinuousLinearMap.smul_apply, Prod.smul_snd, covec_smul', BHf,
        smul_dotProduct, Pi.smul_apply, smul_eq_mul])
    (fun A C C' => by
      funext a b
      simp only [map_add, ContinuousLinearMap.add_apply, Prod.snd_add, covec_add', BHf,
        mulVec_add, dotProduct_add, Pi.add_apply])
    (fun r A C => by
      funext a b
      simp only [map_smul, ContinuousLinearMap.smul_apply, Prod.smul_snd, covec_smul', BHf,
        mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul])

def βs (s : Fin 10 → ℝ) : Mat 14 →L[ℝ] Mat 14 →L[ℝ] (Fin 10 → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mat 14 →ₗ[ℝ] (Fin 10 → Fin 4 → ℝ)) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      β₀ s)

lemma βs_apply (s : Fin 10 → ℝ) (A C : Mat 14) (a : Fin 10) (b : Fin 4) :
    βs s A C a b = BHf (symMat s) (homMat A (Pi.single (vI a) 1)) (homMat C (Pi.single (hI b) 1)) :=
  rfl

/-- The chart expression of `fA`, on `(metric, frame matrix)`. -/
def F3b (x : (Fin 10 → ℝ) × Mat 14) : FA :=
  (frameF0 Gchim x, fun a b =>
    BHf (symMat x.1) (homMat x.2 (Pi.single (vI a) 1)) (homMat x.2 (Pi.single (hI b) 1)))

lemma contDiff_homMat : ContDiff ℝ ∞ (fun M : Mat 14 => homMat M) := by
  have : (fun M : Mat 14 => homMat M) = fun M => (ΦL : R14 →L[ℝ] CFib).comp (matL M) :=
    funext fun M => ContinuousLinearMap.ext fun x => rfl
  rw [this]
  exact contDiff_const.clm_comp matL.contDiff

lemma contDiffOn_F3b : ContDiffOn ℝ ∞ F3b (Prod.fst ⁻¹' nondeg) := by
  refine (contDiffOn_frameF0 contDiffOn_Gchim).prodMk ?_
  refine ContDiff.contDiffOn (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_)
  have hm : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × Mat 14 =>
      (((0 : Fin 4 → ℝ), x.1), homMat x.2) : (Fin 10 → ℝ) × Mat 14 → ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) :=
    (contDiff_const.prodMk contDiff_fst).prodMk (contDiff_homMat.comp contDiff_snd)
  exact (contDiff_BHf_chart (vI a) (hI b)).comp hm

/-! ### Surjectivity of the derivative -/

/-- The correction matrix: `Z + Zᵀ = S` and `Z (hI b) (vI a) = w a b`. -/
def Zm (S : Mat 14) (w : Fin 10 → Fin 4 → ℝ) : Mat 14 := fun i j =>
  S i j / 2 +
    (if i ∈ SH ∧ j ∉ SH then w (vInv j) (hInv i) - S i j / 2
     else if i ∉ SH ∧ j ∈ SH then -(w (vInv i) (hInv j) - S j i / 2) else 0)

lemma Zm_sym {S : Mat 14} (hS : S ∈ symS 14) (w : Fin 10 → Fin 4 → ℝ) (i j : Fin 14) :
    Zm S w i j + Zm S w j i = S i j := by
  unfold Zm
  have e := hS i j
  by_cases hi : i ∈ SH <;> by_cases hj : j ∈ SH <;> simp [hi, hj, e] <;> ring

lemma Zm_hv (S : Mat 14) (w : Fin 10 → Fin 4 → ℝ) (a : Fin 10) (b : Fin 4) :
    Zm S w (hI b) (vI a) = w a b := by
  unfold Zm
  simp [hI_mem, vI_not_mem, vInv_vI, hInv_hI]

lemma η77_sq (i : Fin 14) : η77 i i * η77 i i = 1 := by
  rw [η77_apply', if_pos rfl]; split_ifs <;> norm_num

/-- **The derivative of `F3b` at an adapted orthonormal frame is onto.** -/
theorem F3b_surj {s : Fin 10 → ℝ} (hnd : s ∈ nondeg) {M : Mat 14}
    (hO : bil (Gchim s) M M = η77) (ha : Adapted (homMat M)) :
    (fderiv ℝ F3b (s, M)).range = ⊤ := by
  set K := Gchim s
  have hU : IsOpen (Prod.fst ⁻¹' nondeg : Set ((Fin 10 → ℝ) × Mat 14)) :=
    isOpen_nondeg.preimage continuous_fst
  have hF : HasFDerivAt F3b (fderiv ℝ F3b (s, M)) (s, M) :=
    ((contDiffOn_F3b.contDiffAt (hU.mem_nhds hnd)).differentiableAt (by simp)).hasFDerivAt
  set N : Mat 14 → Mat 14 := fun Y => M + mulCL 14 M Y
  have hN0 : N 0 = M := by simp [N]
  have hN : HasFDerivAt N (mulCL 14 M) 0 := (mulCL 14 M).hasFDerivAt.const_add M
  have hℓ : HasFDerivAt (fun Y => (s, N Y)) ((0 : Mat 14 →L[ℝ] (Fin 10 → ℝ)).prod (mulCL 14 M)) 0 :=
    (hasFDerivAt_const s 0).prodMk hN
  have hO' : HasFDerivAt (orthF K) (fderiv ℝ (orthF K) M) (N 0) := by
    rw [hN0]; exact ((orthF_contDiff K).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h1 := hO'.comp (0 : Mat 14) hN
  have h2 := (βs s).hasFDerivAt_of_bilinear hN hN
  have hE : HasFDerivAt (F3b ∘ fun Y => (s, N Y))
      ((fderiv ℝ F3b (s, M)).comp ((0 : Mat 14 →L[ℝ] (Fin 10 → ℝ)).prod (mulCL 14 M))) 0 := by
    have hF' : HasFDerivAt F3b (fderiv ℝ F3b (s, M)) (s, N 0) := by rw [hN0]; exact hF
    exact hF'.comp (0 : Mat 14) hℓ
  have hfun : (F3b ∘ fun Y => (s, N Y)) = fun Y => (orthF K (N Y), βs s (N Y) (N Y)) := rfl
  rw [hfun] at hE
  have huniq := hE.unique (h1.prodMk h2)
  rw [LinearMap.range_eq_top]
  rintro ⟨S, w⟩
  set Z := Zm (S : Mat 14) w
  set Y : Mat 14 := mulM η77 Z
  refine ⟨((0 : Mat 14 →L[ℝ] (Fin 10 → ℝ)).prod (mulCL 14 M)) Y, ?_⟩
  show ((fderiv ℝ F3b (s, M)).comp ((0 : Mat 14 →L[ℝ] (Fin 10 → ℝ)).prod (mulCL 14 M))) Y = (S, w)
  rw [huniq]
  have hMY : mulCL 14 M Y = mulM M Y := (mulM_eq _ _).symm
  have hEta : (Matrix.of η77)ᵀ = Matrix.of η77 := mat_symm_of_mem (ηSig_mem 7 7)
  have hsq : Matrix.of η77 * Matrix.of η77 = 1 := ηSig_sq 7 7
  have hOm : (Matrix.of M)ᵀ * Matrix.of K * Matrix.of M = Matrix.of η77 := by
    rw [← bil_eq_mat, hO]
  refine Prod.ext ?_ ?_
  · -- frame part
    show fderiv ℝ (orthF K) M (mulCL 14 M Y) = S
    rw [fderiv_orthF, hMY]
    apply Subtype.ext
    have hsum : bil K M (mulM M Y) + bil K (mulM M Y) M = (S : Mat 14) := by
      apply Matrix.of.injective
      rw [← Matrix.of_add_of, bil_eq_mat, bil_eq_mat]
      show (Matrix.of M)ᵀ * Matrix.of K * (Matrix.of M * (Matrix.of η77 * Matrix.of Z)) +
          (Matrix.of M * (Matrix.of η77 * Matrix.of Z))ᵀ * Matrix.of K * Matrix.of M = Matrix.of S
      have e1 : (Matrix.of M)ᵀ * Matrix.of K * (Matrix.of M * (Matrix.of η77 * Matrix.of Z)) =
          Matrix.of Z := by
        calc _ = ((Matrix.of M)ᵀ * Matrix.of K * Matrix.of M) * Matrix.of η77 * Matrix.of Z := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.of Z := by rw [hOm, hsq, Matrix.one_mul]
      have e2 : (Matrix.of M * (Matrix.of η77 * Matrix.of Z))ᵀ * Matrix.of K * Matrix.of M =
          (Matrix.of Z)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hEta]
        calc _ = (Matrix.of Z)ᵀ * Matrix.of η77 * ((Matrix.of M)ᵀ * Matrix.of K * Matrix.of M) := by
              simp only [Matrix.mul_assoc]
          _ = (Matrix.of Z)ᵀ := by rw [hOm, Matrix.mul_assoc, hsq, Matrix.mul_one]
      rw [e1, e2]
      ext i j
      exact Zm_sym S.2 w i j
    show (symP 14 (bil K M (mulM M Y) + bil K (mulM M Y) M) : Mat 14) = S
    rw [hsum, symP_of_mem S.2]
  · -- off-block `H*` part
    show βs s (N 0) (mulCL 14 M Y) + βs s (mulCL 14 M Y) (N 0) = w
    rw [hN0, hMY]
    funext a b
    rw [Pi.add_apply, Pi.add_apply, βs_apply, βs_apply]
    have hzero : BHf (symMat s) (homMat M (Pi.single (vI a) 1)) (homMat (mulM M Y) (Pi.single (hI b) 1)) = 0 := by
      unfold BHf; rw [ha.2 _ (vI_not_mem a), covec_zero', zero_dotProduct]
    rw [hzero, zero_add, homMat_mulM, ContinuousLinearMap.comp_apply, BHf_lin_left]
    have hent : ∀ k, BHf (symMat s) (homMat M (Pi.single k 1)) (homMat M (Pi.single (hI b) 1)) =
        if k ∈ SH then η77 k (hI b) else 0 := by
      intro k
      split_ifs with hk
      · have e' := bil_homMat_entry s (homMat M) k (hI b)
        rw [ContinuousLinearEquiv.symm_apply_apply] at e'
        have e := e'.symm.trans (congrFun (congrFun hO k) (hI b))
        rw [Bmod_eq_split, ha.1 k hk] at e
        have h0 : BVf (symMat s) 0 (homMat M (Pi.single (hI b) 1)).1 = 0 := by
          have : symMat (0 : Fin 10 → ℝ) = 0 := by ext; simp [symMat]
          simp [BVf, chimY, this]
        rw [h0, zero_add] at e
        exact e
      · unfold BHf; rw [ha.2 k hk, covec_zero', zero_dotProduct]
    simp only [matCLM_apply, mulVec_single_apply, hent]
    rw [Finset.sum_eq_single (hI b)]
    · rw [if_pos (hI_mem b)]
      have hY : Y (hI b) (vI a) = η77 (hI b) (hI b) * Z (hI b) (vI a) := by
        show (Matrix.of η77 * Matrix.of Z) (hI b) (vI a) = _
        rw [Matrix.mul_apply, Finset.sum_eq_single (hI b)]
        · rfl
        · intro l _ hl; rw [show Matrix.of η77 (hI b) l = 0 by rw [η77_apply, if_neg (Ne.symm hl)],
            zero_mul]
        · simp
      rw [hY, show Z (hI b) (vI a) = w a b from Zm_hv _ w a b]
      calc η77 (hI b) (hI b) * w a b * η77 (hI b) (hI b)
          = (η77 (hI b) (hI b) * η77 (hI b) (hI b)) * w a b := by ring
        _ = w a b := by rw [η77_sq, one_mul]
    · intro k _ hk
      split_ifs
      · rw [η77_apply', if_neg hk, mul_zero]
      · rw [mul_zero]
    · simp

/-! ### The regular level -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- `Ω` as an open submanifold of `HomTotM`. -/
def ΩO (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Opens (HomTotM X) :=
  ⟨Ωset X, isOpen_Ωset⟩

example : IsManifold 𝓘(ℝ, HomModel) ∞ (ΩO X) := inferInstance

/-- The defining map of the adapted frames. -/
def fA (q : ΩO X) : FA :=
  (Fframe (q : HomTotM X), fun a b => gramH (q : HomTotM X) (vI a) (hI b))

/-- The level `(η₇₇, 0)`. -/
def cA : FA := (⟨η77, ηSig_mem 7 7⟩, 0)

instance : Nontrivial FA :=
  ⟨⟨(0, 0), cA, fun h => η77_ne_zero (congrArg Prod.fst h).symm⟩⟩

/-- **The level set of `fA` is `AFr`.** -/
theorem mem_levelA_iff (q : ΩO X) : q ∈ levelSet (fA (X := X)) cA ↔ (q : HomTotM X) ∈ AFr X := by
  constructor
  · intro hq
    have h1 : Fframe (q : HomTotM X) = ⟨η77, ηSig_mem 7 7⟩ := congrArg Prod.fst hq
    have h2 : ∀ a b, gramH (q : HomTotM X) (vI a) (hI b) = 0 := fun a b =>
      congrFun (congrFun (congrArg Prod.snd hq) a) b
    exact mem_AFr_of_level h1 q.2 h2
  · intro hq
    obtain ⟨-, h0⟩ := level_of_mem_AFr hq
    exact Prod.ext hq.1 (funext fun a => funext fun b => h0 a b)

lemma fA_chart (a : ΩO X) {p : HomModel} (hp : p ∈ (chartAt HomModel a).target) :
    fA ((chartAt HomModel a).symm p) = F3b (Lchart p) := by
  set c := chartAt HomModel (a : HomTotM X)
  have hca : chartAt HomModel a = c.subtypeRestr ⟨a⟩ := TopologicalSpace.Opens.chartAt_eq
  rw [hca] at hp ⊢
  have hpc : p ∈ c.target := c.subtypeRestr_target_subset ⟨a⟩ hp
  have hv : ((c.subtypeRestr ⟨a⟩).symm p : HomTotM X) = c.symm p :=
    c.subtypeRestr_symm_apply ⟨a⟩ hp
  have hsrc : c.symm p ∈ c.source := c.map_target hpc
  unfold fA
  rw [hv]
  refine Prod.ext (Fframe_chart' (a : HomTotM X) hpc) (funext fun i => funext fun j => ?_)
  show gramH (c.symm p) (vI i) (hI j) = BHf (symMat (Lchart p).1)
    (homMat (Lchart p).2 (Pi.single (vI i) 1)) (homMat (Lchart p).2 (Pi.single (hI j) 1))
  rw [gramH_chart _ _ hsrc, c.right_inv hpc]
  show _ = BHf (symMat (Lchart p).1) (homMat (Lchart p).2 _) (homMat (Lchart p).2 _)
  rw [Lchart_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- **The adapted frames are a regular level set.** -/
theorem fA_regular : RegularLevel HomModel (fA (X := X)) cA := by
  refine ⟨fun a => ?_, fun a x hx hfx => ?_⟩
  · have hsub : (chartAt HomModel a).target ⊆ (chartAt HomModel (a : HomTotM X)).target :=
      (chartAt HomModel (a : HomTotM X)).subtypeRestr_target_subset ⟨a⟩
    refine ((contDiffOn_F3b.comp Lchart.contDiff.contDiffOn fun p hp =>
      chart_target_nondeg (a : HomTotM X) (hsub hp))).congr fun p hp => fA_chart a hp
  · set c := chartAt HomModel (a : HomTotM X)
    have hca : chartAt HomModel a = c.subtypeRestr ⟨a⟩ := TopologicalSpace.Opens.chartAt_eq
    set p := chartAt HomModel a x
    have hp : p ∈ (chartAt HomModel a).target := (chartAt HomModel a).map_source hx
    have hev : (fA ∘ (chartAt HomModel a).symm) =ᶠ[nhds p] (F3b ∘ Lchart) :=
      Filter.eventually_of_mem ((chartAt HomModel a).open_target.mem_nhds hp)
        fun p' hp' => fA_chart a hp'
    rw [hev.fderiv_eq]
    have hsub : (chartAt HomModel a).target ⊆ c.target := by
      rw [hca]; exact c.subtypeRestr_target_subset ⟨a⟩
    have hnd := chart_target_nondeg (a : HomTotM X) (hsub hp)
    have hU : IsOpen (Prod.fst ⁻¹' nondeg : Set ((Fin 10 → ℝ) × Mat 14)) :=
      isOpen_nondeg.preimage continuous_fst
    have hd : HasFDerivAt F3b (fderiv ℝ F3b (Lchart p)) (Lchart p) :=
      ((contDiffOn_F3b.contDiffAt (hU.mem_nhds hnd)).differentiableAt (by simp)).hasFDerivAt
    rw [(hd.comp p Lchart.hasFDerivAt).fderiv]
    -- the frame is adapted and orthonormal
    have hxs : (x : HomTotM X) ∈ c.source := by
      rw [hca] at hx; rwa [OpenPartialHomeomorph.subtypeRestr_source] at hx
    have hpx : p = c x := by rw [show p = chartAt HomModel a x from rfl, hca]; rfl
    have hAFr : (x : HomTotM X) ∈ AFr X := (mem_levelA_iff x).mp hfx
    have hlev : bil (Gchim (Lchart p).1) (Lchart p).2 (Lchart p).2 = η77 := by
      have h1 : frameF0 Gchim (Lchart p) = ⟨η77, ηSig_mem 7 7⟩ := by
        rw [← Fframe_chart' (a : HomTotM X) (hsub hp), Function.comp_apply, hpx, c.left_inv hxs]
        exact hAFr.1
      exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h1
    have hadp : Adapted (homMat (Lchart p).2) := by
      rw [Lchart_apply, ContinuousLinearEquiv.apply_symm_apply, hpx]
      exact (adapted_chart_iff _ _ hxs).mpr hAFr.2
    have hs := F3b_surj hnd hlev hadp
    show LinearMap.range ((fderiv ℝ F3b (Lchart p)).toLinearMap.comp (Lchart.toLinearMap)) = ⊤
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr Lchart_surjective)]
    exact hs

/-- **Dimension 65** `= 14 (Y) + 45 (O(6,4)) + 6 (O(1,3))`. -/
lemma fibreDim_AFrM : fibreDim HomModel FA = 65 := by
  have h1 : Module.finrank ℝ HomModel = 210 := by
    show Module.finrank ℝ (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) = 210
    rw [Module.finrank_prod, Module.finrank_prod, finrank_HomF]; simp
  have h2 : Module.finrank ℝ FA = 145 := by
    show Module.finrank ℝ (symS 14 × (Fin 10 → Fin 4 → ℝ)) = 145
    rw [Module.finrank_prod, finrank_symS, Module.finrank_pi_fintype]; simp [Module.finrank_pi]; rfl
  unfold fibreDim; rw [h1, h2]

/-- **The adapted orthonormal frames, as a manifold.** -/
abbrev AFrM (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] := levelSet (fA (X := X)) cA

instance : ChartedSpace (Fin (fibreDim HomModel FA) → ℝ) (AFrM X) := regCharted fA_regular

/-- **`AFr` is a smooth manifold** (of dimension 65, `fibreDim_AFrM`). -/
instance isManifold_AFrM : IsManifold 𝓘(ℝ, Fin (fibreDim HomModel FA) → ℝ) ∞ (AFrM X) :=
  isManifold_regularLevel fA_regular

/-- The underlying frame. -/
def frameA (p : AFrM X) : HomTotM X := ((p : ΩO X) : HomTotM X)

lemma frameA_mem (p : AFrM X) : frameA p ∈ AFr X := (mem_levelA_iff _).mp p.2

/-- **The inclusion `AFrM → HomTotM` is smooth.** -/
theorem contMDiff_frameA :
    ContMDiff 𝓘(ℝ, Fin (fibreDim HomModel FA) → ℝ) 𝓘(ℝ, HomModel) ∞ (frameA (X := X)) :=
  contMDiff_subtype_val.comp (contMDiff_regularLevel_val fA_regular)

end

end GU.Library
