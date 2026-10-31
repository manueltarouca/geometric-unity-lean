import GU.Bundle.ChimFrames
import GU.Library.RegularValue

/-!
# The orthonormal frame bundle of the chimeric bundle is a smooth submanifold (L4e)

(i) The model of `HomTotM X` is `HomModel = ModelProd (ModelProd ℝ⁴ ℝ¹⁰) HomF`; it gets the
product normed structure, and `IsManifold` transfers to `𝓘(ℝ, HomModel)` (`homTot_isManifold`).
(ii) `Fframe q = sym(qᵀ Gchim(s) q)` has `levelSet Fframe η₇₇ = orthoSetM` (`levelSet_Fframe`).
(iii) In every total-space chart, `Fframe ∘ chart⁻¹ (e, h) = orthF (Gchim e.2) (homMat⁻¹ h)`
(`Fframe_chart`: chart-independent Gram entries `gram_triv`, `Gi_chart`). This is smooth on the
Lorentzian chart target and submersive at frames (`Fframe_regular`).
(iv) **`isManifold_orthoFrames`**, **`contMDiff_orthoFrames_val`**, **`fibreDim_orthoFrames`**:
`orthoSetM` (as the level-set subtype) is a smooth 105-dimensional submanifold of `HomTotM X`.
Its fibres are nonempty exactly over the (1,3) part of `Y` (`orthoM_iff_13`); over (3,1) points
they are empty. The O(7,7) action (algebra) is in `FrameAction.lean`; its smoothness is in `FrameActionSmooth.lean`; local triviality is open.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- The model space of `HomTotM`. -/
abbrev HomModel := ModelProd (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) HomF

noncomputable instance : NormedAddCommGroup HomModel :=
  inferInstanceAs (NormedAddCommGroup (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF))
noncomputable instance : NormedSpace ℝ HomModel :=
  inferInstanceAs (NormedSpace ℝ (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF))
instance finDim_HomF : FiniteDimensional ℝ HomF :=
  LinearEquiv.finiteDimensional homMat.toLinearEquiv

instance : FiniteDimensional ℝ HomModel :=
  Module.Finite.prod (R := ℝ) (M := (Fin 4 → ℝ) × (Fin 10 → ℝ)) (N := HomF)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **`HomTotM` is a smooth manifold over the self-model** `𝓘(ℝ, HomModel)`. -/
instance homTot_isManifold : IsManifold 𝓘(ℝ, HomModel) ∞ (HomTotM X) := by
  have h : IsManifold (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
      (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod (modelWithCornersSelf ℝ HomF)) ∞ (HomTotM X) :=
    inferInstance
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  have hc := (HasGroupoid.compatible (G := contDiffGroupoid ∞ (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
      (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod (modelWithCornersSelf ℝ HomF))) he he').1
  simpa [contDiffPregroupoid, Function.comp_def] using hc

/-- The frame map `HomTotM → Sym(14)`. -/
noncomputable def Fframe (q : HomTotM X) : symS 14 :=
  orthF (Gchim ((q.proj : Sym2TX X).2)) (homMat.symm q.2)

/-- **`orthoSetM` is the level set `Fframe⁻¹{η₇₇}`.** -/
theorem levelSet_Fframe :
    levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩ = orthoSetM := by
  ext q
  rw [mem_orthoSetM_iff_mat]
  show orthF _ _ = _ ↔ _
  constructor
  · intro h; exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h
  · intro h
    apply Subtype.ext
    show (symP 14 (bil _ _ _) : Mat 14) = η77
    rw [symP_of_mem (bil_mem (Gchim ((q.proj : Sym2TX X).2)) (Gchim_mem _) (homMat.symm q.2)), h]

/-! ### (iii) `Fframe` in total-space charts -/

/-- Gram entries of `HomTot` frames are chart-independent (the `key` of `mem_orthoSet_iff`). -/
lemma gram_localTriv (i : atlas (Fin 4 → ℝ) X) (p : HomTot X) (hp : πY p.proj ∈ (Zt X).baseSet i)
    (u w : CFib) :
    Bmod (Gi i p.proj) ((((frameCore (X := X)).localTriv i p).2 : EndC) u)
      ((((frameCore (X := X)).localTriv i p).2 : EndC) w) =
    Bmod (Gpt p.proj) ((show EndC from p.2) u) ((show EndC from p.2) w) := by
  have hx : πY p.proj ∈ (Zt X).baseSet ((Zt X).indexAt (πY p.proj)) ∩ (Zt X).baseSet i :=
    ⟨(Zt X).mem_baseSet_at _, hp⟩
  rw [VectorBundleCore.localTriv_apply, Gi_eq]
  show Bmod _ (gX ((Zt X).indexAt (πY p.proj)) i _ _) (gX ((Zt X).indexAt (πY p.proj)) i _ _) = _
  rw [gX_eq_TP _ _ _ hx, gX_eq_TP _ _ _ hx]
  exact GU.Bmod_covariant _ _ _ _ _

/-- **Gram entries in a `HomTotM` trivialisation.** -/
lemma gram_triv (y0 : Yobs X) (q : HomTotM X)
    (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) (x x' : R14) :
    Bmod (Gpt q.proj) ((show HomF from q.2) x) ((show HomF from q.2) x') =
      Bmod (Gi (achart (Fin 4 → ℝ) (πY y0)) q.proj)
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
  exact (gram_localTriv (achart (Fin 4 → ℝ) (πY y0)) (ofM q) hi _ _).symm

/-- The chart-`a` metric is the chart fibre coordinate. Proved by `rfl` through the `Opens`
charted space, `FiberBundle.chartedSpace`, `VectorBundleCore.trivializationAt = localTriv (indexAt)`
and `tangentBundleCore.indexAt = achart`; if a Mathlib bump breaks it, use
`FiberBundle.chartedSpace_chartAt` and `VectorBundleCore.localTriv_apply`. -/
lemma Gi_chart (a y : Yobs X) : Gi (achart (Fin 4 → ℝ) (πY a)) y =
    symMat ((chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a y).2) := rfl

/-- Entries of `qᵀ Gchim(s) q` for `q = homMat⁻¹ h`. -/
lemma bil_homMat_entry (s : Fin 10 → ℝ) (h : HomF) (i j : Fin 14) :
    bil (Gchim s) (homMat.symm h) (homMat.symm h) i j =
      Bmod (symMat s) (h (Pi.single i 1)) (h (Pi.single j 1)) := by
  have hq : ∀ x, ΦL (Matrix.of (homMat.symm h) *ᵥ x) = h x := fun x => by
    rw [← homMat_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [← hq, ← hq, Bmod_Φ]
  set M := Matrix.of (homMat.symm h)
  calc bil (Gchim s) (homMat.symm h) (homMat.symm h) i j
      = (Matrix.of (bil (Gchim s) (homMat.symm h) (homMat.symm h))) i j := rfl
    _ = (Mᵀ * Matrix.of (Gchim s) * M) i j := by rw [bil_eq_mat]
    _ = Pi.single i 1 ⬝ᵥ ((Mᵀ * Matrix.of (Gchim s) * M) *ᵥ Pi.single j 1) :=
        (single_dot_mulVec _ i j).symm
    _ = _ := by rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma orthF_eq_of_entries {G G' : Mat 14} {M M' : Mat 14}
    (h : ∀ i j, bil G M M i j = bil G' M' M' i j) : orthF G M = orthF G' M' := by
  unfold orthF; congr 1; funext i j; exact h i j

/-- **`Fframe` in a total-space chart** is `orthF (Gchim e.2) (homMat⁻¹ h)`. -/
theorem Fframe_chart (a : HomTotM X) {p : HomModel}
    (hp : p ∈ (chartAt HomModel a).target) :
    Fframe ((chartAt HomModel a).symm p) = orthF (Gchim p.1.2) (homMat.symm p.2) := by
  set q := (chartAt HomModel a).symm p
  have hqs : q ∈ (chartAt HomModel a).source := (chartAt HomModel a).map_target hp
  have hpq : chartAt HomModel a q = p := (chartAt HomModel a).right_inv hp
  have hsrc := hqs
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hsrc hpq
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_univ, and_true, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id] at hsrc hpq
  have hq1 : ((trivializationAt HomF (HomCb (X := X)) a.proj) q).1 = q.proj :=
    Trivialization.coe_fst _ hsrc.1
  have hb : q.proj ∈ (trivializationAt CFib (Cb (X := X)) a.proj).baseSet := by
    have := (Trivialization.mem_source _).mp hsrc.1
    exact this.2
  have e2 : ((chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj).prod
      (OpenPartialHomeomorph.refl HomF)) ((trivializationAt HomF (HomCb (X := X)) a.proj) q) =
      (chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj q.proj,
        ((trivializationAt HomF (HomCb (X := X)) a.proj) q).2) := by
    rw [OpenPartialHomeomorph.prod_apply]; simp only [OpenPartialHomeomorph.refl_apply, id]; rw [hq1]
  rw [← hpq]
  erw [e2]
  unfold Fframe
  apply orthF_eq_of_entries
  intro i j
  refine (bil_homMat_entry (((q.proj : Sym2TX X).2 : Fin 10 → ℝ)) q.2 i j).trans
    (((gram_triv a.proj q hb _ _).trans ?_).trans (bil_homMat_entry _ _ i j).symm)
  rw [Gi_chart]

/-- The linear chart-to-frame-family map `p ↦ (p.1.2, homMat⁻¹ p.2)`. -/
noncomputable def Lchart : HomModel →L[ℝ] (Fin 10 → ℝ) × Mat 14 :=
  ((ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) (Fin 10 → ℝ)).comp
      (ContinuousLinearMap.fst ℝ ((Fin 4 → ℝ) × (Fin 10 → ℝ)) HomF)).prod
    ((homMat.symm : HomF →L[ℝ] Mat 14).comp (ContinuousLinearMap.snd ℝ ((Fin 4 → ℝ) × (Fin 10 → ℝ)) HomF))

lemma Lchart_apply (p : HomModel) : Lchart p = (p.1.2, homMat.symm p.2) := rfl

lemma Lchart_surjective : Function.Surjective Lchart := by
  rintro ⟨s, M⟩
  exact ⟨((0, s), homMat M), by rw [Lchart_apply]; simp⟩

lemma Fframe_chart' (a : HomTotM X) {p : HomModel} (hp : p ∈ (chartAt HomModel a).target) :
    (Fframe ∘ (chartAt HomModel a).symm) p = frameF0 Gchim (Lchart p) :=
  Fframe_chart a hp

lemma chart_target_nondeg (a : HomTotM X) {p : HomModel} (hp : p ∈ (chartAt HomModel a).target) :
    (Lchart p).1 ∈ nondeg := by
  set q := (chartAt HomModel a).symm p
  have hqs : q ∈ (chartAt HomModel a).source := (chartAt HomModel a).map_target hp
  have hpq : chartAt HomModel a q = p := (chartAt HomModel a).right_inv hp
  have hsrc := hqs
  rw [show chartAt HomModel a = _ from FiberBundle.chartedSpace_chartAt a] at hsrc hpq
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_univ, and_true, OpenPartialHomeomorph.coe_trans, Function.comp_apply] at hsrc hpq
  have hq1 : ((trivializationAt HomF (HomCb (X := X)) a.proj) q).1 = q.proj :=
    Trivialization.coe_fst _ hsrc.1
  have hb : q.proj ∈ (trivializationAt CFib (Cb (X := X)) a.proj).baseSet :=
    ((Trivialization.mem_source _).mp hsrc.1).2
  have hi : πY q.proj ∈ (Zt X).baseSet (achart (Fin 4 → ℝ) (πY a.proj)) := by
    rw [Cb_baseSet] at hb; exact hb
  have hdet := Gi_det_ne (achart (Fin 4 → ℝ) (πY a.proj)) q.proj hi
  rw [Gi_chart] at hdet
  rw [← hpq, Lchart_apply]
  show (symMat _).det ≠ 0
  rw [OpenPartialHomeomorph.prod_apply]; simp only [OpenPartialHomeomorph.refl_apply, id]
  rw [Trivialization.coe_coe, hq1]
  exact hdet

/-- **`orthoSetM` is a regular level set of `Fframe`.** -/
theorem Fframe_regular : RegularLevel HomModel (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩ := by
  have hU : IsOpen (Prod.fst ⁻¹' nondeg : Set ((Fin 10 → ℝ) × Mat 14)) :=
    isOpen_nondeg.preimage continuous_fst
  have hF0 := contDiffOn_frameF0 (G := Gchim) (U := nondeg) contDiffOn_Gchim
  refine ⟨fun a => ?_, fun a x hx hfx => ?_⟩
  · refine ((hF0.comp Lchart.contDiff.contDiffOn fun p hp => chart_target_nondeg a hp)).congr
      fun p hp => Fframe_chart' a hp
  · set p := chartAt HomModel a x
    have hp : p ∈ (chartAt HomModel a).target := (chartAt HomModel a).map_source hx
    have hev : (Fframe ∘ (chartAt HomModel a).symm) =ᶠ[nhds p] (frameF0 Gchim ∘ Lchart) :=
      Filter.eventually_of_mem ((chartAt HomModel a).open_target.mem_nhds hp)
        fun p' hp' => Fframe_chart' a hp'
    rw [hev.fderiv_eq]
    have hnd := chart_target_nondeg a hp
    have hd : HasFDerivAt (frameF0 Gchim) (fderiv ℝ (frameF0 Gchim) (Lchart p)) (Lchart p) :=
      ((hF0.contDiffAt (hU.mem_nhds hnd)).differentiableAt (by simp)).hasFDerivAt
    rw [(hd.comp p Lchart.hasFDerivAt).fderiv]
    have hlev : bil (Gchim (Lchart p).1) (Lchart p).2 (Lchart p).2 = η77 := by
      have h1 : frameF0 Gchim (Lchart p) = ⟨η77, ηSig_mem 7 7⟩ := by
        rw [← Fframe_chart' a hp]; simp only [Function.comp_apply, p,
          (chartAt HomModel a).left_inv hx]; exact hfx
      exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h1
    have hs := frameF0_surj (G := Gchim) isOpen_nondeg contDiffOn_Gchim (fun s _ => Gchim_mem s)
      (ηSig_mem 7 7) (ηSig_sq 7 7) hnd hlev
    show LinearMap.range ((fderiv ℝ (frameF0 Gchim) (Lchart p)).toLinearMap.comp
      (Lchart.toLinearMap)) = ⊤
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr Lchart_surjective)]
    exact hs

/-! ### (iv) The orthonormal frame bundle is a smooth submanifold -/

instance : Nontrivial (symS 14) := ⟨⟨0, ⟨η77, ηSig_mem 7 7⟩, η77_ne_zero.symm⟩⟩
instance : Module.Free ℝ HomF := Module.Free.of_divisionRing ℝ HomF

/-- **The `(7,7)`-orthonormal frames of the chimeric bundle (over the (1,3) part of `Y`) form a
smooth manifold**
(as the regular level set `Fframe⁻¹{η₇₇} = orthoSetM`, `levelSet_Fframe`). -/
theorem isManifold_orthoFrames :
    letI := regCharted (Fframe_regular (X := X))
    IsManifold 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞
      (levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩) :=
  isManifold_regularLevel _

/-- **... and a smooth submanifold of the hom bundle `HomTotM`.** -/
theorem contMDiff_orthoFrames_val :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ContMDiff 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) 𝓘(ℝ, HomModel) ∞
      (Subtype.val : levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩ → HomTotM X) :=
  contMDiff_regularLevel_val _

lemma finrank_HomF : Module.finrank ℝ HomF = 196 := by
  rw [← homMat.toLinearEquiv.finrank_eq]
  simp [Mat, Module.finrank_pi_fintype]

/-- **Dimension 105** `= 14 (Y) + 91 (O(7,7))`. -/
lemma fibreDim_orthoFrames : fibreDim HomModel (symS 14) = 105 := by
  have h1 : Module.finrank ℝ HomModel = 210 := by
    show Module.finrank ℝ (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF) = 210
    rw [Module.finrank_prod, Module.finrank_prod, finrank_HomF]; simp
  have h2 : Module.finrank ℝ (symS 14) = 105 := by rw [finrank_symS]; rfl
  unfold fibreDim; rw [h1, h2]

end GU.Library
