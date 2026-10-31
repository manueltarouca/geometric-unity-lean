import GU.Bundle.AdaptedFrames

/-!
# Phase 3, item 1: the inverse of the local trivialisation is smooth

In chart coordinates the inverse of `Ψ(e, g) = σ(e)·g` is `q ↦ ((c q).1, Mσ(e)⁻¹ · Mq)`, with
`Mq = homMat⁻¹ (c q).2` and `Mσ(e) = homMat⁻¹ (c (σ e)).2`. Smoothness follows from: `homMat⁻¹`
is linear (`contDiff_homMat_symm`, entrywise), matrix inversion is smooth where `det ≠ 0`
(`EntCDn.inv`), and the chart and `σ` are smooth.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- Entries of `homMat⁻¹ h`. -/
lemma homMat_symm_apply (h : HomF) (i j : Fin 14) :
    homMat.symm h i j = (ΦL.symm (h (Pi.single j 1))) i := by
  have hq := homMat_apply (homMat.symm h) (Pi.single j 1)
  rw [ContinuousLinearEquiv.apply_symm_apply, mulVec_single_one] at hq
  rw [hq, ContinuousLinearEquiv.symm_apply_apply]; rfl

/-- **`homMat⁻¹` is smooth** (entrywise: evaluation, `Φ⁻¹`, coordinate). -/
lemma contDiff_homMat_symm : ContDiff ℝ ∞ (fun h : HomF => homMat.symm h) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp_rw [homMat_symm_apply]
  have hev : ContDiff ℝ ∞ (fun h : HomF => h (Pi.single j 1)) :=
    contDiff_id.clm_apply contDiff_const
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 14 => ℝ) i).contDiff.comp
    ((ΦL.symm : CFib →L[ℝ] R14).contDiff.comp hev))

-- Projections from `HomModel`, via the plain product (`ModelProd` blocks direct instance search).
lemma contDiff_homModel_fst' :
    ContDiff ℝ ∞ (fun p : HomModel => (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p.1)) := by
  have h : ContDiff ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => p.1) := contDiff_fst
  exact h

lemma contDiff_homModel_snd' : ContDiff ℝ ∞ (fun p : HomModel => (p.2 : HomF)) := by
  have h : ContDiff ℝ ∞ (fun p : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF => p.2) := contDiff_snd
  exact h

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

section Coord

variable (q0 : HomTotM X) {U : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ))}
  {σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X}

/-- The section's frame matrix in chart coordinates. -/
noncomputable def Msec (σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X)
    (e : (Fin 4 → ℝ) × (Fin 10 → ℝ)) : Mat 14 :=
  homMat.symm ((chartAt HomModel q0 (σ e)).2 : HomF)

lemma contDiffOn_Msec
    (hσ : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U)
    (hsrc : ∀ e ∈ U, σ e ∈ (chartAt HomModel q0).source) :
    ContDiffOn ℝ ∞ (Msec q0 σ) U := by
  have hτ : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞
      (fun e => chartAt HomModel q0 (σ e)) U :=
    (contMDiffOn_chart (x := q0)).comp hσ hsrc
  have hτ' : ContDiffOn ℝ ∞ (fun e => chartAt HomModel q0 (σ e)) U :=
    contMDiffOn_iff_contDiffOn.mp hτ
  exact contDiff_homMat_symm.comp_contDiffOn (contDiff_homModel_snd'.comp_contDiffOn hτ')

lemma Msec_det_ne (hσp : ∀ e ∈ U, σ e ∈ OFr X ∧ σ e ∈ (chartAt HomModel q0).source)
    {e} (he : e ∈ U) : (Matrix.of (Msec q0 σ e)).det ≠ 0 := by
  obtain ⟨hO, hs⟩ := hσp e he
  set c := chartAt HomModel q0
  have hp : c (σ e) ∈ c.target := c.map_source hs
  have h1 : Fframe (c.symm (c (σ e))) = ⟨η77, ηSig_mem 7 7⟩ := by rw [c.left_inv hs]; exact hO
  rw [Fframe_chart q0 hp] at h1
  have hb := bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h1
  have hm := congrArg Matrix.of hb
  rw [bil_eq_mat] at hm
  exact (isUnit_frame hm).ne_zero

/-- The inverse of the section's frame matrix, entrywise smooth. -/
lemma entCD_Msec_inv
    (hσ : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U)
    (hσp : ∀ e ∈ U, σ e ∈ OFr X ∧ σ e ∈ (chartAt HomModel q0).source) :
    EntCDn ∞ U (fun e => (Matrix.of (Msec q0 σ e))⁻¹) := by
  have hM := contDiffOn_Msec q0 hσ fun e he => (hσp e he).2
  have hE : EntCDn ∞ U (fun e => Matrix.of (Msec q0 σ e)) := fun i j =>
    (contDiffOn_pi.mp (contDiffOn_pi.mp hM i) j)
  exact hE.inv fun e he => Msec_det_ne q0 hσp he

end Coord

section CoordF

variable (q0 : HomTotM X) {U : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ))}
  {σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X}

/-- The group coordinate of the inverse trivialisation, in chart coordinates. -/
noncomputable def Fg (σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X) (p : HomModel) : Mat 14 :=
  Matrix.of.symm ((Matrix.of (Msec q0 σ (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p.1)))⁻¹ *
    Matrix.of (homMat.symm (p.2 : HomF)))

lemma contDiffOn_Fg
    (hσ : ContMDiffOn 𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)) 𝓘(ℝ, HomModel) ∞ σ U)
    (hσp : ∀ e ∈ U, σ e ∈ OFr X ∧ σ e ∈ (chartAt HomModel q0).source) :
    ContDiffOn ℝ ∞ (Fg q0 σ)
      {p : HomModel | (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p.1) ∈ U} := by
  have hI := entCD_Msec_inv q0 hσ hσp
  have hH : ContDiff ℝ ∞ (fun p : HomModel => homMat.symm (p.2 : HomF)) :=
    contDiff_homMat_symm.comp contDiff_homModel_snd'
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  show ContDiffOn ℝ ∞ (fun p : HomModel => ∑ k, (Matrix.of (Msec q0 σ
      (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p.1)))⁻¹ i k * homMat.symm (p.2 : HomF) k j) _
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ ?_
  · exact (hI i k).comp contDiff_homModel_fst'.contDiffOn fun p hp => hp
  · exact (contDiff_pi.mp (contDiff_pi.mp hH k) j).contDiffOn

end CoordF

section Assemble

variable (q0 : HomTotM X) {U : Set ((Fin 4 → ℝ) × (Fin 10 → ℝ))}
  {σ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) → HomTotM X}

/-- `Fg` recovers the group element: `Fg (c (σ(e) · g)) = g`. -/
lemma Fg_ractM (hσp : ∀ e ∈ U, σ e ∈ OFr X ∧ (chartAt HomModel q0 (σ e)).1 = e ∧
      σ e ∈ (chartAt HomModel q0).source) {e} (he : e ∈ U) (g : O77) :
    Fg q0 σ (chartAt HomModel q0 (ractM (σ e) g)) = (g : Mat 14) := by
  obtain ⟨hO, hfst, hsrc⟩ := hσp e he
  have hdet := Msec_det_ne q0 (fun e he => ⟨(hσp e he).1, (hσp e he).2.2⟩) he
  rw [chart_ractM q0 _ hsrc]
  unfold Fg
  simp only
  rw [homMat_symm_comp]
  erw [hfst]
  apply Matrix.of.injective
  rw [Equiv.apply_symm_apply]
  show (Matrix.of (Msec q0 σ e))⁻¹ * (Matrix.of (Msec q0 σ e) * Matrix.of (g : Mat 14)) = _
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]

end Assemble

open Classical in
/-- **Phase 3, item 1: the local trivialisation is a diffeomorphism.** Near the base coordinate
of any orthonormal frame `q₀` there are a smooth section `σ` on `U` and the maps
`Ψ : U × O77 → OFr`, `Ψ(e, g) = σ(e) · g`, and `Ψinv : OFr → E14 × O77`,
`Ψinv q = ((c q).1, Mσ⁻¹ · Mq)`, both smooth (on `U × O77`, resp. on the chart domain
`W = {q | q ∈ c.source, (c q).1 ∈ U}`), mutually inverse there. -/
theorem localTriv_diffeo (q0 : HomTotM X) (hq0 : q0 ∈ OFr X) :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ∃ U ∈ nhds (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 q0).1),
      ∃ (Ψ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × O77 → OFr X) (Ψinv : OFr X → ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × O77)
        (W : Set (OFr X)),
        ContMDiffOn (𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)).prod 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ))
          𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ Ψ (U ×ˢ Set.univ) ∧
        ContMDiffOn 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ)
          (𝓘(ℝ, (Fin 4 → ℝ) × (Fin 10 → ℝ)).prod 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ)) ∞ Ψinv W ∧
        (∀ eg ∈ U ×ˢ (Set.univ : Set O77), Ψ eg ∈ W ∧ Ψinv (Ψ eg) = eg) ∧
        (∀ q ∈ W, Ψinv q ∈ U ×ˢ (Set.univ : Set O77) ∧ Ψ (Ψinv q) = q) ∧
        IsOpen U ∧ IsOpen W ∧ (⟨q0, hq0⟩ : OFr X) ∈ W ∧
        (∀ eg ∈ U ×ˢ (Set.univ : Set O77),
          (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (chartAt HomModel q0 (Ψ eg : HomTotM X)).1) = eg.1) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨U0, hU0, σ, hσ0, hσp0⟩ := exists_local_section q0 hq0
  set U := interior U0
  have hU : U ∈ nhds _ := interior_mem_nhds.mpr hU0
  have hUo : IsOpen U := isOpen_interior
  have hσ := hσ0.mono interior_subset
  have hσp : ∀ e ∈ U, _ := fun e he => hσp0 e (interior_subset he)
  set c := chartAt HomModel q0
  have hσp' : ∀ e ∈ U, σ e ∈ OFr X ∧ σ e ∈ c.source := fun e he => ⟨(hσp e he).1, (hσp e he).2.2⟩
  -- forward map
  let Ψ : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × O77 → OFr X := fun eg =>
    if h : eg.1 ∈ U then ⟨ractM (σ eg.1) eg.2, ractM_mem_OFr (hσp _ h).1 _⟩ else ⟨q0, hq0⟩
  -- the chart domain
  let W : Set (OFr X) := {q | (q : HomTotM X) ∈ c.source ∧
    (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (c q).1) ∈ U}
  have hWg : ∀ q ∈ W, Fg q0 σ (c q) ∈ O77 := by
    rintro q ⟨hqs, hqU⟩
    obtain ⟨g0, hg0⟩ := localTriv_surj q0 hq0 U σ hσp q.2 hqs hqU
    have := Fg_ractM q0 hσp hqU g0
    rw [hg0] at this
    rw [this]; exact g0.2
  let gO : OFr X → O77 := fun q => if h : q ∈ W then ⟨Fg q0 σ (c q), hWg q h⟩ else 1
  let Ψinv : OFr X → ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × O77 := fun q =>
    ((show (Fin 4 → ℝ) × (Fin 10 → ℝ) from (c q).1), gO q)
  have hO : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Mat 14) ∞
      (Subtype.val : O77 → Mat 14) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
  have hval := contMDiff_regularLevel_val (Fframe_regular (X := X))
  have hcv : ContMDiffOn 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) 𝓘(ℝ, HomModel) ∞
      (fun q : OFr X => c q) W :=
    (contMDiffOn_chart (x := q0)).comp hval.contMDiffOn fun q hq => hq.1
  have hWo : IsOpen W := by
    have hfst : Continuous (fun p : HomModel => (show (Fin 4 → ℝ) × (Fin 10 → ℝ) from p.1)) :=
      contDiff_homModel_fst'.continuous
    exact continuous_subtype_val.isOpen_preimage _
      (c.isOpen_inter_preimage (hUo.preimage hfst))
  have hq0W : (⟨q0, hq0⟩ : OFr X) ∈ W :=
    ⟨mem_chart_source _ q0, mem_of_mem_nhds hU⟩
  refine ⟨U, hU, Ψ, Ψinv, W, ?_, ?_, ?_, ?_, hUo, hWo, hq0W, ?_⟩
  · -- Ψ smooth
    rw [contMDiffOn_regularLevel_iff]
    have hpair := (hσ.comp contMDiffOn_fst (fun (eg : ((Fin 4 → ℝ) × (Fin 10 → ℝ)) × O77)
        (h : eg ∈ U ×ˢ (Set.univ : Set O77)) => h.1)).prodMk (hO.comp contMDiff_snd).contMDiffOn
    refine (contMDiff_ractM_joint.comp_contMDiffOn hpair).congr fun eg heg => ?_
    show ((Ψ eg : OFr X) : HomTotM X) = ractM (σ eg.1) eg.2
    simp only [Ψ, dif_pos heg.1]
  · -- Ψinv smooth
    refine ContMDiffOn.prodMk ?_ ?_
    · exact contDiff_homModel_fst'.contMDiff.comp_contMDiffOn hcv
    · rw [contMDiffOn_levelSet_iff (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))]
      have hF := (contDiffOn_Fg q0 hσ hσp').contMDiffOn
      refine (hF.comp hcv fun q hq => hq.2).congr fun q hq => ?_
      show ((gO q : O77) : Mat 14) = Fg q0 σ (c q)
      simp only [gO, dif_pos hq]
  · rintro ⟨e, g⟩ ⟨he, -⟩
    have hsrc := (hσp e he).2.2
    have hmem : Ψ (e, g) ∈ W := by
      simp only [Ψ, dif_pos he]
      refine ⟨ractM_mem_source q0 _ hsrc g, ?_⟩
      show (c (ractM (σ e) g)).1 ∈ U
      rw [chart_fst_ractM q0 _ hsrc, (hσp e he).2.1]; exact he
    refine ⟨hmem, ?_⟩
    have hΨ : ((Ψ (e, g) : OFr X) : HomTotM X) = ractM (σ e) g := by simp only [Ψ, dif_pos he]
    refine Prod.ext ?_ ?_
    · show (c (Ψ (e, g) : HomTotM X)).1 = e
      rw [hΨ, chart_fst_ractM q0 _ hsrc, (hσp e he).2.1]
    · show gO (Ψ (e, g)) = g
      simp only [gO, dif_pos hmem]
      apply Subtype.ext
      show Fg q0 σ (c (Ψ (e, g) : HomTotM X)) = g
      rw [hΨ, Fg_ractM q0 hσp he]
  · rintro q ⟨hqs, hqU⟩
    have hqW : q ∈ W := ⟨hqs, hqU⟩
    refine ⟨⟨hqU, Set.mem_univ _⟩, ?_⟩
    obtain ⟨g0, hg0⟩ := localTriv_surj q0 hq0 U σ hσp q.2 hqs hqU
    have hg : gO q = g0 := by
      simp only [gO, dif_pos hqW]
      apply Subtype.ext
      show Fg q0 σ (c q) = g0
      have := Fg_ractM q0 hσp hqU g0
      rwa [hg0] at this
    apply Subtype.ext
    show ((Ψ (Ψinv q) : OFr X) : HomTotM X) = q
    simp only [Ψ, Ψinv, dif_pos hqU, hg]
    exact hg0

  · rintro ⟨e, g⟩ ⟨he, -⟩
    have hsrc := (hσp e he).2.2
    have hΨ : ((Ψ (e, g) : OFr X) : HomTotM X) = ractM (σ e) g := by simp only [Ψ, dif_pos he]
    show (c (Ψ (e, g) : HomTotM X)).1 = e
    rw [hΨ, chart_fst_ractM q0 _ hsrc, (hσp e he).2.1]

end GU.Library
