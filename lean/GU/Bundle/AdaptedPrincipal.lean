import GU.Bundle.AdaptedManifold

/-!
# Phase 3, item 3: the adapted frames are a smooth principal `O(6,4) × O(1,3)` sub-bundle

**`adaptedBundle`**: `AFrM → Y13` (the adapted orthonormal frames, a smooth submanifold of
`HomTotM` by `fA_regular`) is a `SmoothPrincipalBundle` with group the Lie group
`Gp = O(6,4) × O(1,3)`, acting through the block homomorphism `ιB : Gp →* O77` (injective, smooth,
range `Gblk`). Local triviality comes from `adaptedReduction.locTriv` (adapted local sections and
`Gblk`-valued division maps), pulled back along the smooth block inverse `ιinv`.
**`adaptedSubBundle`**: the inclusion `inclA : AFrM → OFr` is smooth, injective, covers the
identity of `Y13`, and is `ιB`-equivariant, i.e. `AFrM` is a smooth principal sub-bundle of the
frame bundle `OFr`, the structure group `O(6,4) × O(1,3)` mapping into `O(7,7)` by the injective
smooth homomorphism `ιB` onto the closed subgroup `Gblk`; both `ιB` and `inclA` are immersions
(`injective_mfderiv_ιB`, `injective_mfderiv_inclA`, `Immersions.lean`). The aligned Pati–Salam
groups `PS6', PS4' ≤ Gblk = range ιB` act on it through the
homomorphism `ιinv` on `Gblk` (`PS6'_le_range_ιB`, `adaptedBundle_PS6'`, `ιinv_mul`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The model of `AFrM`. -/
abbrev IA := 𝓘(ℝ, Fin (fibreDim HomModel FA) → ℝ)

/-- An adapted frame as a point of `AFrM`. -/
def mkA (q : HomTotM X) (hq : q ∈ AFr X) : AFrM X :=
  ⟨⟨q, (level_of_mem_AFr hq).1⟩, (mem_levelA_iff _).mpr hq⟩

@[simp] lemma frameA_mkA (q : HomTotM X) (hq : q ∈ AFr X) : frameA (mkA q hq) = q := rfl

lemma frameA_injective : Function.Injective (frameA (X := X)) := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

lemma mkA_frameA (p : AFrM X) : mkA (frameA p) (frameA_mem p) = p := frameA_injective rfl

/-- The projection `AFrM → Y13`. -/
def projA (p : AFrM X) : Y13o X := ⟨(frameA p).proj, proj_mem_Y13o (frameA_mem p).1⟩

/-- The right `Gp`-action through `ιB`. -/
def actA (p : AFrM X) (g : Gp) : AFrM X :=
  mkA (ractM (frameA p) (ιB g)) (ractM_mem_AFr_blk (frameA_mem p) (ιB_mem_Gblk g))

/-- The inclusion into the frame bundle. -/
def inclA (p : AFrM X) : OFr X := ⟨frameA p, (frameA_mem p).1⟩

lemma contMDiff_projA : ContMDiff IA ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
    (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞ (projA (X := X)) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact contMDiff_homTot_proj.comp contMDiff_frameA

lemma contMDiff_actA : ContMDiff (IA.prod IGp) IA ∞ (fun pg : AFrM X × Gp => actA pg.1 pg.2) := by
  rw [contMDiff_regularLevel_iff fA_regular, ← ContMDiff.subtypeVal_comp_iff]
  have hO : ContMDiff 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) 𝓘(ℝ, Mat 14) ∞
      (Subtype.val : O77 → Mat 14) :=
    contMDiff_levelSet_val (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
  have h1 : ContMDiff (IA.prod IGp) 𝓘(ℝ, HomModel) ∞ (fun pg : AFrM X × Gp => frameA pg.1) :=
    contMDiff_frameA.comp contMDiff_fst
  have h2 : ContMDiff (IA.prod IGp) 𝓘(ℝ, Mat 14) ∞ (fun pg : AFrM X × Gp => ((ιB pg.2 : O77) : Mat 14)) :=
    hO.comp (contMDiff_ιB.comp contMDiff_snd)
  exact contMDiff_ractM_joint.comp (h1.prodMk h2)

lemma contMDiff_inclA :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ContMDiff IA 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ (inclA (X := X)) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  rw [contMDiff_regularLevel_iff (Fframe_regular (X := X))]
  exact contMDiff_frameA

/-- **Local triviality of the adapted bundle.** -/
theorem adapted_locTriv (b : Y13o X) :
    ∃ V : Set (Y13o X), IsOpen V ∧ b ∈ V ∧ ∃ (σ : Y13o X → AFrM X) (τ : AFrM X → Gp),
      ContMDiffOn ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
        IA ∞ σ V ∧ (∀ y ∈ V, projA (σ y) = y) ∧
      ContMDiffOn IA IGp ∞ τ (projA ⁻¹' V) ∧ (∀ p ∈ projA ⁻¹' V, actA (σ (projA p)) (τ p) = p) := by
  classical
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨V, hV, hbV, σ, τ, hσ, hσp, hτ, hrec, hτH⟩ := (adaptedReduction (X := X)).locTriv b
  obtain ⟨q0, -, hq0⟩ := exists_adapted_frame (b : Yobs X) b.2
  let σA : Y13o X → AFrM X := fun y =>
    if h : ((σ y : OFr X) : HomTotM X) ∈ AFr X then mkA _ h else mkA q0 hq0
  have hσA : ∀ y ∈ V, frameA (σA y) = ((σ y : OFr X) : HomTotM X) := fun y hy => by
    show frameA (if h : ((σ y : OFr X) : HomTotM X) ∈ AFr X then mkA _ h else mkA q0 hq0) = _
    have hm : ((σ y : OFr X) : HomTotM X) ∈ AFr X := (hσp y hy).2
    rw [dif_pos hm]; rfl
  let τA : AFrM X → Gp := fun p => ιinv (τ (inclA p))
  refine ⟨V, hV, hbV, σA, τA, ?_, fun y hy => ?_, ?_, fun p hp => ?_⟩
  · rw [contMDiffOn_regularLevel_iff fA_regular]
    refine fun y hy => (ContMDiffWithinAt.subtypeVal_comp_iff _ _ _ _).mp ?_
    have hv := contMDiff_regularLevel_val (Fframe_regular (X := X))
    exact ((hv.comp_contMDiffOn hσ).congr fun y hy => hσA y hy) y hy
  · apply Subtype.ext
    show (frameA (σA y)).proj = y
    rw [hσA y hy]
    exact congrArg Subtype.val ((hσp y hy).1)
  · have hF : ContMDiffOn IA 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞
        (fun p => τ (inclA p)) (projA ⁻¹' V) :=
      hτ.comp contMDiff_inclA.contMDiffOn fun p hp => hp
    exact contMDiffOn_ιinv_comp hF fun p hp => hτH _ hp (frameA_mem p)
  · apply frameA_injective
    have hy : projA p ∈ V := hp
    have e1 := hrec (inclA p) hp
    have e2 : ιB (τA p) = τ (inclA p) := ιB_ιinv (hτH _ hp (frameA_mem p))
    show ractM (frameA (σA (projA p))) (ιB (τA p)) = frameA p
    rw [hσA _ hy, e2]
    exact congrArg Subtype.val e1

/-- **Phase 3, item 3: the adapted frames form a smooth principal `O(6,4) × O(1,3)`-bundle over
`Y13`.** -/
def adaptedBundle :
    SmoothPrincipalBundle ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
      IGp IA (Y13o X) Gp (AFrM X) where
  proj := projA
  act := actA
  act_one p := frameA_injective (by
    show ractM (frameA p) (ιB 1) = frameA p
    rw [map_one]; exact ractM_one _)
  act_mul p g h := frameA_injective (by
    show ractM (ractM (frameA p) (ιB g)) (ιB h) = ractM (frameA p) (ιB (g * h))
    rw [map_mul]; exact ractM_mul _ _ _)
  proj_act _ _ := rfl
  free p g h := by
    have hp : frameA p ∈ orthoSetM := by rw [← levelSet_Fframe]; exact (frameA_mem p).1
    have := ractM_free hp (ιB g) (congrArg frameA h)
    exact ιB_injective (this.trans (map_one ιB).symm)
  transitive p q h := by
    obtain ⟨g, hg, he⟩ := adapted_fibre_transitive (frameA_mem p) (frameA_mem q)
      (congrArg Subtype.val h)
    refine ⟨ιinv g, frameA_injective ?_⟩
    show ractM (frameA p) (ιB (ιinv g)) = frameA q
    rw [ιB_ιinv hg]; exact he
  proj_surjective b := by
    obtain ⟨q, hqp, hq⟩ := exists_adapted_frame (b : Yobs X) b.2
    exact ⟨mkA q hq, Subtype.ext hqp⟩
  smooth_proj := contMDiff_projA
  smooth_act := contMDiff_actA
  locTriv := adapted_locTriv

/-- **`AFrM` is a smooth principal sub-bundle of the frame bundle `OFr`**: the inclusion is
smooth, injective, covers the identity of `Y13`, and intertwines the actions through the
injective smooth Lie group homomorphism `ιB : O(6,4) × O(1,3) →* O(7,7)` with range `Gblk`. -/
theorem adaptedSubBundle :
    letI := regCharted (Fframe_regular (X := X))
    haveI := isManifold_regularLevel (Fframe_regular (X := X))
    ContMDiff IA 𝓘(ℝ, Fin (fibreDim HomModel (symS 14)) → ℝ) ∞ (inclA (X := X)) ∧
    Function.Injective (inclA (X := X)) ∧
    (∀ p, (frameBundle (X := X)).proj (inclA p) = (adaptedBundle (X := X)).proj p) ∧
    (∀ p g, inclA ((adaptedBundle (X := X)).act p g) = (frameBundle (X := X)).act (inclA p) (ιB g)) ∧
    Function.Injective ιB ∧ ContMDiff IGp 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ ιB ∧
    ιB.range = Gblk := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  exact ⟨contMDiff_inclA, fun p q h => frameA_injective (congrArg (fun r : OFr X => (r : HomTotM X)) h),
    fun _ => rfl, fun _ _ => rfl, ιB_injective, contMDiff_ιB, range_ιB⟩

/-- The aligned Pati–Salam groups lie in the image of the block group. -/
theorem PS6'_le_range_ιB : PS6' ≤ ιB.range := range_ιB ▸ PS6'_le_Gblk
theorem PS4'_le_range_ιB : PS4' ≤ ιB.range := range_ιB ▸ PS4'_le_Gblk

/-- **The aligned Pati–Salam groups act on the adapted bundle**: for `g ∈ PS6'` (resp. `PS4'`),
`ιinv g ∈ Gp` acts on `AFrM` and this action is the `O77`-action of `g` on frames. -/
theorem adaptedBundle_PS6' (p : AFrM X) {g : O77} (hg : g ∈ PS6') :
    frameA ((adaptedBundle (X := X)).act p (ιinv g)) = ractM (frameA p) g := by
  show ractM (frameA p) (ιB (ιinv g)) = _
  rw [ιB_ιinv (PS6'_le_Gblk hg)]

theorem adaptedBundle_PS4' (p : AFrM X) {g : O77} (hg : g ∈ PS4') :
    frameA ((adaptedBundle (X := X)).act p (ιinv g)) = ractM (frameA p) g := by
  show ractM (frameA p) (ιB (ιinv g)) = _
  rw [ιB_ιinv (PS4'_le_Gblk hg)]

end

end GU.Library
