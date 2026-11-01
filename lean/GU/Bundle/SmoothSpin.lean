import GU.Bundle.TimeObstruction
import GU.Bundle.SpinLie

/-!
# Phase 4, item 6: the smooth spin structure

For spin-lift data `D` with smooth frames `σ i` (the lifts `h i j` are then automatically smooth,
`contMDiffOn_h`), the glued bundle `P̃ → W` is a smooth principal `Spin(7,7)`-bundle
(**`smoothSpinBundle`**). `P̃` carries the manifold structure pulled back along the local homeomorphism
`Φ : P̃ → OFr` (`isLocalHomeomorph_Φ`), so `Φ` is a local diffeomorphism into `OFr`
(`isLocalDiffeomorph_Φ`) whose image is the open `SO₀`-reduction over `W` determined by the `σ i`
(`range_Φ`, `isOpen_range_Φ`, `range_Φ_act_mem`, `range_Φ_transitive`). The pulled-back structure and
`smooth_proj`, `smooth_act` do not use smoothness of the `σ i`; that hypothesis is what makes the
given trivialisations smooth. Instances exist (`exists_smoothSpin_near`), so far one-chart with
trivial cocycle.
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The model of the frame bundle. -/
abbrev EF := Fin (fibreDim HomModel (symS 14)) → ℝ

/-- The model of `Y`. -/
abbrev IY := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))

noncomputable local instance : ChartedSpace EF (OFr X) := regCharted (Fframe_regular (X := X))
local instance : IsManifold 𝓘(ℝ, EF) ∞ (OFr X) := isManifold_regularLevel (Fframe_regular (X := X))

lemma contMDiff_projOFr : ContMDiff 𝓘(ℝ, EF) IY ∞ (projOFr (X := X)) :=
  (frameBundle (X := X)).smooth_proj

namespace SpinLiftData

variable (D : SpinLiftData X)

/-- **`Φ` is a local homeomorphism.** -/
theorem isLocalHomeomorph_Φ : IsLocalHomeomorph D.Φ := by
  have h1 := D.isCoveringMap_Φ.isLocalHomeomorph
  have h2 : IsLocalHomeomorph (Subtype.val : Set.range D.Φ → OFr X) :=
    D.isOpen_range_Φ.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact h2.comp h1

/-- `W` as an open subset of `Y13`. -/
def WO : Opens (Y13o X) := ⟨D.W, D.isOpen_W⟩

/-- The projection to `W`. -/
def projW (p : D.P) : D.WO := ⟨p.proj.1, p.proj.2⟩

/-- The pulled-back charts of `P̃`. -/
@[instance_reducible] def chartP : ChartedSpace EF D.P := pullCharted EF D.isLocalHomeomorph_Φ

/-- **`Φ` is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_Φ :
    letI := D.chartP
    IsLocalDiffeomorph 𝓘(ℝ, EF) 𝓘(ℝ, EF) ∞ D.Φ :=
  isLocalDiffeomorph_pull D.isLocalHomeomorph_Φ

/-- **`τ i` is smooth** when the frames are. -/
theorem contMDiffOn_τ (hσ : ∀ i, ContMDiffOn IY 𝓘(ℝ, EF) ∞ (D.σ i) (D.V i)) (i : D.ι) :
    ContMDiffOn 𝓘(ℝ, EF) 𝓘(ℝ, E77) ∞ (D.τ i) (projOFr ⁻¹' D.V i) := by
  intro q0 hq0
  obtain ⟨V', hV', hq0V', σ', τ', -, -, hτ', hrec⟩ := (frameBundle (X := X)).locTriv (projOFr q0)
  have hτc : ContMDiffOn 𝓘(ℝ, EF) 𝓘(ℝ, E77) ∞ τ' (projOFr ⁻¹' V') := hτ'
  set N := projOFr ⁻¹' (D.V i ∩ V')
  have hN : IsOpen N := ((D.isOpen_V i).inter hV').preimage continuous_projOFr
  have hform : ∀ q ∈ N, D.τ i q = (τ' (D.σ i (projOFr q)))⁻¹ * τ' q := by
    intro q hq
    apply D.τ_unique i hq.1
    set y := projOFr q
    have hy : projOFr (D.σ i y) = y := D.proj_σ i y hq.1
    have e1 : actOFr' (σ' y) (τ' (D.σ i y)) = D.σ i y := by
      have := hrec (D.σ i y) (by show projOFr (D.σ i y) ∈ V'; rw [hy]; exact hq.2)
      rw [show (frameBundle (X := X)).proj (D.σ i y) = y from hy] at this
      exact this
    calc actOFr' (D.σ i y) ((τ' (D.σ i y))⁻¹ * τ' q)
        = actOFr' (actOFr' (σ' y) (τ' (D.σ i y))) ((τ' (D.σ i y))⁻¹ * τ' q) := by rw [e1]
      _ = actOFr' (σ' y) (τ' q) := by rw [actOFr'_mul, mul_inv_cancel_left]
      _ = q := hrec q hq.2
  have hT : ContMDiffOn 𝓘(ℝ, EF) 𝓘(ℝ, E77) ∞ (fun q => τ' (D.σ i (projOFr q))) N :=
    hτc.comp ((hσ i).comp contMDiff_projOFr.contMDiffOn fun q hq => hq.1) fun q hq => by
      show projOFr (D.σ i (projOFr q)) ∈ V'
      rw [D.proj_σ i _ hq.1]; exact hq.2
  have hR : ContMDiffOn 𝓘(ℝ, EF) 𝓘(ℝ, E77) ∞ (fun q => (τ' (D.σ i (projOFr q)))⁻¹ * τ' q) N :=
    hT.inv.mul (hτc.mono fun q hq => hq.2)
  exact ((hR.congr hform).contMDiffAt (hN.mem_nhds ⟨hq0, hq0V'⟩)).contMDiffWithinAt

/-- **The lifts are automatically smooth.** -/
theorem contMDiffOn_h (hσ : ∀ i, ContMDiffOn IY 𝓘(ℝ, EF) ∞ (D.σ i) (D.V i)) (i j : D.ι) :
    ContMDiffOn IY 𝓘(ℝ, E77) ∞ (D.h i j) (D.V i ∩ D.V j) := by
  rw [contMDiffOn_into_spin_iff ((D.isOpen_V i).inter (D.isOpen_V j))]
  refine ⟨D.cont_h i j, ?_⟩
  have h1 : ContMDiffOn IY 𝓘(ℝ, E77) ∞ (fun y => D.τ i (D.σ j y)) (D.V i ∩ D.V j) :=
    (D.contMDiffOn_τ hσ i).comp ((hσ j).mono Set.inter_subset_right) fun y hy => by
      show projOFr (D.σ j y) ∈ D.V i
      rw [D.proj_σ j y hy.2]; exact hy.1
  refine h1.congr fun y hy => (D.τ_unique i ?_ ?_).symm
  · rw [D.proj_σ j y hy.2]; exact hy.1
  · rw [D.proj_σ j y hy.2]; exact (D.lift i j y hy).symm

/-- **Phase 4, item 6: the smooth principal `Spin(7,7)`-bundle of smooth spin-lift data.** -/
def smoothSpinBundle (hσ : ∀ i, ContMDiffOn IY 𝓘(ℝ, EF) ∞ (D.σ i) (D.V i)) :
    letI := D.chartP
    haveI := isManifold_pull (E := EF) D.isLocalHomeomorph_Φ
    SmoothPrincipalBundle IY 𝓘(ℝ, E77) 𝓘(ℝ, EF) D.WO Spin77 D.P := by
  letI := D.chartP
  haveI := isManifold_pull (E := EF) D.isLocalHomeomorph_Φ
  have hΦ : ContMDiff 𝓘(ℝ, EF) 𝓘(ℝ, EF) ∞ D.Φ := contMDiff_pull D.isLocalHomeomorph_Φ
  have hPr : ContMDiff 𝓘(ℝ, EF) IY ∞ D.projW := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_projOFr.comp hΦ).congr fun p => (D.proj_Φ p).symm
  have hA : ContMDiff (𝓘(ℝ, EF).prod 𝓘(ℝ, E77)) 𝓘(ℝ, EF) ∞
      (fun pt : D.P × Spin77 => D.actS pt.1 pt.2) := by
    rw [contMDiff_into_pull_iff D.isLocalHomeomorph_Φ]
    refine ⟨D.continuous_actS₂, ?_⟩
    have h1 : ContMDiff (𝓘(ℝ, EF).prod 𝓘(ℝ, E77)) 𝓘(ℝ, EF) ∞ (fun pt : D.P × Spin77 => D.Φ pt.1) :=
      hΦ.comp contMDiff_fst
    have h2 : ContMDiff (𝓘(ℝ, EF).prod 𝓘(ℝ, E77)) 𝓘(ℝ, E77) ∞
        (fun pt : D.P × Spin77 => spinToO77 pt.2) := contMDiff_ρ.comp contMDiff_snd
    exact ((contMDiff_actOFr (X := X)).comp (h1.prodMk h2)).congr fun pt => D.Φ_actS pt.1 pt.2
  exact
  { proj := D.projW
    act := D.actS
    act_one := D.actS_one
    act_mul := D.actS_mul
    proj_act := fun _ _ => rfl
    free := D.actS_free
    transitive := fun p q h => D.actS_transitive p q (Subtype.ext (congrArg Subtype.val h))
    proj_surjective := fun b => ⟨⟨⟨b.1, b.2⟩, (1 : Spin77)⟩, rfl⟩
    smooth_proj := hPr
    smooth_act := hA
    locTriv := fun b => by
      obtain ⟨i, hi⟩ := D.cover b.1 b.2
      let S := D.toStructure
      let toW : D.WO → D.W := fun y => ⟨y.1, y.2⟩
      have htoW : Continuous toW := continuous_subtype_val.subtype_mk _
      let V : Set D.WO := Subtype.val ⁻¹' D.V i
      have hV : IsOpen V := (D.isOpen_V i).preimage continuous_subtype_val
      let σ : D.WO → D.P := fun y => S.sec i (toW y)
      let τ : D.P → Spin77 := fun p => (D.core.localTriv i p).2
      have hsecproj : ∀ y ∈ V, (σ y).proj = toW y := fun y hy => S.proj_sec i (y := toW y) hy
      have hsΦ : ∀ y ∈ V, D.Φ (σ y) = D.σ i y := fun y hy => by
        have hp := hsecproj y hy
        have h1 := D.Φ_chart i (p := σ y) (by rw [hp]; exact hy)
        rw [show (D.core.localTriv i (σ y)).2 = 1 from congrArg Prod.snd (S.e_sec i (y := toW y) hy),
          map_one, actOFr'_one, hp] at h1
        exact h1
      have hOp : IsOpen (D.projW ⁻¹' V) := hV.preimage hPr.continuous
      refine ⟨V, hV, hi, σ, τ, ?_, fun y hy => ?_, ?_, fun p hp => ?_⟩
      · rw [contMDiffOn_into_pull_iff D.isLocalHomeomorph_Φ hV]
        refine ⟨(S.continuousOn_sec i).comp htoW.continuousOn fun y hy => hy, ?_⟩
        have hs : ContMDiffOn IY 𝓘(ℝ, EF) ∞ (fun y : D.WO => D.σ i y) V :=
          (hσ i).comp contMDiff_subtype_val.contMDiffOn fun y hy => hy
        exact hs.congr hsΦ
      · apply Subtype.ext
        exact congrArg Subtype.val (hsecproj y hy)
      · have hρ : ∀ p ∈ D.projW ⁻¹' V, spinToO77 (τ p) = D.τ i (D.Φ p) := fun p hp => by
          have hp' : ((p.proj : D.W) : Y13o X) ∈ D.V i := hp
          refine (D.τ_unique i (by rw [D.proj_Φ]; exact hp') ?_).symm
          rw [D.proj_Φ]; exact (D.Φ_chart i hp').symm
        rw [contMDiffOn_into_spin_iff hOp]
        refine ⟨?_, ?_⟩
        · have h0 : ContinuousOn (D.core.localTriv i) (D.core.localTriv i).source :=
            (D.core.localTriv i).toOpenPartialHomeomorph.continuousOn
          exact continuous_snd.comp_continuousOn (h0.mono fun p hp => hp)
        · have hT : ContMDiffOn 𝓘(ℝ, EF) 𝓘(ℝ, E77) ∞ (fun p : D.P => D.τ i (D.Φ p)) (D.projW ⁻¹' V) :=
            (D.contMDiffOn_τ hσ i).comp hΦ.contMDiffOn fun p hp => by
              show projOFr (D.Φ p) ∈ D.V i
              rw [D.proj_Φ]; exact hp
          exact hT.congr hρ
      · have hp' : ((p.proj : D.W) : Y13o X) ∈ D.V i := hp
        exact S.sec_act_coord i (p := p) hp' }

/-- The image of `Φ` is `SO₀`-stable. -/
theorem range_Φ_act_mem {q : OFr X} (hq : q ∈ Set.range D.Φ) {g : O77} (hg : g ∈ SO0) :
    actOFr' q g ∈ Set.range D.Φ := by
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
  refine ⟨D.actS p t, ?_⟩
  rw [D.Φ_actS, show spinToO77 t = g from congrArg Subtype.val ht]

/-- `SO₀` acts transitively on the fibres of the image of `Φ`. -/
theorem range_Φ_transitive {q q' : OFr X} (hq : q ∈ Set.range D.Φ) (hq' : q' ∈ Set.range D.Φ)
    (h : projOFr q = projOFr q') : ∃ g ∈ SO0, actOFr' q g = q' := by
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨p', rfl⟩ := hq'
  rw [D.proj_Φ, D.proj_Φ] at h
  obtain ⟨t, ht⟩ := D.actS_transitive p p' (Subtype.ext h)
  exact ⟨spinToO77 t, spinToO77_mem t, by rw [← D.Φ_actS, ht]⟩

/-- A smooth frame over an open `W` gives smooth spin-lift data. -/
lemma ofSection_smooth {W : Set (Y13o X)} {hW : IsOpen W} {σ : Y13o X → OFr X}
    {hc : ContinuousOn σ W} {hp : ∀ y ∈ W, projOFr (σ y) = y}
    (hσ : ContMDiffOn IY 𝓘(ℝ, EF) ∞ σ W) :
    ∀ i, ContMDiffOn IY 𝓘(ℝ, EF) ∞ ((ofSection W hW σ hc hp).σ i) ((ofSection W hW σ hc hp).V i) :=
  fun _ => hσ

end SpinLiftData

/-- **Smooth spin structures exist near every point of `Y13`** (one chart, trivial cocycle). -/
theorem exists_smoothSpin_near (b : Y13o X) :
    ∃ D : SpinLiftData X, b ∈ D.W ∧ ∀ i, ContMDiffOn IY 𝓘(ℝ, EF) ∞ (D.σ i) (D.V i) := by
  obtain ⟨V, hV, hb, σ, -, hσ, hp, -, -⟩ := frame_locTriv (X := X) b
  exact ⟨SpinLiftData.ofSection V hV σ hσ.continuousOn hp, hb,
    SpinLiftData.ofSection_smooth hσ⟩

end

end GU.Library
