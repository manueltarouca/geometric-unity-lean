import GU.Bundle.SpinConverse
import GU.Bundle.TimeObstruction
import GU.Bundle.SpinExamples

/-!
# Phase 6, item 3: spin structures over a general frame system

`FrameSys`: a base `B`, a space of frames `Fr` with a continuous projection onto `B` (surjective) and a
continuous right `O(7,7)`-action that is free, fibre-transitive, and has continuous local
trivialisations. Examples: `OFr X → Y13o X` (`ofrFS`) and the pulled-back frames `OFrT X → Ytilde X`
(`coverFS`, in `CoverSpinAPI.lean`).

This file restates `SpinStructure.lean` and `SpinConverse.lean` over a `FrameSys`, by the same proofs
(namespace `Gen`): cocycle lifts `Gen.SpinLiftData`, spin structures `Gen.SpinStructure`, the two-to-one
map `Gen.SpinLiftData.Φ_eq_iff`, `Gen.SpinStructure.Φ_eq_iff`, the covering map `isCoveringMap_Φ`, and the
equivalence `exists_data_iff_exists_structure`.
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- **A frame system**: frames over a base with a free, fibre-transitive, continuous right `O(7,7)`-action
admitting continuous local trivialisations. -/
structure FrameSys where
  B : Type
  [topB : TopologicalSpace B]
  Fr : Type
  [topF : TopologicalSpace Fr]
  proj : Fr → B
  act : Fr → O77 → Fr
  act_mul : ∀ q g g', act (act q g) g' = act q (g * g')
  act_one : ∀ q, act q 1 = q
  proj_act : ∀ q g, proj (act q g) = proj q
  cancel : ∀ {q : Fr} {g g' : O77}, act q g = act q g' → g = g'
  continuous_act : Continuous fun qg : Fr × O77 => act qg.1 qg.2
  continuous_proj : Continuous proj
  proj_surj : Function.Surjective proj
  exists_act : ∀ p r, proj p = proj r → ∃ h, act p h = r
  locTriv : ∀ b, ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ ∃ (σ : B → Fr) (τ : Fr → O77),
    ContinuousOn τ (proj ⁻¹' V) ∧ ∀ p ∈ proj ⁻¹' V, act (σ (proj p)) (τ p) = p

attribute [instance] FrameSys.topB FrameSys.topF

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **The orthonormal frames over `Y13` form a frame system.** -/
def ofrFS (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : FrameSys where
  B := Y13o X
  Fr := OFr X
  proj := projOFr
  act := actOFr'
  act_mul := actOFr'_mul
  act_one := actOFr'_one
  proj_act := projOFr_act
  cancel := actOFr'_cancel
  continuous_act := continuous_actOFr'
  continuous_proj := continuous_projOFr
  proj_surj y := by
    obtain ⟨q, hq⟩ := (orthoM_iff_13 (y : Yobs X)).mpr y.2
    exact ⟨⟨q, by rw [OFr, levelSet_Fframe]; exact hq.2⟩, Subtype.ext hq.1⟩
  exists_act := exists_act_eq
  locTriv b := by
    let _ := regCharted (Fframe_regular (X := X))
    have _ := isManifold_regularLevel (Fframe_regular (X := X))
    obtain ⟨V', hV', hb, σ', τ', -, -, hτ', hrec⟩ := (frameBundle (X := X)).locTriv b
    exact ⟨V', hV', hb, σ', τ', hτ'.continuousOn, hrec⟩

end

namespace Gen

noncomputable section

variable {Fs : FrameSys}

/-! ### The data -/

/-- **Spin-lift data over an open `W ⊆ Fs.B`**: local sections of `Fs.Fr` over an open cover of `W` with
continuous `Spin(7,7)` lifts of their transition functions satisfying the cocycle identity
(`w₂ = 0`). (For `ofrFS`, `W` cannot contain a full loop of metrics in a fibre, `no_spinLiftData`; for
`coverFS`, `W` can be everything, `exists_data_cover_R4`.) -/
structure SpinLiftData (Fs : FrameSys) where
  W : Set (Fs.B)
  isOpen_W : IsOpen W
  ι : Type
  V : ι → Set (Fs.B)
  isOpen_V : ∀ i, IsOpen (V i)
  V_sub : ∀ i, V i ⊆ W
  cover : ∀ y ∈ W, ∃ i, y ∈ V i
  σ : ι → Fs.B → Fs.Fr
  cont_σ : ∀ i, ContinuousOn (σ i) (V i)
  proj_σ : ∀ i, ∀ y ∈ V i, Fs.proj (σ i y) = y
  h : ι → ι → Fs.B → Spin77
  cont_h : ∀ i j, ContinuousOn (h i j) (V i ∩ V j)
  lift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = Fs.act (σ i y) (spinToO77 (h i j y))
  cocycle : ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, h i j y * h j k y = h i k y

/-- **The `w₂` defect**: for any continuous lifts of the transition functions (no cocycle
hypothesis), `h i j · h j k · (h i k)⁻¹ ∈ {1, −1}` on triple overlaps. -/
theorem spinLift_defect_mem {ι : Type} {V : ι → Set (Fs.B)} {σ : ι → Fs.B → Fs.Fr}
    {h : ι → ι → Fs.B → Spin77}
    (lift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = Fs.act (σ i y) (spinToO77 (h i j y)))
    {i j k : ι} {y : Fs.B} (hy : y ∈ V i ∩ V j ∩ V k) :
    h i j y * h j k y * (h i k y)⁻¹ = 1 ∨ h i j y * h j k y * (h i k y)⁻¹ = negOne := by
  rw [← spinToO77_eq_one_iff]
  have e1 := lift j k y ⟨hy.1.2, hy.2⟩
  have e2 := lift i j y hy.1
  have e3 := lift i k y ⟨hy.1.1, hy.2⟩
  rw [e2, Fs.act_mul, e3] at e1
  have := Fs.cancel e1
  rw [map_mul, map_mul, map_inv, ← this, mul_inv_cancel]

namespace SpinLiftData

variable {Fs : FrameSys} (D : SpinLiftData Fs)

lemma h_self (i : D.ι) {y : Fs.B} (hy : y ∈ D.V i) : D.h i i y = 1 := by
  have := D.cocycle i i i y ⟨⟨hy, hy⟩, hy⟩
  exact mul_eq_left.mp this

/-- The glued `Spin(7,7)` bundle. -/
def core : FiberBundleCore D.ι D.W Spin77 where
  baseSet i := Subtype.val ⁻¹' D.V i
  isOpen_baseSet i := (D.isOpen_V i).preimage continuous_subtype_val
  indexAt y := (D.cover y y.2).choose
  mem_baseSet_at y := (D.cover y y.2).choose_spec
  coordChange i j y s := (D.h i j y)⁻¹ * s
  coordChange_self i y hy s := by simp [D.h_self i hy]
  continuousOn_coordChange i j :=
    (((D.cont_h i j).comp (continuous_subtype_val.comp_continuousOn continuousOn_fst)
      fun p hp => hp.1).inv).mul continuousOn_snd
  coordChange_comp i j k y hy s := by
    rw [← mul_assoc, ← mul_inv_rev, D.cocycle i j k y hy]

/-- **The spin bundle** `P̃`. -/
abbrev P := D.core.TotalSpace

/-- The fibre coordinate. -/
def sp (p : D.P) : Spin77 := p.2

/-- The right `Spin(7,7)`-action. -/
def actS (p : D.P) (t : Spin77) : D.P := ⟨p.proj, (show Spin77 from p.2) * t⟩

/-- **The double-cover map** `Φ : P̃ → Fs.Fr`. -/
def Φ (p : D.P) : Fs.Fr := Fs.act (D.σ (D.core.indexAt p.proj) p.proj) (spinToO77 (D.sp p))

lemma localTriv_apply' (i : D.ι) (p : D.P) :
    D.core.localTriv i p = (p.proj, (D.h (D.core.indexAt p.proj) i p.proj)⁻¹ * D.sp p) := rfl

lemma mem_baseSet_at' (y : D.W) : (y : Fs.B) ∈ D.V (D.core.indexAt y) :=
  D.core.mem_baseSet_at y

/-- **Chart formula**: in the trivialisation `i`, `Φ (y, s) = σ i y · ρ(s)`. -/
lemma Φ_chart (i : D.ι) {p : D.P} (hp : (p.proj : Fs.B) ∈ D.V i) :
    D.Φ p = Fs.act (D.σ i p.proj) (spinToO77 (D.core.localTriv i p).2) := by
  set a := D.core.indexAt p.proj
  have ha : (p.proj : Fs.B) ∈ D.V a := D.mem_baseSet_at' p.proj
  rw [localTriv_apply', D.lift a i p.proj ⟨ha, hp⟩, Fs.act_mul, ← map_mul, mul_inv_cancel_left]
  rfl

lemma proj_Φ (p : D.P) : Fs.proj (D.Φ p) = p.proj := by
  rw [Φ, Fs.proj_act]; exact D.proj_σ _ _ (D.mem_baseSet_at' p.proj)

lemma Φ_actS (p : D.P) (t : Spin77) : D.Φ (D.actS p t) = Fs.act (D.Φ p) (spinToO77 t) := by
  show Fs.act _ (spinToO77 (D.sp p * t)) = _
  rw [map_mul, ← Fs.act_mul]; rfl

lemma ext' {p q : D.P} (h1 : p.proj = q.proj) (h2 : D.sp p = D.sp q) : p = q := by
  obtain ⟨y, s⟩ := p; obtain ⟨y', s'⟩ := q
  simp only at h1; subst h1
  exact congrArg _ h2

lemma sp_actS (p : D.P) (t : Spin77) : D.sp (D.actS p t) = D.sp p * t := rfl

lemma actS_one (p : D.P) : D.actS p 1 = p :=
  D.ext' rfl (by rw [sp_actS, mul_one])

lemma actS_mul (p : D.P) (s t : Spin77) : D.actS (D.actS p s) t = D.actS p (s * t) :=
  D.ext' rfl (by rw [sp_actS, sp_actS, sp_actS, mul_assoc])

lemma proj_actS (p : D.P) (t : Spin77) : (D.actS p t).proj = p.proj := rfl

lemma actS_free (p : D.P) (t : Spin77) (h : D.actS p t = p) : t = 1 := by
  have : D.sp p * t = D.sp p := congrArg D.sp h
  exact mul_eq_left.mp this

lemma actS_transitive (p q : D.P) (h : p.proj = q.proj) : ∃ t, D.actS p t = q :=
  ⟨(D.sp p)⁻¹ * D.sp q, D.ext' h (by show D.sp p * ((D.sp p)⁻¹ * D.sp q) = _; group)⟩

/-- In each local trivialisation the action is right multiplication. -/
lemma localTriv_actS (i : D.ι) (p : D.P) (t : Spin77) :
    D.core.localTriv i (D.actS p t) = ((D.core.localTriv i p).1, (D.core.localTriv i p).2 * t) := by
  rw [localTriv_apply', localTriv_apply']
  exact Prod.ext rfl (mul_assoc _ _ _).symm

/-- **Fibres of `Φ` are `{p, p·(−1)}`.** -/
theorem Φ_eq_iff (p q : D.P) : D.Φ p = D.Φ q ↔ q = p ∨ q = D.actS p negOne := by
  constructor
  · intro hpq
    have hproj : p.proj = q.proj :=
      Subtype.ext (by rw [← D.proj_Φ p, ← D.proj_Φ q, hpq])
    have e : spinToO77 (D.sp p) = spinToO77 (D.sp q) := by
      unfold Φ at hpq; rw [hproj] at hpq; exact Fs.cancel hpq
    have e' : spinToO77 ((D.sp p)⁻¹ * D.sp q) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    rcases (spinToO77_eq_one_iff _).mp e' with h1 | h1
    · left; exact D.ext' hproj.symm (by rw [inv_mul_eq_one] at h1; exact h1.symm)
    · right
      exact D.ext' hproj.symm (by
        show D.sp q = D.sp p * negOne
        rw [← h1]; group)
  · rintro (rfl | rfl)
    · rfl
    · rw [D.Φ_actS, spinToO77_negOne, Fs.act_one]

/-- `Φ` is continuous. -/
theorem continuous_Φ : Continuous D.Φ := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  set i := D.core.indexAt p.proj
  set e := D.core.localTriv i
  have hp : p ∈ e.source := D.core.mem_baseSet_at p.proj
  have hF : ContinuousOn (fun z : D.W × Spin77 => Fs.act (D.σ i z.1) (spinToO77 z.2))
      ((Subtype.val ⁻¹' D.V i) ×ˢ Set.univ) :=
    Fs.continuous_act.comp_continuousOn
      (((D.cont_σ i).comp (continuous_subtype_val.comp_continuousOn continuousOn_fst)
        fun z hz => hz.1).prodMk
        (continuous_spinToO77.comp continuous_snd).continuousOn)
  have hc : ContinuousOn D.Φ e.source := by
    refine (hF.comp e.continuousOn fun q hq => ?_).congr fun q hq => D.Φ_chart i hq
    exact ⟨(e.coe_fst hq).symm ▸ hq, Set.mem_univ _⟩
  exact hc.continuousAt (e.open_source.mem_nhds hp)

lemma continuous_actS (t : Spin77) : Continuous fun p => D.actS p t := by
  haveI : ∀ x, Nonempty (D.core.Fiber x) := fun _ => ⟨(1 : Spin77)⟩
  refine continuous_iff_continuousAt.mpr fun p => ?_
  set e := D.core.localTriv (D.core.indexAt p.proj)
  have hp : p ∈ e.source := D.core.mem_baseSet_at p.proj
  have hsrc : ∀ q ∈ e.source, D.actS q t ∈ e.source := fun q hq => hq
  have hc : ContinuousOn (fun q => D.actS q t) e.source := by
    have hg : ContinuousOn (fun q => ((e q).1, (e q).2 * t)) e.source :=
      (continuous_fst.comp_continuousOn e.continuousOn).prodMk
        ((continuous_snd.comp_continuousOn e.continuousOn).mul continuousOn_const)
    have h1 : ContinuousOn (fun q => e.toOpenPartialHomeomorph.symm ((e q).1, (e q).2 * t)) e.source :=
      e.toOpenPartialHomeomorph.continuousOn_symm.comp hg fun q hq => by
        show _ ∈ e.target
        rw [e.target_eq]; exact ⟨(e.coe_fst hq).symm ▸ hq, Set.mem_univ _⟩
    refine h1.congr fun q hq => ?_
    have := e.left_inv (hsrc q hq)
    have h2 : e.toOpenPartialHomeomorph (D.actS q t) = ((e q).1, (e q).2 * t) :=
      D.localTriv_actS _ q t
    rw [h2] at this
    exact this.symm
  exact hc.continuousAt (e.open_source.mem_nhds hp)

/-- The action is jointly continuous. -/
lemma continuous_actS₂ : Continuous fun pt : D.P × Spin77 => D.actS pt.1 pt.2 := by
  haveI : ∀ x, Nonempty (D.core.Fiber x) := fun _ => ⟨(1 : Spin77)⟩
  refine continuous_iff_continuousAt.mpr fun pt => ?_
  set e := D.core.localTriv (D.core.indexAt pt.1.proj)
  have hp : pt ∈ e.source ×ˢ (Set.univ : Set Spin77) := ⟨D.core.mem_baseSet_at pt.1.proj, trivial⟩
  have hg : ContinuousOn (fun qt : D.P × Spin77 => ((e qt.1).1, (e qt.1).2 * qt.2))
      (e.source ×ˢ Set.univ) :=
    ((continuous_fst.comp_continuousOn (e.continuousOn.comp continuousOn_fst fun _ h => h.1)).prodMk
      ((continuous_snd.comp_continuousOn (e.continuousOn.comp continuousOn_fst fun _ h => h.1)).mul
        continuous_snd.continuousOn))
  have h1 : ContinuousOn (fun qt : D.P × Spin77 =>
      e.toOpenPartialHomeomorph.symm ((e qt.1).1, (e qt.1).2 * qt.2)) (e.source ×ˢ Set.univ) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp hg fun qt hq => by
      show _ ∈ e.target
      rw [e.target_eq]; exact ⟨(e.coe_fst hq.1).symm ▸ hq.1, Set.mem_univ _⟩
  have hc : ContinuousOn (fun qt : D.P × Spin77 => D.actS qt.1 qt.2) (e.source ×ˢ Set.univ) := by
    refine h1.congr fun qt hq => ?_
    have := e.left_inv (show D.actS qt.1 qt.2 ∈ e.source from hq.1)
    have h2 : e.toOpenPartialHomeomorph (D.actS qt.1 qt.2) = ((e qt.1).1, (e qt.1).2 * qt.2) :=
      D.localTriv_actS _ qt.1 qt.2
    rw [h2] at this
    exact this.symm
  exact hc.continuousAt ((e.open_source.prod isOpen_univ).mem_nhds hp)

/-- The two sheets are distinct. -/
lemma actS_negOne_ne (p : D.P) : D.actS p negOne ≠ p := fun h => negOne_ne_one (D.actS_free p _ h)

/-! ### The division map of a local section -/

lemma exists_τ (i : D.ι) {q : Fs.Fr} (hq : Fs.proj q ∈ D.V i) :
    ∃ g, Fs.act (D.σ i (Fs.proj q)) g = q := by
  exact Fs.exists_act _ _ (D.proj_σ i _ hq)

open Classical in
/-- `τ i q`: the `O77`-coordinate of `q` relative to the section `σ i`. -/
def τ (i : D.ι) (q : Fs.Fr) : O77 :=
  if hq : Fs.proj q ∈ D.V i then (D.exists_τ i hq).choose else 1

lemma τ_spec (i : D.ι) {q : Fs.Fr} (hq : Fs.proj q ∈ D.V i) :
    Fs.act (D.σ i (Fs.proj q)) (D.τ i q) = q := by
  unfold τ; rw [dite_cond_eq_true (eq_true hq)]
  exact (D.exists_τ i hq).choose_spec

lemma τ_unique (i : D.ι) {q : Fs.Fr} {g : O77} (hq : Fs.proj q ∈ D.V i)
    (h : Fs.act (D.σ i (Fs.proj q)) g = q) : D.τ i q = g :=
  Fs.cancel ((D.τ_spec i hq).trans h.symm)

/-- **`τ i` is continuous** on the preimage of `V i`. -/
theorem continuousOn_τ (i : D.ι) : ContinuousOn (D.τ i) (Fs.proj ⁻¹' D.V i) := by
  intro q0 hq0
  obtain ⟨V', hV', hq0V', σ', τ', hτc, hrec⟩ := Fs.locTriv (Fs.proj q0)
  set N := Fs.proj ⁻¹' (D.V i ∩ V')
  have hN : IsOpen N := ((D.isOpen_V i).inter hV').preimage Fs.continuous_proj
  have hform : ∀ q ∈ N, D.τ i q = (τ' (D.σ i (Fs.proj q)))⁻¹ * τ' q := by
    intro q hq
    apply D.τ_unique i hq.1
    set y := Fs.proj q
    have hy : Fs.proj (D.σ i y) = y := D.proj_σ i y hq.1
    have e1 : Fs.act (σ' y) (τ' (D.σ i y)) = D.σ i y := by
      have := hrec (D.σ i y) (by show Fs.proj (D.σ i y) ∈ V'; rw [hy]; exact hq.2)
      rw [hy] at this
      exact this
    calc Fs.act (D.σ i y) ((τ' (D.σ i y))⁻¹ * τ' q)
        = Fs.act (Fs.act (σ' y) (τ' (D.σ i y))) ((τ' (D.σ i y))⁻¹ * τ' q) := by rw [e1]
      _ = Fs.act (σ' y) (τ' q) := by rw [Fs.act_mul, mul_inv_cancel_left]
      _ = q := hrec q hq.2
  have hT : ContinuousOn (fun q => τ' (D.σ i (Fs.proj q))) N :=
    hτc.comp ((D.cont_σ i).comp Fs.continuous_proj.continuousOn fun q hq => hq.1) fun q hq => by
      show Fs.proj (D.σ i (Fs.proj q)) ∈ V'
      rw [D.proj_σ i _ hq.1]; exact hq.2
  have hR : ContinuousOn (fun q => (τ' (D.σ i (Fs.proj q)))⁻¹ * τ' q) N :=
    hT.inv.mul (hτc.mono fun q hq => hq.2)
  exact ((hR.congr hform).continuousAt (hN.mem_nhds ⟨hq0, hq0V'⟩)).continuousWithinAt

/-! ### The image and the covering -/

/-- **The image of `Φ` is the `SO₀`-part of `Fs.Fr`.** -/
theorem range_Φ : Set.range D.Φ =
    {q | Fs.proj q ∈ D.W ∧
      ∀ i, Fs.proj q ∈ D.V i → ∃ g ∈ SO0, q = Fs.act (D.σ i (Fs.proj q)) g} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨by rw [D.proj_Φ]; exact p.proj.2, fun i hi => ?_⟩
    rw [D.proj_Φ] at hi ⊢
    exact ⟨_, spinToO77_mem _, D.Φ_chart i hi⟩
  · rintro ⟨hW, hq⟩
    let y : D.W := ⟨Fs.proj q, hW⟩
    set a := D.core.indexAt y
    obtain ⟨g, hg, hqg⟩ := hq a (D.mem_baseSet_at' y)
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
    refine ⟨⟨y, t⟩, ?_⟩
    show Fs.act (D.σ a (y : Fs.B)) (spinToO77 t) = q
    rw [show spinToO77 t = g from congrArg Subtype.val ht]
    exact hqg.symm

lemma τ_mem_SO0 (i : D.ι) {q : Fs.Fr} (hq : q ∈ Set.range D.Φ) (hi : Fs.proj q ∈ D.V i) :
    D.τ i q ∈ SO0 := by
  rw [D.range_Φ] at hq
  obtain ⟨g, hg, hqg⟩ := hq.2 i hi
  rw [D.τ_unique i hi hqg.symm]; exact hg

/-- `Φ` onto its image is an open map. -/
theorem isOpenMap_Φ : IsOpenMap (Set.rangeFactorization D.Φ) := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨p, hpW, rfl⟩
  set i := D.core.indexAt p.proj
  set tr := D.core.localTriv i
  have hpi : (p.proj : Fs.B) ∈ D.V i := D.mem_baseSet_at' p.proj
  have hps : p ∈ tr.source := hpi
  have himg : IsOpen (tr '' (W ∩ tr.source)) :=
    tr.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hW.inter tr.open_source)
      Set.inter_subset_right
  obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ :=
    isOpen_prod_iff.mp himg (tr p).1 (tr p).2 ⟨p, ⟨hpW, hps⟩, rfl⟩
  obtain ⟨O0, hO0, hO0B⟩ := isOpen_induced_iff.mp (isOpenMap_spinToSO0 B hB)
  have hA' : IsOpen (Subtype.val '' A : Set (Fs.B)) := D.isOpen_W.isOpenMap_subtype_val A hA
  set O : Set (Fs.Fr) := Fs.proj ⁻¹' ((Subtype.val '' A) ∩ D.V i) ∩ D.τ i ⁻¹' O0
  have hO : IsOpen O :=
    ((D.continuousOn_τ i).mono fun q hq => hq.2).isOpen_inter_preimage
      ((hA'.inter (D.isOpen_V i)).preimage Fs.continuous_proj) hO0
  have hfst : (tr p).1 = p.proj := rfl
  refine ⟨Subtype.val ⁻¹' O, ?_, hO.preimage continuous_subtype_val, ?_⟩
  · rintro ⟨q, hqr⟩ ⟨⟨⟨a0, ha0, hqa⟩, hqi⟩, hqO⟩
    have hSO := D.τ_mem_SO0 i hqr hqi
    have hmem : (⟨D.τ i q, hSO⟩ : SO0) ∈ spinToSO0 '' B := by rw [← hO0B]; exact hqO
    obtain ⟨t, htB, ht⟩ := hmem
    obtain ⟨p', ⟨hp'W, hp's⟩, hp'⟩ := hAB (show (a0, t) ∈ A ×ˢ B from ⟨ha0, htB⟩)
    refine ⟨p', hp'W, Subtype.ext ?_⟩
    show D.Φ p' = q
    have hy : (p'.proj : Fs.B) = Fs.proj q := by
      rw [← hqa]; exact congrArg (fun z => ((z.1 : D.W) : Fs.B)) hp'
    have hs : (tr p').2 = t := congrArg Prod.snd hp'
    rw [D.Φ_chart i hp's, hs, show spinToO77 t = D.τ i q from congrArg Subtype.val ht, hy,
      D.τ_spec i hqi]
  · show D.Φ p ∈ O
    refine ⟨⟨by rw [D.proj_Φ, ← hfst]; exact ⟨_, hpA, rfl⟩, by rw [D.proj_Φ]; exact hpi⟩, ?_⟩
    show D.τ i (D.Φ p) ∈ O0
    rw [D.τ_unique i (by rw [D.proj_Φ]; exact hpi) (by rw [D.proj_Φ]; exact (D.Φ_chart i hpi).symm)]
    have : spinToSO0 (tr p).2 ∈ Subtype.val ⁻¹' O0 := by rw [hO0B]; exact ⟨_, hpB, rfl⟩
    exact this

/-- The kernel `{±1}` acting on `P̃` (by `p ↦ p · g⁻¹`). -/
@[instance_reducible] def kerAct : MulAction spinToSO0.ker D.P where
  smul g p := D.actS p (g : Spin77)⁻¹
  one_smul p := by show D.actS p ((1 : Spin77))⁻¹ = p; rw [inv_one, D.actS_one]
  mul_smul g h p := by
    show D.actS p ((g : Spin77) * h)⁻¹ = D.actS (D.actS p (h : Spin77)⁻¹) (g : Spin77)⁻¹
    rw [D.actS_mul, mul_inv_rev]

lemma spinToO77_of_ker (g : spinToSO0.ker) : spinToO77 (g : Spin77) = 1 :=
  congrArg Subtype.val (MonoidHom.mem_ker.mp g.2)

/-- **`Φ` is a covering map onto its image** (a quotient covering by `{±1}`). -/
theorem isQuotientCoveringMap_Φ :
    letI := D.kerAct
    IsQuotientCoveringMap (Set.rangeFactorization D.Φ) spinToSO0.ker := by
  letI := D.kerAct
  have hc : Continuous (Set.rangeFactorization D.Φ) := D.continuous_Φ.subtype_mk _
  refine { toIsQuotientMap := D.isOpenMap_Φ.isQuotientMap hc Set.rangeFactorization_surjective,
           toContinuousConstSMul := ⟨fun g => D.continuous_actS _⟩,
           apply_eq_iff_mem_orbit := ?_, disjoint := ?_ }
  · intro e1 e2
    rw [Subtype.ext_iff, MulAction.mem_orbit_iff]
    show D.Φ e1 = D.Φ e2 ↔ ∃ g : spinToSO0.ker, D.actS e2 (g : Spin77)⁻¹ = e1
    constructor
    · intro h
      rcases (D.Φ_eq_iff e2 e1).mp h.symm with h1 | h1
      · exact ⟨1, by rw [h1]; show D.actS e2 ((1 : Spin77))⁻¹ = e2; rw [inv_one, D.actS_one]⟩
      · exact ⟨⟨negOne, negOne_mem_ker_spinToSO0⟩, by
          show D.actS e2 negOne⁻¹ = e1; rw [negOne_inv, h1]⟩
    · rintro ⟨g, rfl⟩
      rw [D.Φ_actS, map_inv, spinToO77_of_ker, inv_one, Fs.act_one]
  · intro e
    set tr := D.core.localTriv (D.core.indexAt e.proj)
    have hes : e ∈ tr.source := D.mem_baseSet_at' e.proj
    set s0 := (tr e).2
    have hne : s0 ≠ s0 * negOne := fun h => negOne_ne_one (mul_eq_left.mp h.symm)
    obtain ⟨A1, A2, hA1, hA2, hs0, hs1, hdisj⟩ := t2_separation hne
    set B' := A1 ∩ (fun s => s * negOne) ⁻¹' A2
    have hB' : IsOpen B' := hA1.inter (hA2.preimage (continuous_id.mul continuous_const))
    refine ⟨tr.source ∩ tr ⁻¹' (Set.univ ×ˢ B'), ?_, fun g hg => ?_⟩
    · exact (tr.continuousOn.isOpen_inter_preimage tr.open_source (isOpen_univ.prod hB')).mem_nhds
        ⟨hes, Set.mem_univ _, hs0, hs1⟩
    · obtain ⟨_, ⟨p, ⟨hps, -, hpB⟩, rfl⟩, ⟨-, -, hgpB⟩⟩ := hg
      rcases (spinToO77_eq_one_iff _).mp (spinToO77_of_ker g) with h1 | h1
      · exact Subtype.ext h1
      · exfalso
        have e2 : (tr (D.actS p (g : Spin77)⁻¹)).2 = (tr p).2 * negOne := by
          rw [D.localTriv_actS, h1, negOne_inv]
        have hA : (tr p).2 * negOne ∈ A1 := by
          have : (tr (D.actS p (g : Spin77)⁻¹)).2 ∈ A1 := hgpB.1
          rwa [e2] at this
        exact Set.disjoint_left.mp hdisj hA hpB.2

/-- **`Φ : P̃ → Fs.Fr` is a covering map onto its image.** -/
theorem isCoveringMap_Φ : IsCoveringMap (Set.rangeFactorization D.Φ) := by
  letI := D.kerAct
  exact D.isQuotientCoveringMap_Φ.isCoveringMap

/-- **A frame over an open `W` gives spin-lift data** (one chart, trivial lifts). Such frames exist
locally (for `ofrFS`: `exists_spinLiftData_near`, `SpinExamples.lean`). -/
def ofSection (W : Set (Fs.B)) (hW : IsOpen W) (σ : Fs.B → Fs.Fr) (hσ : ContinuousOn σ W)
    (hσp : ∀ y ∈ W, Fs.proj (σ y) = y) : SpinLiftData Fs :=
  ⟨W, hW, Unit, fun _ => W, fun _ => hW, fun _ => subset_rfl, fun _ hy => ⟨(), hy⟩, fun _ => σ,
    fun _ => hσ, fun _ y hy => hσp y hy, fun _ _ _ => 1, fun _ _ => continuousOn_const,
    fun _ _ y _ => by rw [map_one, Fs.act_one], fun _ _ _ _ _ => mul_one 1⟩

/-- **Spin lift** (the generic form of Phase 3, item 4): from spin-lift data (`w₂ = 0` in cocycle form), `P̃` is a
topological principal `Spin(7,7)`-bundle over `W` (local trivialisations over the `V i`, in which
the action is right multiplication; free, fibre-transitive action), and `Φ : P̃ → Fs.Fr` is a
continuous, base-preserving, `ρ`-equivariant double cover of the `SO₀`-reduction of `Fs.Fr`
determined by the `σ i`. -/
theorem spin_lift :
    Continuous D.core.proj ∧
    (∀ i, (D.core.localTriv i).baseSet = Subtype.val ⁻¹' D.V i ∧ ∀ p t,
      D.core.localTriv i (D.actS p t) = ((D.core.localTriv i p).1, (D.core.localTriv i p).2 * t)) ∧
    (∀ p, D.actS p 1 = p) ∧ (∀ p s t, D.actS (D.actS p s) t = D.actS p (s * t)) ∧
    (∀ p t, (D.actS p t).proj = p.proj) ∧ (∀ p t, D.actS p t = p → t = 1) ∧
    (∀ p q : D.P, p.proj = q.proj → ∃ t, D.actS p t = q) ∧
    Continuous (fun pt : D.P × Spin77 => D.actS pt.1 pt.2) ∧ (∀ p, D.actS p negOne ≠ p) ∧
    Continuous D.Φ ∧ (∀ p, Fs.proj (D.Φ p) = p.proj) ∧
    (∀ p t, D.Φ (D.actS p t) = Fs.act (D.Φ p) (spinToO77 t)) ∧
    (∀ p q, D.Φ p = D.Φ q ↔ q = p ∨ q = D.actS p negOne) ∧
    Set.range D.Φ = {q | Fs.proj q ∈ D.W ∧
      ∀ i, Fs.proj q ∈ D.V i → ∃ g ∈ SO0, q = Fs.act (D.σ i (Fs.proj q)) g} ∧
    IsCoveringMap (Set.rangeFactorization D.Φ) :=
  ⟨D.core.continuous_proj, fun i => ⟨rfl, D.localTriv_actS i⟩, D.actS_one, D.actS_mul,
    D.proj_actS, D.actS_free, D.actS_transitive, D.continuous_actS₂, D.actS_negOne_ne, D.continuous_Φ, D.proj_Φ, D.Φ_actS, D.Φ_eq_iff,
    D.range_Φ, D.isCoveringMap_Φ⟩

end SpinLiftData

/-- **Spin structure from a `ℤ/2`-lift of the transition cocycle.** Given continuous local
sections `σ i` of the frame bundle over an open cover of an open `W ⊆ Fs.B` and continuous `Spin(7,7)` lifts
`h i j` of their transition functions satisfying the cocycle identity (equivalently: the `w₂`
defect of `spinLift_defect_mem` is trivial), there is a topological principal `Spin(7,7)`-bundle
`P̃ → W` (jointly continuous, free, fibre-transitive right action; local trivialisations over the
`V i` in which the action is right multiplication) and a continuous, `ρ`-equivariant map
`Φ : P̃ → Fs.Fr` whose fibres are the two points `{p, p·(−1)}`, whose image is the `SO₀`-reduction
determined by the `σ i`, and which is
a covering map onto its image. -/
theorem spin_structure_of_lift (W : Set (Fs.B)) (hW : IsOpen W) {ι : Type}
    (V : ι → Set (Fs.B)) (hV : ∀ i, IsOpen (V i)) (hVW : ∀ i, V i ⊆ W)
    (hcov : ∀ y ∈ W, ∃ i, y ∈ V i) (σ : ι → Fs.B → Fs.Fr) (hσ : ∀ i, ContinuousOn (σ i) (V i))
    (hσp : ∀ i, ∀ y ∈ V i, Fs.proj (σ i y) = y) (h : ι → ι → Fs.B → Spin77)
    (hh : ∀ i j, ContinuousOn (h i j) (V i ∩ V j))
    (hlift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = Fs.act (σ i y) (spinToO77 (h i j y)))
    (hcoc : ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, h i j y * h j k y = h i k y) :
    ∃ (P : Type) (_ : TopologicalSpace P) (projS : P → W) (actS : P → Spin77 → P)
      (Φ : P → Fs.Fr),
      Continuous projS ∧ (∀ p, actS p 1 = p) ∧ (∀ p s t, actS (actS p s) t = actS p (s * t)) ∧
      (∀ p t, projS (actS p t) = projS p) ∧ (∀ p t, actS p t = p → t = 1) ∧
      (∀ p q, projS p = projS q → ∃ t, actS p t = q) ∧
      (∀ i, ∃ e : Trivialization Spin77 projS, e.baseSet = Subtype.val ⁻¹' V i ∧
        ∀ p ∈ e.source, ∀ t, e (actS p t) = ((e p).1, (e p).2 * t)) ∧
      Continuous (fun pt : P × Spin77 => actS pt.1 pt.2) ∧ (∀ p, actS p negOne ≠ p) ∧
      Continuous Φ ∧ (∀ p, Fs.proj (Φ p) = projS p) ∧
      (∀ p t, Φ (actS p t) = Fs.act (Φ p) (spinToO77 t)) ∧
      (∀ p q, Φ p = Φ q ↔ q = p ∨ q = actS p negOne) ∧
      Set.range Φ = {q | Fs.proj q ∈ W ∧
        ∀ i, Fs.proj q ∈ V i → ∃ g ∈ SO0, q = Fs.act (σ i (Fs.proj q)) g} ∧
      IsCoveringMap (Set.rangeFactorization Φ) := by
  let D : SpinLiftData Fs := ⟨W, hW, ι, V, hV, hVW, hcov, σ, hσ, hσp, h, hh, hlift, hcoc⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h7a, h7b, h8, h9, h10, h11, h12, h13⟩ := D.spin_lift
  exact ⟨D.P, inferInstance, D.core.proj, D.actS, D.Φ, h1, h3, h4, h5, h6, h7,
    fun i => ⟨D.core.localTriv i, (h2 i).1, fun p _ t => (h2 i).2 p t⟩, h7a, h7b, h8, h9, h10, h11,
    h12, h13⟩


end

noncomputable section

variable {Fs : FrameSys}


/-- **A spin structure on the frames over an open `W ⊆ Fs.B`** (for `ofrFS` and nonempty `X`, `W` cannot be
all of `Y13`, `no_spinStructure`; for `coverFS` it can, `coverSpin`): a principal `Spin(7,7)`-bundle `P → W`
(local trivialisations `e i` over an open cover in which the action is right multiplication) with a
continuous, base-preserving, `ρ`-equivariant map `Φ : P → Fs.Fr`. Not assumed, but derived: freeness
(`act_free`), the two-point fibres of `Φ` (`Φ_eq_iff`), that `Φ` covers an `SO₀`-reduction
(`range_Φ_eq`, `isCoveringMap_Φ`). `act_one`, `act_mul`, `continuous_act` are in fact
redundant given `e_act` and `proj_act`; they are kept for convenience. -/
structure SpinStructure (Fs : FrameSys) where
  W : Set (Fs.B)
  isOpen_W : IsOpen W
  P : Type
  top : TopologicalSpace P
  projS : P → W
  actS : P → Spin77 → P
  Φ : P → Fs.Fr
  act_one : ∀ p, actS p 1 = p
  act_mul : ∀ p s t, actS (actS p s) t = actS p (s * t)
  proj_act : ∀ p t, projS (actS p t) = projS p
  continuous_act : Continuous fun pt : P × Spin77 => actS pt.1 pt.2
  ι : Type
  V : ι → Set (Fs.B)
  V_sub : ∀ i, V i ⊆ W
  cover : ∀ y ∈ W, ∃ i, y ∈ V i
  e : ι → Trivialization Spin77 projS
  baseSet_e : ∀ i, (e i).baseSet = Subtype.val ⁻¹' V i
  e_act : ∀ i, ∀ p ∈ (e i).source, ∀ t, e i (actS p t) = ((e i p).1, (e i p).2 * t)
  continuous_Φ : Continuous Φ
  proj_Φ : ∀ p, Fs.proj (Φ p) = (projS p : Fs.B)
  Φ_act : ∀ p t, Φ (actS p t) = Fs.act (Φ p) (spinToO77 t)

attribute [instance] SpinStructure.top

/-- **Isomorphism of spin structures**: an equivariant homeomorphism over the base commuting with
the maps to the frame bundle. -/
structure SpinIso (S S' : SpinStructure Fs) where
  F : S.P ≃ₜ S'.P
  proj_F : ∀ p, (S'.projS (F p) : Fs.B) = S.projS p
  act_F : ∀ p t, F (S.actS p t) = S'.actS (F p) t
  Φ_F : ∀ p, S'.Φ (F p) = S.Φ p

namespace SpinStructure

variable (S : SpinStructure Fs)

/-- The section of the trivialisation `i`. -/
def sec (i : S.ι) (y : S.W) : S.P := (S.e i).toOpenPartialHomeomorph.symm (y, 1)

lemma mem_target (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) (t : Spin77) :
    (y, t) ∈ (S.e i).target := by
  rw [Trivialization.mem_target, S.baseSet_e]; exact hy

lemma mem_source_iff (i : S.ι) (p : S.P) : p ∈ (S.e i).source ↔ (S.projS p : Fs.B) ∈ S.V i := by
  rw [Trivialization.mem_source, S.baseSet_e]; rfl

lemma e_symm (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) (t : Spin77) :
    S.e i ((S.e i).toOpenPartialHomeomorph.symm (y, t)) = (y, t) :=
  (S.e i).right_inv (S.mem_target i hy t)

lemma e_sec (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) : S.e i (S.sec i y) = (y, 1) :=
  S.e_symm i hy 1

lemma proj_sec (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) : S.projS (S.sec i y) = y :=
  (S.e i).proj_symm_apply (S.mem_target i hy 1)

lemma sec_mem (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) : S.sec i y ∈ (S.e i).source :=
  (S.mem_source_iff i _).mpr (by rw [S.proj_sec i hy]; exact hy)

lemma continuousOn_sec (i : S.ι) : ContinuousOn (S.sec i) (Subtype.val ⁻¹' S.V i) :=
  (S.e i).toOpenPartialHomeomorph.continuousOn_symm.comp
    (continuousOn_id.prodMk continuousOn_const) fun _ hy => S.mem_target i hy 1

lemma fst_e (i : S.ι) {p : S.P} (hp : (S.projS p : Fs.B) ∈ S.V i) : (S.e i p).1 = S.projS p :=
  (S.e i).coe_fst ((S.mem_source_iff i p).mpr hp)

lemma act_mem (i : S.ι) {p : S.P} (hp : (S.projS p : Fs.B) ∈ S.V i) (t : Spin77) :
    S.actS p t ∈ (S.e i).source :=
  (S.mem_source_iff i _).mpr (by rw [S.proj_act]; exact hp)

/-- The coordinate of `sᵢ · t` is `t`. -/
lemma e_sec_act (i : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i) (t : Spin77) :
    S.e i (S.actS (S.sec i y) t) = (y, t) := by
  rw [S.e_act i _ (S.sec_mem i hy), S.e_sec i hy, one_mul]

/-- **Every point is `sᵢ · (its coordinate)`.** -/
lemma sec_act_coord (i : S.ι) {p : S.P} (hp : (S.projS p : Fs.B) ∈ S.V i) :
    S.actS (S.sec i (S.projS p)) (S.e i p).2 = p := by
  apply (S.e i).injOn (S.act_mem i (by rw [S.proj_sec i hp]; exact hp) _)
    ((S.mem_source_iff i p).mpr hp)
  show S.e i _ = S.e i p
  rw [S.e_sec_act i hp]
  exact Prod.ext (S.fst_e i hp).symm rfl

/-- The action is free. -/
lemma act_free (p : S.P) (t : Spin77) (h : S.actS p t = p) : t = 1 := by
  obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
  have hs := (S.mem_source_iff i p).mpr hi
  have := congrArg (fun q => (S.e i q).2) h
  simp only [S.e_act i p hs] at this
  exact mul_eq_left.mp this

/-- The transition lift `sⱼ = sᵢ · hᵢⱼ`. -/
def lift (i j : S.ι) (y : S.W) : Spin77 := (S.e i (S.sec j y)).2

lemma sec_eq (i j : S.ι) {y : S.W} (hy : (y : Fs.B) ∈ S.V i ∩ S.V j) :
    S.sec j y = S.actS (S.sec i y) (S.lift i j y) := by
  have h := S.sec_act_coord i (p := S.sec j y) (by rw [S.proj_sec j hy.2]; exact hy.1)
  rw [S.proj_sec j hy.2] at h
  exact h.symm

lemma isOpen_V (i : S.ι) : IsOpen (S.V i) := by
  have h : S.V i = Subtype.val '' (Subtype.val ⁻¹' S.V i : Set S.W) := by
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.mpr (S.V_sub i)]
  rw [h]
  refine S.isOpen_W.isOpenMap_subtype_val _ ?_
  rw [← S.baseSet_e]; exact (S.e i).open_baseSet

/-- A map on the base is continuous on `V i` if its restriction to `W` is. -/
lemma continuousOn_of_val {Z : Type*} [TopologicalSpace Z] (i : S.ι) {g : Fs.B → Z}
    (h : ContinuousOn (g ∘ Subtype.val : S.W → Z) (Subtype.val ⁻¹' S.V i)) :
    ContinuousOn g (S.V i) := by
  intro y hy
  have hW : y ∈ S.W := S.V_sub i hy
  have hO : IsOpen (Subtype.val ⁻¹' S.V i : Set S.W) := (S.isOpen_V i).preimage continuous_subtype_val
  have hat := h.continuousAt (x := ⟨y, hW⟩) (hO.mem_nhds hy)
  exact ((S.isOpen_W.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hat).continuousWithinAt

open Classical in
/-- The local frame `Φ ∘ sᵢ`, extended to the base. -/
def σd (i : S.ι) (y : Fs.B) : Fs.Fr :=
  if hy : y ∈ S.W then S.Φ (S.sec i ⟨y, hy⟩)
  else
    (Fs.proj_surj y).choose

open Classical in
/-- The lift, extended to the base. -/
def hd (i j : S.ι) (y : Fs.B) : Spin77 := if hy : y ∈ S.W then S.lift i j ⟨y, hy⟩ else 1

lemma σd_val (i : S.ι) (y : S.W) : S.σd i y = S.Φ (S.sec i y) := dif_pos y.2

lemma hd_val (i j : S.ι) (y : S.W) : S.hd i j y = S.lift i j y := dif_pos y.2

/-- **The cocycle of a spin structure.** -/
def toData : SpinLiftData Fs where
  W := S.W
  isOpen_W := S.isOpen_W
  ι := S.ι
  V := S.V
  isOpen_V := S.isOpen_V
  V_sub := S.V_sub
  cover := S.cover
  σ := S.σd
  cont_σ i := S.continuousOn_of_val i (by
    refine (S.continuous_Φ.comp_continuousOn (S.continuousOn_sec i)).congr fun y _ => S.σd_val i y)
  proj_σ i y hy := by
    have hW := S.V_sub i hy
    have e : S.σd i y = S.Φ (S.sec i ⟨y, hW⟩) := S.σd_val i ⟨y, hW⟩
    rw [e, S.proj_Φ, S.proj_sec i (y := ⟨y, hW⟩) hy]
  h := S.hd
  cont_h i j := by
    intro y hy
    have hW := S.V_sub i hy.1
    have hO : IsOpen (Subtype.val ⁻¹' (S.V i ∩ S.V j) : Set S.W) :=
      ((S.isOpen_V i).inter (S.isOpen_V j)).preimage continuous_subtype_val
    have h0 : ContinuousOn (S.e i) (S.e i).source := (S.e i).toOpenPartialHomeomorph.continuousOn
    have hc : ContinuousOn (fun y : S.W => S.e i (S.sec j y)) (Subtype.val ⁻¹' (S.V i ∩ S.V j)) :=
      ContinuousOn.comp h0 ((S.continuousOn_sec j).mono fun y hy => hy.2) fun y hy =>
        (S.mem_source_iff i _).mpr (by rw [S.proj_sec j hy.2]; exact hy.1)
    have hc2 : ContinuousOn (S.hd i j ∘ Subtype.val : S.W → Spin77)
        (Subtype.val ⁻¹' (S.V i ∩ S.V j)) :=
      (continuous_snd.comp_continuousOn hc).congr fun y _ => S.hd_val i j y
    have hat := hc2.continuousAt (x := ⟨y, hW⟩) (hO.mem_nhds hy)
    exact ((S.isOpen_W.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hat).continuousWithinAt
  lift i j y hy := by
    have hW := S.V_sub i hy.1
    let y' : S.W := ⟨y, hW⟩
    show S.σd j (y' : Fs.B) = Fs.act (S.σd i (y' : Fs.B)) (spinToO77 (S.hd i j (y' : Fs.B)))
    rw [S.σd_val, S.σd_val, S.hd_val, S.sec_eq i j (y := y') hy, S.Φ_act]
  cocycle i j k y hy := by
    have hW := S.V_sub i hy.1.1
    let y' : S.W := ⟨y, hW⟩
    show S.hd i j (y' : Fs.B) * S.hd j k (y' : Fs.B) = S.hd i k (y' : Fs.B)
    rw [S.hd_val, S.hd_val, S.hd_val]
    have h1 := S.sec_eq i k (y := y') ⟨hy.1.1, hy.2⟩
    have h2 := S.sec_eq j k (y := y') ⟨hy.1.2, hy.2⟩
    rw [S.sec_eq i j (y := y') hy.1, S.act_mul] at h2
    have := congrArg (fun q => (S.e i q).2) (h2.symm.trans h1)
    simpa only [S.e_sec_act i (y := y') hy.1.1] using this

end SpinStructure

namespace SpinLiftData

variable (D : SpinLiftData Fs)

/-- The spin structure glued from a cocycle. -/
def toStructure : SpinStructure Fs where
  W := D.W
  isOpen_W := D.isOpen_W
  P := D.P
  top := inferInstance
  projS := D.core.proj
  actS := D.actS
  Φ := D.Φ
  act_one := D.actS_one
  act_mul := D.actS_mul
  proj_act := D.proj_actS
  continuous_act := D.continuous_actS₂
  ι := D.ι
  V := D.V
  V_sub := D.V_sub
  cover := D.cover
  e := D.core.localTriv
  baseSet_e _ := rfl
  e_act i p _ t := D.localTriv_actS i p t
  continuous_Φ := D.continuous_Φ
  proj_Φ := D.proj_Φ
  Φ_act := D.Φ_actS

end SpinLiftData

namespace SpinStructure

variable (S : SpinStructure Fs)

/-- The image of `Φ` in terms of the local frames. -/
lemma range_Φ_eq : Set.range S.Φ = Set.range S.toData.Φ := by
  rw [S.toData.range_Φ]
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨by rw [S.proj_Φ]; exact (S.projS p).2, fun (i : S.ι) hi => ?_⟩
    have hp : (S.projS p : Fs.B) ∈ S.V i := by rw [S.proj_Φ] at hi; exact hi
    refine ⟨spinToO77 (S.e i p).2, spinToO77_mem _, ?_⟩
    rw [S.proj_Φ]
    show S.Φ p = Fs.act (S.σd i (S.projS p : Fs.B)) _
    have e := S.σd_val i (S.projS p)
    rw [e, ← S.Φ_act, S.sec_act_coord i hp]
  · rintro ⟨hW, hq⟩
    obtain ⟨i, hi⟩ := S.cover (Fs.proj q) hW
    obtain ⟨g, hg, hqg⟩ := hq i hi
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
    let y : S.W := ⟨Fs.proj q, hW⟩
    refine ⟨S.actS (S.sec i y) t, ?_⟩
    rw [S.Φ_act, show spinToO77 t = g from congrArg Subtype.val ht, hqg]
    show Fs.act (S.Φ (S.sec i y)) g = Fs.act (S.σd i (y : Fs.B)) g
    rw [S.σd_val]

/-- The chart index of the glued bundle. -/
def idx (y : S.W) : S.ι := S.toData.core.indexAt y

lemma mem_idx (y : S.W) : (y : Fs.B) ∈ S.V (S.idx y) := S.toData.core.mem_baseSet_at y

/-- From the glued bundle to `S`. -/
def glueTo (q : S.toData.P) : S.P :=
  S.actS (S.sec (S.idx q.proj) q.proj) (S.toData.sp q)

/-- From `S` to the glued bundle. -/
def glueFrom (p : S.P) : S.toData.P :=
  ⟨S.projS p, (S.e (S.idx (S.projS p)) p).2⟩

lemma glueTo_chart (i : S.ι) {q : S.toData.P} (hq : ((q.proj : S.W) : Fs.B) ∈ S.V i) :
    S.glueTo q = S.actS (S.sec i q.proj) (S.toData.core.localTriv i q).2 := by
  let y : S.W := q.proj
  set a := S.idx y
  have ha : (y : Fs.B) ∈ S.V a := S.mem_idx y
  show _ = S.actS (S.sec i y) ((S.hd a i (y : Fs.B))⁻¹ * S.toData.sp q)
  rw [S.hd_val, S.sec_eq a i (y := y) ⟨ha, hq⟩, S.act_mul, mul_inv_cancel_left]; rfl

lemma localTriv_glueFrom (i : S.ι) {p : S.P} (hp : (S.projS p : Fs.B) ∈ S.V i) :
    S.toData.core.localTriv i (S.glueFrom p) = S.e i p := by
  set a := S.idx (S.projS p)
  have ha : (S.projS p : Fs.B) ∈ S.V a := S.mem_idx _
  have h1 := S.sec_act_coord i hp
  rw [S.sec_eq a i ⟨ha, hp⟩, S.act_mul] at h1
  have h2 := congrArg (fun r => (S.e a r).2) h1
  simp only [S.e_sec_act a ha] at h2
  refine Prod.ext (S.fst_e i hp).symm ?_
  show (S.hd a i (S.projS p : Fs.B))⁻¹ * (S.e a p).2 = (S.e i p).2
  rw [S.hd_val, ← h2, inv_mul_cancel_left]

lemma continuous_glueTo : Continuous S.glueTo := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  set i := S.idx q.proj
  set t := S.toData.core.localTriv i
  have hq : q ∈ t.source := S.mem_idx q.proj
  have h0 : ContinuousOn t t.source := t.toOpenPartialHomeomorph.continuousOn
  have hF : ContinuousOn (fun z : S.W × Spin77 => S.actS (S.sec i z.1) z.2)
      ((Subtype.val ⁻¹' S.V i) ×ˢ Set.univ) :=
    S.continuous_act.comp_continuousOn
      (((S.continuousOn_sec i).comp continuousOn_fst fun z hz => hz.1).prodMk continuousOn_snd)
  have hc : ContinuousOn S.glueTo t.source := by
    refine (ContinuousOn.comp hF h0 fun r hr => ?_).congr fun r hr => S.glueTo_chart i hr
    exact ⟨(t.coe_fst hr).symm ▸ hr, Set.mem_univ _⟩
  exact hc.continuousAt (t.open_source.mem_nhds hq)

lemma continuous_glueFrom : Continuous S.glueFrom := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
  set t := S.toData.core.localTriv i
  have hps : p ∈ (S.e i).source := (S.mem_source_iff i p).mpr hi
  have h0 : ContinuousOn (S.e i) (S.e i).source := (S.e i).toOpenPartialHomeomorph.continuousOn
  have hc : ContinuousOn S.glueFrom (S.e i).source := by
    have h1 : ContinuousOn (fun r => t.toOpenPartialHomeomorph.symm (S.e i r)) (S.e i).source :=
      ContinuousOn.comp t.toOpenPartialHomeomorph.continuousOn_symm h0 fun r hr => by
        show _ ∈ t.target
        rw [t.target_eq]
        have hr' := (S.mem_source_iff i r).mp hr
        refine ⟨?_, Set.mem_univ _⟩
        show (((S.e i r).1 : S.W) : Fs.B) ∈ S.V i
        rw [S.fst_e i hr']; exact hr'
    refine h1.congr fun r hr => ?_
    have hr' := (S.mem_source_iff i r).mp hr
    have hmem : S.glueFrom r ∈ t.source := hr'
    have := t.left_inv hmem
    have h2 : t.toOpenPartialHomeomorph (S.glueFrom r) = S.e i r := S.localTriv_glueFrom i hr'
    rw [h2] at this
    exact this.symm
  exact hc.continuousAt ((S.e i).open_source.mem_nhds hps)

lemma proj_glueTo (q : S.toData.P) : S.projS (S.glueTo q) = q.proj := by
  unfold glueTo; rw [S.proj_act, S.proj_sec _ (S.mem_idx q.proj)]

/-- **Every spin structure is isomorphic to the one glued from its own cocycle.** -/
def isoToData : SpinIso S.toData.toStructure S where
  F :=
    { toFun := S.glueTo
      invFun := S.glueFrom
      left_inv := fun (q : S.toData.P) => by
        have hp := S.proj_glueTo q
        refine S.toData.ext' hp ?_
        show (S.e (S.idx (S.projS (S.glueTo q))) (S.glueTo q)).2 = S.toData.sp q
        rw [hp]; unfold glueTo
        rw [S.e_sec_act _ (S.mem_idx q.proj)]
      right_inv := fun p => S.sec_act_coord _ (S.mem_idx (S.projS p))
      continuous_toFun := S.continuous_glueTo
      continuous_invFun := S.continuous_glueFrom }
  proj_F q := congrArg Subtype.val (S.proj_glueTo q)
  act_F q t := by
    show S.glueTo (S.toData.actS q t) = S.actS (S.glueTo q) t
    unfold glueTo; rw [S.act_mul]; rfl
  Φ_F := fun (q : S.toData.P) => by
    show S.Φ (S.glueTo q) = S.toData.Φ q
    unfold glueTo; rw [S.Φ_act]
    exact congrArg (fun r => Fs.act r (spinToO77 (S.toData.sp q))) (S.σd_val _ _).symm

/-- **The fibres of `Φ` are the two points `{p, p·(−1)}`.** -/
theorem Φ_eq_iff (p q : S.P) : S.Φ p = S.Φ q ↔ q = p ∨ q = S.actS p negOne := by
  constructor
  · intro hpq
    have hproj : S.projS p = S.projS q :=
      Subtype.ext (by rw [← S.proj_Φ p, ← S.proj_Φ q, hpq])
    obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
    have hq : (S.projS q : Fs.B) ∈ S.V i := hproj ▸ hi
    have hP := S.sec_act_coord i hi
    have hQ := S.sec_act_coord i hq
    rw [← hproj] at hQ
    have e : spinToO77 (S.e i p).2 = spinToO77 (S.e i q).2 := by
      apply Fs.cancel (q := S.Φ (S.sec i (S.projS p)))
      rw [← S.Φ_act, ← S.Φ_act, hP, hQ, hpq]
    have e' : spinToO77 ((S.e i p).2⁻¹ * (S.e i q).2) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    rcases (spinToO77_eq_one_iff _).mp e' with h1 | h1
    · left
      rw [inv_mul_eq_one] at h1
      rw [← hQ, ← h1, hP]
    · right
      have h2 : (S.e i q).2 = (S.e i p).2 * negOne := by rw [← h1]; group
      rw [← hQ, h2, ← S.act_mul, hP]
  · rintro (rfl | rfl)
    · rfl
    · rw [S.Φ_act, spinToO77_negOne, Fs.act_one]

/-- The two sheets are distinct. -/
lemma act_negOne_ne (p : S.P) : S.actS p negOne ≠ p := fun h => negOne_ne_one (S.act_free p _ h)

/-- **`Φ` is a covering map onto its image.** -/
theorem isCoveringMap_Φ : IsCoveringMap (Set.rangeFactorization S.Φ) := by
  have hc := S.toData.isCoveringMap_Φ
  let I := S.isoToData
  have h1 := hc.comp_homeomorph I.F.symm
  have h2 := h1.homeomorph_comp (Homeomorph.setCongr S.range_Φ_eq.symm)
  convert h2 using 1
  funext p
  apply Subtype.ext
  show S.Φ p = S.toData.Φ (I.F.symm p)
  have := I.Φ_F (I.F.symm p)
  rw [Homeomorph.apply_symm_apply] at this
  exact this

end SpinStructure

/-- **Cocycle lifts exist iff a spin structure exists** (with the same image in the frames). -/
theorem exists_data_iff_exists_structure (Q : Set (Fs.Fr)) :
    (∃ D : SpinLiftData Fs, Set.range D.Φ = Q) ↔ ∃ S : SpinStructure Fs, Set.range S.Φ = Q :=
  ⟨fun ⟨D, hD⟩ => ⟨D.toStructure, hD⟩,
   fun ⟨S, hS⟩ => ⟨S.toData, S.range_Φ_eq.symm.trans hS⟩⟩

/-- **Cocycle lifts exist iff a spin structure exists.** -/
theorem nonempty_data_iff_nonempty_structure :
    Nonempty (SpinLiftData Fs) ↔ Nonempty (SpinStructure Fs) :=
  ⟨fun ⟨D⟩ => ⟨D.toStructure⟩, fun ⟨S⟩ => ⟨S.toData⟩⟩


end

end Gen

/-! ### The original theory is the case `ofrFS` -/

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Spin-lift data over `Y13` are generic spin-lift data for `ofrFS X` (field by field). -/
def SpinLiftData.toGen (D : SpinLiftData X) : Gen.SpinLiftData (ofrFS X) :=
  ⟨D.W, D.isOpen_W, D.ι, D.V, D.isOpen_V, D.V_sub, D.cover, D.σ, D.cont_σ, D.proj_σ, D.h, D.cont_h,
    D.lift, D.cocycle⟩

/-- A spin structure over `Y13` is a generic spin structure for `ofrFS X` (field by field). -/
def SpinStructure.toGen (S : SpinStructure X) : Gen.SpinStructure (ofrFS X) :=
  ⟨S.W, S.isOpen_W, S.P, S.top, S.projS, S.actS, S.Φ, S.act_one, S.act_mul, S.proj_act, S.continuous_act,
    S.ι, S.V, S.V_sub, S.cover, S.e, S.baseSet_e, S.e_act, S.continuous_Φ, S.proj_Φ, S.Φ_act⟩

/-- **Non-vacuity for `ofrFS`**: generic spin-lift data near every point of `Y13`. -/
theorem exists_gen_data_near (b : Y13o X) : ∃ D : Gen.SpinLiftData (ofrFS X), b ∈ D.W := by
  obtain ⟨D, hD⟩ := exists_spinLiftData_near b
  exact ⟨D.toGen, hD⟩

end

end GU.Library
