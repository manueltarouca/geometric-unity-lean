import GU.Bundle.FramePrincipal
import GU.Spinor.SpinConnected
import GU.Spinor.TorusKernel

/-!
# Phase 3, item 4: the spin structure (w₂ = 0 in cocycle form ⇒ a Spin(7,7) double cover)

**Data** (`SpinLiftData`): an open `W ⊆ Y13` (for nonempty `X`, not all of `Y13`: `no_spinLiftData`), an open cover
`V i` of `W`, continuous local sections `σ i` of the
frame bundle `OFr` over `V i`, and continuous `Spin(7,7)`-valued lifts `h i j` of the transition
functions (`σ j = σ i · ρ(h i j)` on `V i ∩ V j`, `ρ = spinToO77`). For *any* such lifts the
defect `h i j · h j k · (h i k)⁻¹` lies in `{±1}` (`spinLift_defect_mem`): informally the Čech
`ℤ/2`-cochain whose class is `w₂` (`w₂` itself is not formalised). Since `ρ` lands in `SO₀`, the
data also fix an `SO₀(7,7)`-reduction of `OFr` (orientation and time orientation). **Hypothesis**:
the lifts can be chosen with trivial defect (`cocycle`: `h i j · h j k = h i k`), i.e. "`SO₀`-reduction
with `w₂ = 0`". The hypotheses have instances over small `W` (`ofSection`, `SpinExamples.lean`).

**Conclusion** (`spin_lift`, `spin_structure_of_lift`): a topological principal
`Spin(7,7)`-bundle `P̃ → W` (`core`/`P`, glued by `FiberBundleCore`; jointly continuous right
action `actS`, free, fibre-transitive, right multiplication in every local trivialisation) and a
continuous, base-preserving, `ρ`-equivariant map `Φ : P̃ → OFr` whose fibres are exactly the two
distinct points `{p, p·(−1)}` (`Φ_eq_iff`, `actS_negOne_ne`), whose image is the `SO₀`-reduction
determined by the `σ i` (`range_Φ`), and which is a **covering map onto its image**
(`isCoveringMap_Φ`, via `IsQuotientCoveringMap` for the kernel `{±1}` of `Spin(7,7) → SO₀(7,7)`).
Not addressed here: the converse (`SpinConverse.lean`), independence of the choices
(`SpinTwist.lean`), smoothness. So `P̃` is a spin structure: a `Spin(7,7)`-bundle
double-covering the `SO₀(7,7)`-frames. (Topological statement; smoothness of `P̃` is not stated.)
This is the genuine (topological) counterpart of the set-level lift in `SpinLift.lean`.
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### Frame-bundle helpers -/

lemma actOFr'_mul (q : OFr X) (g g' : O77) : actOFr' (actOFr' q g) g' = actOFr' q (g * g') :=
  Subtype.ext (ractM_mul _ _ _)

lemma actOFr'_one (q : OFr X) : actOFr' q 1 = q := Subtype.ext (ractM_one _)

lemma projOFr_act (q : OFr X) (g : O77) : projOFr (actOFr' q g) = projOFr q := rfl

lemma actOFr'_cancel {q : OFr X} {g g' : O77} (h : actOFr' q g = actOFr' q g') : g = g' := by
  have hq : (q : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact q.2
  have : actOFr' q (g * g'⁻¹) = q := by
    rw [← actOFr'_mul, h, actOFr'_mul, mul_inv_cancel, actOFr'_one]
  exact mul_inv_eq_one.mp (ractM_free hq _ (congrArg Subtype.val this))

lemma continuous_actOFr' : Continuous (fun qg : OFr X × O77 => actOFr' qg.1 qg.2) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  exact (contMDiff_actOFr (X := X)).continuous

lemma continuous_projOFr : Continuous (projOFr (X := X)) := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  exact (frameBundle (X := X)).smooth_proj.continuous

lemma spinToO77_eq_one_iff (x : Spin77) : spinToO77 x = 1 ↔ x = 1 ∨ x = negOne := by
  have hk : x ∈ spinToSO0.ker ↔ spinToO77 x = 1 :=
    ⟨fun h => congrArg Subtype.val (MonoidHom.mem_ker.mp h),
     fun h => MonoidHom.mem_ker.mpr (Subtype.ext h)⟩
  rw [← hk]
  have := ker_spinToSO0_eq
  rw [Set.ext_iff] at this
  simpa using this x

lemma spinToO77_negOne : spinToO77 negOne = 1 := (spinToO77_eq_one_iff _).mpr (Or.inr rfl)

lemma negOne_inv : negOne⁻¹ = negOne :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, negOne_sq])

/-! ### The data -/

/-- **Spin-lift data over an open `W ⊆ Y13`**: local sections of `OFr` over an open cover of `W` with
continuous `Spin(7,7)` lifts of their transition functions satisfying the cocycle identity
(`w₂ = 0`). `W` cannot contain a full loop of metrics in a fibre (`no_spinLiftData`). -/
structure SpinLiftData (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] where
  W : Set (Y13o X)
  isOpen_W : IsOpen W
  ι : Type
  V : ι → Set (Y13o X)
  isOpen_V : ∀ i, IsOpen (V i)
  V_sub : ∀ i, V i ⊆ W
  cover : ∀ y ∈ W, ∃ i, y ∈ V i
  σ : ι → Y13o X → OFr X
  cont_σ : ∀ i, ContinuousOn (σ i) (V i)
  proj_σ : ∀ i, ∀ y ∈ V i, projOFr (σ i y) = y
  h : ι → ι → Y13o X → Spin77
  cont_h : ∀ i j, ContinuousOn (h i j) (V i ∩ V j)
  lift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = actOFr' (σ i y) (spinToO77 (h i j y))
  cocycle : ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, h i j y * h j k y = h i k y

/-- **The `w₂` defect**: for any continuous lifts of the transition functions (no cocycle
hypothesis), `h i j · h j k · (h i k)⁻¹ ∈ {1, −1}` on triple overlaps. -/
theorem spinLift_defect_mem {ι : Type} {V : ι → Set (Y13o X)} {σ : ι → Y13o X → OFr X}
    {h : ι → ι → Y13o X → Spin77}
    (lift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = actOFr' (σ i y) (spinToO77 (h i j y)))
    {i j k : ι} {y : Y13o X} (hy : y ∈ V i ∩ V j ∩ V k) :
    h i j y * h j k y * (h i k y)⁻¹ = 1 ∨ h i j y * h j k y * (h i k y)⁻¹ = negOne := by
  rw [← spinToO77_eq_one_iff]
  have e1 := lift j k y ⟨hy.1.2, hy.2⟩
  have e2 := lift i j y hy.1
  have e3 := lift i k y ⟨hy.1.1, hy.2⟩
  rw [e2, actOFr'_mul, e3] at e1
  have := actOFr'_cancel e1
  rw [map_mul, map_mul, map_inv, ← this, mul_inv_cancel]

namespace SpinLiftData

variable (D : SpinLiftData X)

lemma h_self (i : D.ι) {y : Y13o X} (hy : y ∈ D.V i) : D.h i i y = 1 := by
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

/-- **The double-cover map** `Φ : P̃ → OFr`. -/
def Φ (p : D.P) : OFr X := actOFr' (D.σ (D.core.indexAt p.proj) p.proj) (spinToO77 (D.sp p))

lemma localTriv_apply' (i : D.ι) (p : D.P) :
    D.core.localTriv i p = (p.proj, (D.h (D.core.indexAt p.proj) i p.proj)⁻¹ * D.sp p) := rfl

lemma mem_baseSet_at' (y : D.W) : (y : Y13o X) ∈ D.V (D.core.indexAt y) :=
  D.core.mem_baseSet_at y

/-- **Chart formula**: in the trivialisation `i`, `Φ (y, s) = σ i y · ρ(s)`. -/
lemma Φ_chart (i : D.ι) {p : D.P} (hp : (p.proj : Y13o X) ∈ D.V i) :
    D.Φ p = actOFr' (D.σ i p.proj) (spinToO77 (D.core.localTriv i p).2) := by
  set a := D.core.indexAt p.proj
  have ha : (p.proj : Y13o X) ∈ D.V a := D.mem_baseSet_at' p.proj
  rw [localTriv_apply', D.lift a i p.proj ⟨ha, hp⟩, actOFr'_mul, ← map_mul, mul_inv_cancel_left]
  rfl

lemma proj_Φ (p : D.P) : projOFr (D.Φ p) = p.proj :=
  D.proj_σ _ _ (D.mem_baseSet_at' p.proj)

lemma Φ_actS (p : D.P) (t : Spin77) : D.Φ (D.actS p t) = actOFr' (D.Φ p) (spinToO77 t) := by
  show actOFr' _ (spinToO77 (D.sp p * t)) = _
  rw [map_mul, ← actOFr'_mul]; rfl

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
      unfold Φ at hpq; rw [hproj] at hpq; exact actOFr'_cancel hpq
    have e' : spinToO77 ((D.sp p)⁻¹ * D.sp q) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    rcases (spinToO77_eq_one_iff _).mp e' with h1 | h1
    · left; exact D.ext' hproj.symm (by rw [inv_mul_eq_one] at h1; exact h1.symm)
    · right
      exact D.ext' hproj.symm (by
        show D.sp q = D.sp p * negOne
        rw [← h1]; group)
  · rintro (rfl | rfl)
    · rfl
    · rw [D.Φ_actS, spinToO77_negOne, actOFr'_one]

/-- `Φ` is continuous. -/
theorem continuous_Φ : Continuous D.Φ := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  set i := D.core.indexAt p.proj
  set e := D.core.localTriv i
  have hp : p ∈ e.source := D.core.mem_baseSet_at p.proj
  have hF : ContinuousOn (fun z : D.W × Spin77 => actOFr' (D.σ i z.1) (spinToO77 z.2))
      ((Subtype.val ⁻¹' D.V i) ×ˢ Set.univ) :=
    continuous_actOFr'.comp_continuousOn
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

lemma exists_τ (i : D.ι) {q : OFr X} (hq : projOFr q ∈ D.V i) :
    ∃ g, actOFr' (D.σ i (projOFr q)) g = q := by
  obtain ⟨g, hg⟩ := ractM_transitive' (q := ((D.σ i (projOFr q) : OFr X) : HomTotM X))
    (q' := (q : HomTotM X))
    (by rw [← levelSet_Fframe]; exact (D.σ i (projOFr q)).2)
    (by rw [← levelSet_Fframe]; exact q.2)
    (congrArg Subtype.val (D.proj_σ i _ hq))
  exact ⟨g, Subtype.ext hg⟩

open Classical in
/-- `τ i q`: the `O77`-coordinate of `q` relative to the section `σ i`. -/
def τ (i : D.ι) (q : OFr X) : O77 :=
  if hq : projOFr q ∈ D.V i then (D.exists_τ i hq).choose else 1

lemma τ_spec (i : D.ι) {q : OFr X} (hq : projOFr q ∈ D.V i) :
    actOFr' (D.σ i (projOFr q)) (D.τ i q) = q := by
  unfold τ; rw [dite_cond_eq_true (eq_true hq)]
  exact (D.exists_τ i hq).choose_spec

lemma τ_unique (i : D.ι) {q : OFr X} {g : O77} (hq : projOFr q ∈ D.V i)
    (h : actOFr' (D.σ i (projOFr q)) g = q) : D.τ i q = g :=
  actOFr'_cancel ((D.τ_spec i hq).trans h.symm)

/-- **`τ i` is continuous** on the preimage of `V i`. -/
theorem continuousOn_τ (i : D.ι) : ContinuousOn (D.τ i) (projOFr ⁻¹' D.V i) := by
  intro q0 hq0
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨V', hV', hq0V', σ', τ', -, -, hτ', hrec⟩ := (frameBundle (X := X)).locTriv (projOFr q0)
  have hτc : ContinuousOn τ' (projOFr ⁻¹' V') := hτ'.continuousOn
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
  have hT : ContinuousOn (fun q => τ' (D.σ i (projOFr q))) N :=
    hτc.comp ((D.cont_σ i).comp continuous_projOFr.continuousOn fun q hq => hq.1) fun q hq => by
      show projOFr (D.σ i (projOFr q)) ∈ V'
      rw [D.proj_σ i _ hq.1]; exact hq.2
  have hR : ContinuousOn (fun q => (τ' (D.σ i (projOFr q)))⁻¹ * τ' q) N :=
    hT.inv.mul (hτc.mono fun q hq => hq.2)
  exact ((hR.congr hform).continuousAt (hN.mem_nhds ⟨hq0, hq0V'⟩)).continuousWithinAt

/-! ### The image and the covering -/

/-- **The image of `Φ` is the `SO₀`-part of `OFr`.** -/
theorem range_Φ : Set.range D.Φ =
    {q | projOFr q ∈ D.W ∧
      ∀ i, projOFr q ∈ D.V i → ∃ g ∈ SO0, q = actOFr' (D.σ i (projOFr q)) g} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨by rw [D.proj_Φ]; exact p.proj.2, fun i hi => ?_⟩
    rw [D.proj_Φ] at hi ⊢
    exact ⟨_, spinToO77_mem _, D.Φ_chart i hi⟩
  · rintro ⟨hW, hq⟩
    let y : D.W := ⟨projOFr q, hW⟩
    set a := D.core.indexAt y
    obtain ⟨g, hg, hqg⟩ := hq a (D.mem_baseSet_at' y)
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
    refine ⟨⟨y, t⟩, ?_⟩
    show actOFr' (D.σ a (y : Y13o X)) (spinToO77 t) = q
    rw [show spinToO77 t = g from congrArg Subtype.val ht]
    exact hqg.symm

lemma τ_mem_SO0 (i : D.ι) {q : OFr X} (hq : q ∈ Set.range D.Φ) (hi : projOFr q ∈ D.V i) :
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
  have hpi : (p.proj : Y13o X) ∈ D.V i := D.mem_baseSet_at' p.proj
  have hps : p ∈ tr.source := hpi
  have himg : IsOpen (tr '' (W ∩ tr.source)) :=
    tr.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hW.inter tr.open_source)
      Set.inter_subset_right
  obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ :=
    isOpen_prod_iff.mp himg (tr p).1 (tr p).2 ⟨p, ⟨hpW, hps⟩, rfl⟩
  obtain ⟨O0, hO0, hO0B⟩ := isOpen_induced_iff.mp (isOpenMap_spinToSO0 B hB)
  have hA' : IsOpen (Subtype.val '' A : Set (Y13o X)) := D.isOpen_W.isOpenMap_subtype_val A hA
  set O : Set (OFr X) := projOFr ⁻¹' ((Subtype.val '' A) ∩ D.V i) ∩ D.τ i ⁻¹' O0
  have hO : IsOpen O :=
    ((D.continuousOn_τ i).mono fun q hq => hq.2).isOpen_inter_preimage
      ((hA'.inter (D.isOpen_V i)).preimage continuous_projOFr) hO0
  have hfst : (tr p).1 = p.proj := rfl
  refine ⟨Subtype.val ⁻¹' O, ?_, hO.preimage continuous_subtype_val, ?_⟩
  · rintro ⟨q, hqr⟩ ⟨⟨⟨a0, ha0, hqa⟩, hqi⟩, hqO⟩
    have hSO := D.τ_mem_SO0 i hqr hqi
    have hmem : (⟨D.τ i q, hSO⟩ : SO0) ∈ spinToSO0 '' B := by rw [← hO0B]; exact hqO
    obtain ⟨t, htB, ht⟩ := hmem
    obtain ⟨p', ⟨hp'W, hp's⟩, hp'⟩ := hAB (show (a0, t) ∈ A ×ˢ B from ⟨ha0, htB⟩)
    refine ⟨p', hp'W, Subtype.ext ?_⟩
    show D.Φ p' = q
    have hy : (p'.proj : Y13o X) = projOFr q := by
      rw [← hqa]; exact congrArg (fun z => ((z.1 : D.W) : Y13o X)) hp'
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
      rw [D.Φ_actS, map_inv, spinToO77_of_ker, inv_one, actOFr'_one]
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

/-- **`Φ : P̃ → OFr` is a covering map onto its image.** -/
theorem isCoveringMap_Φ : IsCoveringMap (Set.rangeFactorization D.Φ) := by
  letI := D.kerAct
  exact D.isQuotientCoveringMap_Φ.isCoveringMap

/-- **A frame over an open `W` gives spin-lift data** (one chart, trivial lifts). Such frames exist
locally (`exists_spinLiftData_near`, `SpinExamples.lean`). -/
def ofSection (W : Set (Y13o X)) (hW : IsOpen W) (σ : Y13o X → OFr X) (hσ : ContinuousOn σ W)
    (hσp : ∀ y ∈ W, projOFr (σ y) = y) : SpinLiftData X :=
  ⟨W, hW, Unit, fun _ => W, fun _ => hW, fun _ => subset_rfl, fun _ hy => ⟨(), hy⟩, fun _ => σ,
    fun _ => hσ, fun _ y hy => hσp y hy, fun _ _ _ => 1, fun _ _ => continuousOn_const,
    fun _ _ y _ => by rw [map_one, actOFr'_one], fun _ _ _ _ _ => mul_one 1⟩

/-- **Phase 3, item 4 (spin lift)**: from spin-lift data (`w₂ = 0` in cocycle form), `P̃` is a
topological principal `Spin(7,7)`-bundle over `W` (local trivialisations over the `V i`, in which
the action is right multiplication; free, fibre-transitive action), and `Φ : P̃ → OFr` is a
continuous, base-preserving, `ρ`-equivariant double cover of the `SO₀`-reduction of `OFr`
determined by the `σ i`. -/
theorem spin_lift :
    Continuous D.core.proj ∧
    (∀ i, (D.core.localTriv i).baseSet = Subtype.val ⁻¹' D.V i ∧ ∀ p t,
      D.core.localTriv i (D.actS p t) = ((D.core.localTriv i p).1, (D.core.localTriv i p).2 * t)) ∧
    (∀ p, D.actS p 1 = p) ∧ (∀ p s t, D.actS (D.actS p s) t = D.actS p (s * t)) ∧
    (∀ p t, (D.actS p t).proj = p.proj) ∧ (∀ p t, D.actS p t = p → t = 1) ∧
    (∀ p q : D.P, p.proj = q.proj → ∃ t, D.actS p t = q) ∧
    Continuous (fun pt : D.P × Spin77 => D.actS pt.1 pt.2) ∧ (∀ p, D.actS p negOne ≠ p) ∧
    Continuous D.Φ ∧ (∀ p, projOFr (D.Φ p) = p.proj) ∧
    (∀ p t, D.Φ (D.actS p t) = actOFr' (D.Φ p) (spinToO77 t)) ∧
    (∀ p q, D.Φ p = D.Φ q ↔ q = p ∨ q = D.actS p negOne) ∧
    Set.range D.Φ = {q | projOFr q ∈ D.W ∧
      ∀ i, projOFr q ∈ D.V i → ∃ g ∈ SO0, q = actOFr' (D.σ i (projOFr q)) g} ∧
    IsCoveringMap (Set.rangeFactorization D.Φ) :=
  ⟨D.core.continuous_proj, fun i => ⟨rfl, D.localTriv_actS i⟩, D.actS_one, D.actS_mul,
    D.proj_actS, D.actS_free, D.actS_transitive, D.continuous_actS₂, D.actS_negOne_ne, D.continuous_Φ, D.proj_Φ, D.Φ_actS, D.Φ_eq_iff,
    D.range_Φ, D.isCoveringMap_Φ⟩

end SpinLiftData

/-- **Spin structure from a `ℤ/2`-lift of the transition cocycle.** Given continuous local
sections `σ i` of the frame bundle over an open cover of an open `W ⊆ Y13` and continuous `Spin(7,7)` lifts
`h i j` of their transition functions satisfying the cocycle identity (equivalently: the `w₂`
defect of `spinLift_defect_mem` is trivial), there is a topological principal `Spin(7,7)`-bundle
`P̃ → W` (jointly continuous, free, fibre-transitive right action; local trivialisations over the
`V i` in which the action is right multiplication) and a continuous, `ρ`-equivariant map
`Φ : P̃ → OFr` whose fibres are the two points `{p, p·(−1)}`, whose image is the `SO₀`-reduction
determined by the `σ i`, and which is
a covering map onto its image. -/
theorem spin_structure_of_lift (W : Set (Y13o X)) (hW : IsOpen W) {ι : Type}
    (V : ι → Set (Y13o X)) (hV : ∀ i, IsOpen (V i)) (hVW : ∀ i, V i ⊆ W)
    (hcov : ∀ y ∈ W, ∃ i, y ∈ V i) (σ : ι → Y13o X → OFr X) (hσ : ∀ i, ContinuousOn (σ i) (V i))
    (hσp : ∀ i, ∀ y ∈ V i, projOFr (σ i y) = y) (h : ι → ι → Y13o X → Spin77)
    (hh : ∀ i j, ContinuousOn (h i j) (V i ∩ V j))
    (hlift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = actOFr' (σ i y) (spinToO77 (h i j y)))
    (hcoc : ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, h i j y * h j k y = h i k y) :
    ∃ (P : Type) (_ : TopologicalSpace P) (projS : P → W) (actS : P → Spin77 → P)
      (Φ : P → OFr X),
      Continuous projS ∧ (∀ p, actS p 1 = p) ∧ (∀ p s t, actS (actS p s) t = actS p (s * t)) ∧
      (∀ p t, projS (actS p t) = projS p) ∧ (∀ p t, actS p t = p → t = 1) ∧
      (∀ p q, projS p = projS q → ∃ t, actS p t = q) ∧
      (∀ i, ∃ e : Trivialization Spin77 projS, e.baseSet = Subtype.val ⁻¹' V i ∧
        ∀ p ∈ e.source, ∀ t, e (actS p t) = ((e p).1, (e p).2 * t)) ∧
      Continuous (fun pt : P × Spin77 => actS pt.1 pt.2) ∧ (∀ p, actS p negOne ≠ p) ∧
      Continuous Φ ∧ (∀ p, projOFr (Φ p) = projS p) ∧
      (∀ p t, Φ (actS p t) = actOFr' (Φ p) (spinToO77 t)) ∧
      (∀ p q, Φ p = Φ q ↔ q = p ∨ q = actS p negOne) ∧
      Set.range Φ = {q | projOFr q ∈ W ∧
        ∀ i, projOFr q ∈ V i → ∃ g ∈ SO0, q = actOFr' (σ i (projOFr q)) g} ∧
      IsCoveringMap (Set.rangeFactorization Φ) := by
  let D : SpinLiftData X := ⟨W, hW, ι, V, hV, hVW, hcov, σ, hσ, hσp, h, hh, hlift, hcoc⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h7a, h7b, h8, h9, h10, h11, h12, h13⟩ := D.spin_lift
  exact ⟨D.P, inferInstance, D.core.proj, D.actS, D.Φ, h1, h3, h4, h5, h6, h7,
    fun i => ⟨D.core.localTriv i, (h2 i).1, fun p _ t => (h2 i).2 p t⟩, h7a, h7b, h8, h9, h10, h11,
    h12, h13⟩

end

end GU.Library
