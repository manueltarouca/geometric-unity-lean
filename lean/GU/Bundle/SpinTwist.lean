/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SpinConverse

/-!
# Phase 4, item 2: independence of the lift

Fix the frames `σ i` and the cover. Two lifts of the transition functions differ by a `{±1}`-valued
`η i j = h' i j · (h i j)⁻¹`, and the defect changes by `δη` (**`defect_of_lifts`**, from
`mul_defect`): `defect h' = δη · defect h`. A sign change by a coboundary `η i j = ε i · ε j`
(`ε i` a continuous `{±1}`-valued function on `V i`, i.e. a 0-cochain) leaves the defect unchanged
(`coboundary_defect`). So the defect class (informally `w₂`) does not depend on the lifts; the class
itself is not formalised.

**`iso_iff_coboundary`**: two cocycle lifts `h`, `h'` of the same frames on the same cover give
isomorphic spin structures (`SpinIso`) iff `h' i j = ε i · h i j · ε j` for a continuous
`{±1}`-valued `ε`. In particular a cocycle `η` that is not a coboundary gives a cocycle lift `η h`
whose spin structure is not isomorphic to that of `h`. `SpinLiftData.twist` is the lift
`ε i · h i j · ε j`, with `twistIso`. The resulting bijection of isomorphism classes with
`Ȟ¹(V; ℤ/2)`, and its identification with `H¹(Y13; ℤ/2)`, are not formalised.
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### Signs -/

/-- `t = ±1`. -/
def IsSign (t : Spin77) : Prop := t = 1 ∨ t = negOne

lemma negOne_comm (x : Spin77) : negOne * x = x * negOne :=
  Subtype.ext (by simp [negOne])

lemma IsSign.comm {t : Spin77} (h : IsSign t) (x : Spin77) : t * x = x * t := by
  rcases h with rfl | rfl
  · simp
  · exact negOne_comm x

lemma IsSign.mul_self {t : Spin77} (h : IsSign t) : t * t = 1 := by
  rcases h with rfl | rfl
  · simp
  · rw [← pow_two, negOne_sq]

lemma IsSign.inv {t : Spin77} (h : IsSign t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right h.mul_self

lemma IsSign.mul {s t : Spin77} (hs : IsSign s) (ht : IsSign t) : IsSign (s * t) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; rw [← pow_two, negOne_sq]

lemma isSign_iff (t : Spin77) : IsSign t ↔ spinToO77 t = 1 := (spinToO77_eq_one_iff t).symm

/-! ### The defect under a change of lift -/

/-- **Two lifts of the same frames differ by a sign.** -/
theorem lifts_differ_by_sign {q : OFr X} {a b : Spin77}
    (h : actOFr' q (spinToO77 a) = actOFr' q (spinToO77 b)) : IsSign (b * a⁻¹) := by
  rw [isSign_iff, map_mul, map_inv, ← actOFr'_cancel h, mul_inv_cancel]

/-- **The defect changes by the coboundary of the sign change** (`f`, `g` signs; `e` arbitrary). -/
theorem mul_defect {e f g : Spin77} (hf : IsSign f) (hg : IsSign g) (a b c : Spin77) :
    (e * a) * (f * b) * (g * c)⁻¹ = (e * f * g⁻¹) * (a * b * c⁻¹) := by
  have hg' : IsSign g⁻¹ := by rw [hg.inv]; exact hg
  calc (e * a) * (f * b) * (g * c)⁻¹
      = e * (a * f) * b * (c⁻¹ * g⁻¹) := by rw [mul_inv_rev]; group
    _ = e * f * (a * b * c⁻¹ * g⁻¹) := by rw [← hf.comm a]; group
    _ = (e * f * g⁻¹) * (a * b * c⁻¹) := by rw [← hg'.comm]; group

/-- A sign change by a coboundary does not change the defect. -/
theorem coboundary_defect {εi εj εk : Spin77} (hi : IsSign εi) (hj : IsSign εj) (hk : IsSign εk)
    (a b c : Spin77) :
    ((εi * a * εj) * (εj * b * εk)) * (εi * c * εk)⁻¹ = a * b * c⁻¹ := by
  have : (εi * a * εj) * (εj * b * εk) = εi * (a * b) * εk := by
    calc _ = εi * a * (εj * εj) * b * εk := by group
      _ = _ := by rw [hj.mul_self]; group
  rw [this, mul_inv_rev, mul_inv_rev, hk.inv, hi.inv]
  calc εi * (a * b) * εk * (εk * (c⁻¹ * εi))
      = εi * (a * b) * (εk * εk) * c⁻¹ * εi := by group
    _ = εi * (a * b * c⁻¹) * εi := by rw [hk.mul_self]; group
    _ = a * b * c⁻¹ * (εi * εi) := by rw [hi.comm]; group
    _ = _ := by rw [hi.mul_self, mul_one]

/-- **How the defect changes between two lifts of the same frames** (no cocycle hypothesis):
`η i j = h' i j · (h i j)⁻¹` is a sign, and `defect h' = δη · defect h`. -/
theorem defect_of_lifts {ι : Type} {V : ι → Set (Y13o X)} {σ : ι → Y13o X → OFr X}
    {h h' : ι → ι → Y13o X → Spin77}
    (hl : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = actOFr' (σ i y) (spinToO77 (h i j y)))
    (hl' : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = actOFr' (σ i y) (spinToO77 (h' i j y)))
    {i j k : ι} {y : Y13o X} (hy : y ∈ V i ∩ V j ∩ V k) :
    IsSign (h' i j y * (h i j y)⁻¹) ∧
    h' i j y * h' j k y * (h' i k y)⁻¹ =
      ((h' i j y * (h i j y)⁻¹) * (h' j k y * (h j k y)⁻¹) * (h' i k y * (h i k y)⁻¹)⁻¹) *
        (h i j y * h j k y * (h i k y)⁻¹) := by
  have hs : ∀ a b, y ∈ V a ∩ V b → IsSign (h' a b y * (h a b y)⁻¹) := fun a b hab =>
    lifts_differ_by_sign ((hl a b y hab).symm.trans (hl' a b y hab))
  refine ⟨hs i j hy.1, ?_⟩
  have := mul_defect (e := h' i j y * (h i j y)⁻¹) (hs j k ⟨hy.1.2, hy.2⟩) (hs i k ⟨hy.1.1, hy.2⟩)
    (h i j y) (h j k y) (h i k y)
  simpa only [inv_mul_cancel_right] using this

/-! ### A continuity lemma for bundle maps -/

lemma continuous_core_map {ι B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    (Z₁ Z₂ : FiberBundleCore ι B F) (hb : ∀ i, Z₂.baseSet i = Z₁.baseSet i)
    (f : ι → B → F → F)
    (hf : ∀ i, ContinuousOn (fun z : B × F => f i z.1 z.2) (Z₁.baseSet i ×ˢ Set.univ))
    (m : Z₁.TotalSpace → Z₂.TotalSpace) (hp : ∀ q, (m q).proj = q.proj)
    (hc : ∀ i q, q.proj ∈ Z₁.baseSet i → (Z₂.localTriv i (m q)).2 = f i q.proj (Z₁.localTriv i q).2) :
    Continuous m := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  set i := Z₁.indexAt q.proj
  set t₁ := Z₁.localTriv i
  set t₂ := Z₂.localTriv i
  have hq : q ∈ t₁.source := Z₁.mem_baseSet_at q.proj
  have h0 : ContinuousOn t₁ t₁.source := t₁.toOpenPartialHomeomorph.continuousOn
  have hg : ContinuousOn (fun r => ((t₁ r).1, f i (t₁ r).1 (t₁ r).2)) t₁.source := by
    have hmem : ∀ r ∈ t₁.source, t₁ r ∈ Z₁.baseSet i ×ˢ (Set.univ : Set F) := fun r hr =>
      ⟨(t₁.coe_fst hr).symm ▸ hr, Set.mem_univ _⟩
    exact (continuous_fst.comp_continuousOn h0).prodMk (ContinuousOn.comp (hf i) h0 hmem)
  have h1 : ContinuousOn (fun r => t₂.toOpenPartialHomeomorph.symm
      ((t₁ r).1, f i (t₁ r).1 (t₁ r).2)) t₁.source :=
    ContinuousOn.comp t₂.toOpenPartialHomeomorph.continuousOn_symm hg fun r hr => by
      show _ ∈ t₂.target
      rw [t₂.target_eq]
      refine ⟨?_, Set.mem_univ _⟩
      show (t₁ r).1 ∈ Z₂.baseSet i
      rw [hb, t₁.coe_fst hr]; exact hr
  have hc' : ContinuousOn m t₁.source := by
    refine h1.congr fun r hr => ?_
    have hr' : r.proj ∈ Z₁.baseSet i := hr
    have hmem : m r ∈ t₂.source := by
      show (m r).proj ∈ Z₂.baseSet i
      rw [hp, hb]; exact hr'
    have := t₂.left_inv hmem
    have h2 : t₂.toOpenPartialHomeomorph (m r) = ((t₁ r).1, f i (t₁ r).1 (t₁ r).2) := by
      refine Prod.ext (by show (m r).proj = r.proj; exact hp r) ?_
      show (t₂ (m r)).2 = f i r.proj (t₁ r).2
      exact hc i r hr'
    rw [h2] at this
    exact this.symm
  exact hc'.continuousAt (t₁.open_source.mem_nhds hq)

namespace SpinLiftData

variable (D : SpinLiftData X)

/-- The same frames with another cocycle lift. -/
def withH (h' : D.ι → D.ι → Y13o X → Spin77)
    (hc : ∀ i j, ContinuousOn (h' i j) (D.V i ∩ D.V j))
    (hl : ∀ i j, ∀ y ∈ D.V i ∩ D.V j, D.σ j y = actOFr' (D.σ i y) (spinToO77 (h' i j y)))
    (hcoc : ∀ i j k, ∀ y ∈ D.V i ∩ D.V j ∩ D.V k, h' i j y * h' j k y = h' i k y) :
    SpinLiftData X :=
  { D with h := h', cont_h := hc, lift := hl, cocycle := hcoc }

/-- The sign change `ε i · h i j · ε j` (`ε` a continuous sign on each `V i`). -/
def twist (ε : D.ι → Y13o X → Spin77) (hε : ∀ i, ∀ y ∈ D.V i, IsSign (ε i y))
    (hεc : ∀ i, ContinuousOn (ε i) (D.V i)) : SpinLiftData X :=
  D.withH (fun i j y => ε i y * D.h i j y * ε j y)
    (fun i j => (((hεc i).mono Set.inter_subset_left).mul (D.cont_h i j)).mul
      ((hεc j).mono Set.inter_subset_right))
    (fun i j y hy => by
      rw [D.lift i j y hy, map_mul, map_mul, (isSign_iff _).mp (hε i y hy.1),
        (isSign_iff _).mp (hε j y hy.2), one_mul, mul_one])
    (fun i j k y hy => by
      have hj := (hε j y hy.1.2).mul_self
      rw [← D.cocycle i j k y hy]
      calc ε i y * D.h i j y * ε j y * (ε j y * D.h j k y * ε k y)
          = ε i y * D.h i j y * (ε j y * ε j y) * D.h j k y * ε k y := by group
        _ = _ := by rw [hj]; group)

section Iso

variable {h' : D.ι → D.ι → Y13o X → Spin77}
  {hc : ∀ i j, ContinuousOn (h' i j) (D.V i ∩ D.V j)}
  {hl : ∀ i j, ∀ y ∈ D.V i ∩ D.V j, D.σ j y = actOFr' (D.σ i y) (spinToO77 (h' i j y))}
  {hcoc : ∀ i j k, ∀ y ∈ D.V i ∩ D.V j ∩ D.V k, h' i j y * h' j k y = h' i k y}
  {ε : D.ι → Y13o X → Spin77}

/-- The bundle map of a sign change. -/
def signTo (ε : D.ι → Y13o X → Spin77) (q : D.P) : (D.withH h' hc hl hcoc).P :=
  ⟨q.proj, ε (D.core.indexAt q.proj) q.proj * D.sp q⟩

/-- Its inverse. -/
def signFrom (ε : D.ι → Y13o X → Spin77) (q : (D.withH h' hc hl hcoc).P) : D.P :=
  ⟨q.proj, ε (D.core.indexAt q.proj) q.proj * (D.withH h' hc hl hcoc).sp q⟩

/-- **Isomorphism from a coboundary.** -/
def isoOfCoboundary (hε : ∀ i, ∀ y ∈ D.V i, IsSign (ε i y))
    (hεc : ∀ i, ContinuousOn (ε i) (D.V i))
    (hrel : ∀ i j, ∀ y ∈ D.V i ∩ D.V j, h' i j y = ε i y * D.h i j y * ε j y) :
    SpinIso D.toStructure (D.withH h' hc hl hcoc).toStructure := by
  have hcf : ∀ i, ContinuousOn (fun z : D.W × Spin77 => ε i z.1 * z.2)
      ((Subtype.val ⁻¹' D.V i) ×ˢ Set.univ) :=
    fun i => ((hεc i).comp (continuous_subtype_val.comp_continuousOn continuousOn_fst)
      fun z hz => hz.1).mul continuousOn_snd
  have hsgn : ∀ q : D.P, IsSign (ε (D.core.indexAt q.proj) q.proj) := fun q =>
    hε _ _ (D.mem_baseSet_at' q.proj)
  have hToC : ∀ i (q : D.P), (q.proj : Y13o X) ∈ D.V i →
      ((D.withH h' hc hl hcoc).core.localTriv i (D.signTo ε q)).2 =
        ε i q.proj * (D.core.localTriv i q).2 := by
    intro i q hq
    set a := D.core.indexAt q.proj
    have ha : (q.proj : Y13o X) ∈ D.V a := D.mem_baseSet_at' q.proj
    show (h' a i q.proj)⁻¹ * (ε a q.proj * D.sp q) = ε i q.proj * ((D.h a i q.proj)⁻¹ * D.sp q)
    rw [hrel a i q.proj ⟨ha, hq⟩, mul_inv_rev, mul_inv_rev, (hε i _ hq).inv, (hε a _ ha).inv]
    calc ε i q.proj * ((D.h a i q.proj)⁻¹ * ε a q.proj) * (ε a q.proj * D.sp q)
        = ε i q.proj * (D.h a i q.proj)⁻¹ * (ε a q.proj * ε a q.proj) * D.sp q := by group
      _ = _ := by rw [(hε a _ ha).mul_self]; group
  have hFromC : ∀ i (q : (D.withH h' hc hl hcoc).P), (q.proj : Y13o X) ∈ D.V i →
      (D.core.localTriv i (D.signFrom ε q)).2 =
        ε i q.proj * ((D.withH h' hc hl hcoc).core.localTriv i q).2 := by
    intro i q hq
    set a := D.core.indexAt q.proj
    have ha : (q.proj : Y13o X) ∈ D.V a := D.mem_baseSet_at' q.proj
    show (D.h a i q.proj)⁻¹ * (ε a q.proj * (D.withH h' hc hl hcoc).sp q) =
      ε i q.proj * ((h' a i q.proj)⁻¹ * (D.withH h' hc hl hcoc).sp q)
    rw [hrel a i q.proj ⟨ha, hq⟩, mul_inv_rev, mul_inv_rev, (hε i _ hq).inv, (hε a _ ha).inv]
    calc (D.h a i q.proj)⁻¹ * (ε a q.proj * (D.withH h' hc hl hcoc).sp q)
        = (ε i q.proj * ε i q.proj) * (D.h a i q.proj)⁻¹ * (ε a q.proj * (D.withH h' hc hl hcoc).sp q) := by
          rw [(hε i _ hq).mul_self, one_mul]
      _ = _ := by group
  exact
  { F :=
      { toFun := D.signTo ε
        invFun := D.signFrom ε
        left_inv := fun (q : D.P) => D.ext' rfl (by
          show ε (D.core.indexAt q.proj) q.proj * (ε (D.core.indexAt q.proj) q.proj * D.sp q) = D.sp q
          rw [← mul_assoc, (hsgn q).mul_self, one_mul])
        right_inv := fun q => (D.withH h' hc hl hcoc).ext' rfl (by
          show ε (D.core.indexAt q.proj) q.proj * (ε (D.core.indexAt q.proj) q.proj *
            (D.withH h' hc hl hcoc).sp q) = _
          rw [← mul_assoc, (hε _ _ (D.mem_baseSet_at' q.proj)).mul_self, one_mul])
        continuous_toFun := continuous_core_map D.core (D.withH h' hc hl hcoc).core
          (fun _ => rfl) (fun i y s => ε i y * s) hcf (D.signTo ε) (fun _ => rfl) hToC
        continuous_invFun := continuous_core_map (D.withH h' hc hl hcoc).core D.core
          (fun _ => rfl) (fun i y s => ε i y * s) hcf (D.signFrom ε) (fun _ => rfl) hFromC }
    proj_F := fun _ => rfl
    act_F := fun (q : D.P) t => (D.withH h' hc hl hcoc).ext' rfl (by
      show ε (D.core.indexAt q.proj) q.proj * (D.sp q * t) =
        ε (D.core.indexAt q.proj) q.proj * D.sp q * t
      rw [mul_assoc])
    Φ_F := fun (q : D.P) => by
      show actOFr' (D.σ (D.core.indexAt q.proj) q.proj)
          (spinToO77 (ε (D.core.indexAt q.proj) q.proj * D.sp q)) =
        actOFr' (D.σ (D.core.indexAt q.proj) q.proj) (spinToO77 (D.sp q))
      rw [map_mul, (isSign_iff _).mp (hsgn q), one_mul] }

end Iso

/-- **The sign-twisted spin structure is isomorphic to the original.** -/
def twistIso (ε : D.ι → Y13o X → Spin77) (hε : ∀ i, ∀ y ∈ D.V i, IsSign (ε i y))
    (hεc : ∀ i, ContinuousOn (ε i) (D.V i)) :
    SpinIso D.toStructure (D.twist ε hε hεc).toStructure :=
  D.isoOfCoboundary hε hεc fun _ _ _ _ => rfl

/-- Change of coordinate between two charts. -/
lemma localTriv_change (i j : D.ι) {q : D.P} (hi : (q.proj : Y13o X) ∈ D.V i)
    (hj : (q.proj : Y13o X) ∈ D.V j) :
    (D.core.localTriv j q).2 = (D.h i j q.proj)⁻¹ * (D.core.localTriv i q).2 := by
  set a := D.core.indexAt q.proj
  have ha : (q.proj : Y13o X) ∈ D.V a := D.mem_baseSet_at' q.proj
  show (D.h a j q.proj)⁻¹ * D.sp q = (D.h i j q.proj)⁻¹ * ((D.h a i q.proj)⁻¹ * D.sp q)
  rw [← D.cocycle a i j q.proj ⟨⟨ha, hi⟩, hj⟩, mul_inv_rev, mul_assoc]

/-- **Isomorphic spin structures on the same frames differ by a coboundary, and conversely.** -/
theorem iso_iff_coboundary (h' : D.ι → D.ι → Y13o X → Spin77)
    (hc : ∀ i j, ContinuousOn (h' i j) (D.V i ∩ D.V j))
    (hl : ∀ i j, ∀ y ∈ D.V i ∩ D.V j, D.σ j y = actOFr' (D.σ i y) (spinToO77 (h' i j y)))
    (hcoc : ∀ i j k, ∀ y ∈ D.V i ∩ D.V j ∩ D.V k, h' i j y * h' j k y = h' i k y) :
    Nonempty (SpinIso D.toStructure (D.withH h' hc hl hcoc).toStructure) ↔
      ∃ ε : D.ι → Y13o X → Spin77, (∀ i, ∀ y ∈ D.V i, IsSign (ε i y)) ∧
        (∀ i, ContinuousOn (ε i) (D.V i)) ∧
        ∀ i j, ∀ y ∈ D.V i ∩ D.V j, h' i j y = ε i y * D.h i j y * ε j y := by
  constructor
  · rintro ⟨I⟩
    set D' := D.withH h' hc hl hcoc
    -- work on the base `D.W`; both bundles have the same charts and cover
    let S := D.toStructure
    let S' := D'.toStructure
    have hprojI : ∀ p : D.P, ((S'.projS (I.F p) : D.W) : Y13o X) = (p.proj : Y13o X) := I.proj_F
    -- the chart-`i` section of `D`
    let s : D.ι → D.W → D.P := fun i y => S.sec i y
    have hsp : ∀ i (y : D.W), (y : Y13o X) ∈ D.V i → (s i y).proj = y := fun i y hy =>
      S.proj_sec i (y := y) hy
    have hs1 : ∀ i (y : D.W), (y : Y13o X) ∈ D.V i → (D.core.localTriv i (s i y)).2 = 1 :=
      fun i y hy => congrArg Prod.snd (S.e_sec i (y := y) hy)
    classical
    let ε : D.ι → Y13o X → Spin77 := fun i y =>
      if hy : y ∈ D.W then (D'.core.localTriv i (I.F (s i ⟨y, hy⟩))).2 else 1
    have hεv : ∀ i (y : D.W), ε i y = (D'.core.localTriv i (I.F (s i y))).2 := fun i y => dif_pos y.2
    have hprojF : ∀ i (y : D.W), (y : Y13o X) ∈ D.V i →
        (((I.F (s i y) : D'.P).proj : D.W) : Y13o X) = y := fun i y hy => by
      rw [show (((I.F (s i y) : D'.P).proj : D.W) : Y13o X) = (s i y).proj from hprojI _, hsp i y hy]
    have hε : ∀ i, ∀ y ∈ D.V i, IsSign (ε i y) := by
      intro i y hy
      have hW := D.V_sub i hy
      let y' : D.W := ⟨y, hW⟩
      have hp := hprojF i y' hy
      rw [isSign_iff, show ε i y = ε i (y' : Y13o X) from rfl, hεv]
      have h1 := D'.Φ_chart i (p := I.F (s i y')) (by rw [hp]; exact hy)
      rw [hp] at h1
      have h2 := D.Φ_chart i (p := s i y') (by rw [hsp i y' hy]; exact hy)
      rw [hsp i y' hy, hs1 i y' hy, map_one] at h2
      have h3 : D'.Φ (I.F (s i y')) = D.Φ (s i y') := I.Φ_F _
      rw [h1, h2] at h3
      exact actOFr'_cancel h3
    refine ⟨ε, hε, fun i => ?_, fun i j y hy => ?_⟩
    · intro y hy
      have hW := D.V_sub i hy
      have hO : IsOpen (Subtype.val ⁻¹' D.V i : Set D.W) :=
        (D.isOpen_V i).preimage continuous_subtype_val
      have h0 : ContinuousOn (D'.core.localTriv i) (D'.core.localTriv i).source :=
        (D'.core.localTriv i).toOpenPartialHomeomorph.continuousOn
      have hF : ContinuousOn (fun y : D.W => I.F (s i y)) (Subtype.val ⁻¹' D.V i) :=
        I.F.continuous.comp_continuousOn (S.continuousOn_sec i)
      have hC : ContinuousOn (fun y : D.W => (D'.core.localTriv i (I.F (s i y))).2)
          (Subtype.val ⁻¹' D.V i) :=
        continuous_snd.comp_continuousOn (ContinuousOn.comp h0 hF fun y hy => by
          show (((I.F (s i y) : D'.P).proj : D.W) : Y13o X) ∈ D.V i
          rw [hprojF i y hy]; exact hy)
      have hC2 : ContinuousOn (ε i ∘ Subtype.val : D.W → Spin77) (Subtype.val ⁻¹' D.V i) :=
        hC.congr fun y _ => hεv i y
      have hat := hC2.continuousAt (x := ⟨y, hW⟩) (hO.mem_nhds hy)
      exact ((D.isOpen_W.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hat).continuousWithinAt
    · have hW := D.V_sub i hy.1
      let y' : D.W := ⟨y, hW⟩
      have hyi : (y' : Y13o X) ∈ D.V i := hy.1
      have hyj : (y' : Y13o X) ∈ D.V j := hy.2
      have hpi := hsp i y' hyi
      have hc1 : (D.core.localTriv j (s i y')).2 = (D.h i j y)⁻¹ := by
        have := D.localTriv_change i j (q := s i y') (by rw [hpi]; exact hyi) (by rw [hpi]; exact hyj)
        rw [hpi, hs1 i y' hyi, mul_one] at this
        exact this
      have hs : s i y' = D.actS (s j y') (D.core.localTriv j (s i y')).2 := by
        have := S.sec_act_coord j (p := s i y') (by
          show ((s i y').proj : Y13o X) ∈ D.V j; rw [hpi]; exact hyj)
        rw [show S.projS (s i y') = y' from hpi] at this
        exact this.symm
      have hF : I.F (s i y') = D'.actS (I.F (s j y')) (D.core.localTriv j (s i y')).2 := by
        conv_lhs => rw [hs]
        exact I.act_F _ _
      have hjc : (D'.core.localTriv j (I.F (s i y'))).2 = ε j y * (D.h i j y)⁻¹ := by
        have h4 : (D'.core.localTriv j (D'.actS (I.F (s j y')) (D.core.localTriv j (s i y')).2)).2 =
            (D'.core.localTriv j (I.F (s j y'))).2 * (D.core.localTriv j (s i y')).2 :=
          congrArg Prod.snd (D'.localTriv_actS j _ _)
        rw [hF]
        refine h4.trans ?_
        rw [hc1]
        exact congrArg (· * (D.h i j y)⁻¹) (hεv j y').symm
      have hic : (D'.core.localTriv j (I.F (s i y'))).2 = (h' i j y)⁻¹ * ε i y := by
        have hp := hprojF i y' hyi
        have := D'.localTriv_change i j (q := I.F (s i y')) (by rw [hp]; exact hyi)
          (by rw [hp]; exact hyj)
        rw [show (((I.F (s i y') : D'.P).proj : D.W) : Y13o X) = y from hp] at this
        rw [show ε i y = ε i (y' : Y13o X) from rfl, hεv]
        exact this
      have e := hjc.symm.trans hic
      have e2 : h' i j y * ε j y = ε i y * D.h i j y := by
        have e3 : h' i j y * (ε j y * (D.h i j y)⁻¹) = ε i y := by rw [e, mul_inv_cancel_left]
        rw [← e3]; group
      calc h' i j y = h' i j y * (ε j y * ε j y) := by rw [(hε j y hy.2).mul_self, mul_one]
        _ = (h' i j y * ε j y) * ε j y := by group
        _ = _ := by rw [e2]
  · rintro ⟨ε, hε, hεc, hrel⟩
    exact ⟨D.isoOfCoboundary hε hεc hrel⟩

end SpinLiftData

end

end GU.Library
