import GU.Bundle.SpinGeneric
import GU.Bundle.TimeCoverSpin

/-!
# Phase 6, item 3: the API of spin structures on the cover

* **`coverFS X`**: the pulled-back frames `OFrT X → Ytilde X` form a frame system, so the generic theory
  of `SpinGeneric.lean` applies.
* **`CoverSpin.toGen`**, **`ofGen`**: a `CoverSpin` is the same as a generic spin structure over all of
  `Ytilde X` (`W = univ`), with the same `P`, action and map `Φ` (`toGen_P`, `toGen_actS`, `toGen_Φ`);
  `CoverSpin.isoToData` is the isomorphism with the structure glued from its cocycle.
* **`CoverSpin.Φ_eq_iff`**: `Φ` is exactly two-to-one, **`CoverSpin.isCoveringMap_Φ`**: a covering map
  onto its image, and **`coverSpin_iff_data`**: a `CoverSpin` with image `Q` exists iff cocycle lifts over
  all of the cover with image `Q` exist. Instance: `coverSpin` over `ℝ⁴` (`coverSpin_Φ_eq_iff_actS`,
  `isCoveringMap_coverSpin`, `exists_data_cover_R4`).
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### The frame system on the cover -/

lemma actT_one (z : OFrT X) : actT z 1 = z := by
  apply Subtype.ext
  show (z.1.1, actOFr' z.1.2 1) = z.1
  rw [actOFr'_one]

lemma continuous_actT : Continuous fun zg : OFrT X × O77 => actT zg.1 zg.2 := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
    (continuous_actOFr'.comp ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd))

open Classical in
/-- A section of the pulled-back frames from a section of `OFr`. -/
def secT (σ' : (ofrFS X).B → (ofrFS X).Fr) (p : Ytilde X) : OFrT X :=
  ⟨(p, if (ofrFS X).proj (σ' (piT p)) = piT p then σ' (piT p)
    else ((ofrFS X).proj_surj (piT p)).choose), by
    show piT p = (ofrFS X).proj (if (ofrFS X).proj (σ' (piT p)) = piT p then σ' (piT p)
      else ((ofrFS X).proj_surj (piT p)).choose)
    by_cases h : (ofrFS X).proj (σ' (piT p)) = piT p
    · rw [if_pos h]; exact h.symm
    · rw [if_neg h]; exact ((ofrFS X).proj_surj (piT p)).choose_spec.symm⟩

lemma secT_fst (σ' : (ofrFS X).B → (ofrFS X).Fr) (p : Ytilde X) : (secT σ' p).1.1 = p := rfl

lemma secT_snd {σ' : (ofrFS X).B → (ofrFS X).Fr} {p : Ytilde X}
    (h : (ofrFS X).proj (σ' (piT p)) = piT p) : (secT σ' p).1.2 = σ' (piT p) := by
  classical
  show (if (ofrFS X).proj (σ' (piT p)) = piT p then σ' (piT p) else _) = _
  rw [if_pos h]

lemma continuous_OFrT_snd : Continuous fun z : OFrT X => z.1.2 := continuous_snd.comp continuous_subtype_val

/-- **The pulled-back frames form a frame system over the cover.** -/
def coverFS (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : FrameSys where
  B := Ytilde X
  Fr := OFrT X
  proj z := z.1.1
  act := actT
  act_mul := actT_mul
  act_one := actT_one
  proj_act _ _ := rfl
  cancel {z} {g} {g'} h := actOFr'_cancel (congrArg (fun w : OFrT X => w.1.2) h)
  continuous_act := continuous_actT
  continuous_proj := continuous_fst.comp continuous_subtype_val
  proj_surj p := by
    obtain ⟨q, hq⟩ := (ofrFS X).proj_surj (piT p)
    exact ⟨⟨(p, q), hq.symm⟩, rfl⟩
  exists_act z w h := by
    have h' : projOFr z.1.2 = projOFr w.1.2 := by
      rw [← z.2, ← w.2]; exact congrArg piT h
    obtain ⟨g, hg⟩ := exists_act_eq z.1.2 w.1.2 h'
    refine ⟨g, Subtype.ext ?_⟩
    show (z.1.1, actOFr' z.1.2 g) = w.1
    rw [hg, show z.1.1 = w.1.1 from h]
  locTriv b := by
    obtain ⟨V', hV', hb, σ', τ', hτ, hrec⟩ := (ofrFS X).locTriv (piT b)
    refine ⟨piT ⁻¹' V', hV'.preimage continuous_piT, hb, secT σ', fun z => τ' z.1.2, ?_, ?_⟩
    · refine hτ.comp continuous_OFrT_snd.continuousOn fun z hz => ?_
      show projOFr z.1.2 ∈ V'
      rw [← z.2]; exact hz
    · intro z hz
      have hz' : projOFr z.1.2 ∈ V' := by rw [← z.2]; exact hz
      have e := hrec z.1.2 hz'
      have h0 := congrArg projOFr e
      change projOFr (σ' (projOFr z.1.2)) = projOFr z.1.2 at h0
      have hσ : projOFr (σ' (piT z.1.1)) = piT z.1.1 := by
        rw [z.2]; exact h0
      apply Subtype.ext
      refine Prod.ext rfl ?_
      show actOFr' (secT σ' z.1.1).1.2 (τ' z.1.2) = z.1.2
      rw [secT_snd hσ]
      show actOFr' (σ' (piT z.1.1)) (τ' z.1.2) = z.1.2
      rw [z.2]; exact e

/-! ### Changing the base of a trivialisation along a homeomorphism -/

/-- A trivialisation, with its base moved along a homeomorphism. -/
def trivMap {B₁ B₂ P F : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace P]
    [TopologicalSpace F] {f : P → B₁} (φ : B₁ ≃ₜ B₂) (e : Trivialization F f) :
    Trivialization F (fun p => φ (f p)) where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.trans
    (φ.prodCongr (Homeomorph.refl F)).toOpenPartialHomeomorph
  baseSet := φ.symm ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage φ.symm.continuous
  source_eq := by
    ext p
    simp [e.source_eq]
  target_eq := by
    ext ⟨b, x⟩
    simp [e.target_eq]
  proj_toFun p hp := by
    show φ (e p).1 = φ (f p)
    exact congrArg φ (e.proj_toFun p hp.1)

lemma trivMap_apply {B₁ B₂ P F : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace P]
    [TopologicalSpace F] {f : P → B₁} (φ : B₁ ≃ₜ B₂) (e : Trivialization F f) (p : P) :
    trivMap φ e p = (φ (e p).1, (e p).2) := rfl

lemma mem_trivMap_source {B₁ B₂ P F : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂]
    [TopologicalSpace P] [TopologicalSpace F] {f : P → B₁} (φ : B₁ ≃ₜ B₂) (e : Trivialization F f)
    {p : P} (hp : p ∈ (trivMap φ e).source) : p ∈ e.source := hp.1

lemma trivMap_act {B₁ B₂ P F : Type*} [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace P]
    [TopologicalSpace F] [Mul F] {f : P → B₁} (φ : B₁ ≃ₜ B₂) (e : Trivialization F f) {p q : P} {t : F}
    (h : e q = ((e p).1, (e p).2 * t)) : trivMap φ e q = ((trivMap φ e p).1, (trivMap φ e p).2 * t) := by
  rw [trivMap_apply, trivMap_apply, h]

/-! ### `CoverSpin` as a generic spin structure over all of the cover -/

attribute [local instance] CoverSpin.top

namespace CoverSpin

variable (S : CoverSpin X)

/-- **A `CoverSpin` is a generic spin structure with base all of the cover.** -/
def toGen : Gen.SpinStructure (coverFS X) where
  W := Set.univ
  isOpen_W := isOpen_univ
  P := S.P
  top := S.top
  projS p := ⟨S.projS p, Set.mem_univ _⟩
  actS := S.actS
  Φ := S.Φ
  act_one := S.act_one
  act_mul := S.act_mul
  proj_act p t := Subtype.ext (S.proj_act p t)
  continuous_act := S.continuous_act
  ι := S.ι
  V i := (S.e i).baseSet
  V_sub _ := Set.subset_univ _
  cover y _ := S.cover y
  e i := trivMap (Homeomorph.Set.univ (Ytilde X)).symm (S.e i)
  baseSet_e _ := rfl
  e_act i p hp t := trivMap_act _ _ (S.e_act i p (mem_trivMap_source _ _ hp) t)
  continuous_Φ := S.continuous_Φ
  proj_Φ := S.proj_Φ
  Φ_act := S.Φ_act

@[simp] lemma toGen_P : S.toGen.P = S.P := rfl
@[simp] lemma toGen_actS : S.toGen.actS = S.actS := rfl
@[simp] lemma toGen_Φ : S.toGen.Φ = S.Φ := rfl

/-- Every spin structure on the cover is isomorphic to the one glued from its own cocycle. -/
def isoToData : Gen.SpinIso S.toGen.toData.toStructure S.toGen := S.toGen.isoToData

/-- **The map to the frames is exactly two-to-one.** -/
theorem Φ_eq_iff (p q : S.P) : S.Φ p = S.Φ q ↔ q = p ∨ q = S.actS p negOne :=
  Gen.SpinStructure.Φ_eq_iff S.toGen p q

/-- **The map to the frames is a covering map onto its image.** -/
theorem isCoveringMap_Φ : IsCoveringMap (Set.rangeFactorization S.Φ) :=
  Gen.SpinStructure.isCoveringMap_Φ S.toGen

end CoverSpin

/-- **A generic spin structure over all of the cover is a `CoverSpin`.** -/
def ofGen (S : Gen.SpinStructure (coverFS X)) (hW : S.W = Set.univ) : CoverSpin X where
  P := S.P
  top := S.top
  projS p := ((Homeomorph.setCongr hW).trans (Homeomorph.Set.univ (Ytilde X))) (S.projS p)
  actS := S.actS
  Φ := S.Φ
  act_one := S.act_one
  act_mul := S.act_mul
  proj_act p t := congrArg ((Homeomorph.setCongr hW).trans (Homeomorph.Set.univ (Ytilde X))) (S.proj_act p t)
  continuous_act := S.continuous_act
  ι := S.ι
  e i := trivMap ((Homeomorph.setCongr hW).trans (Homeomorph.Set.univ (Ytilde X))) (S.e i)
  cover b := by
    obtain ⟨i, hi⟩ := S.cover b (by rw [hW]; exact Set.mem_univ _)
    refine ⟨i, ?_⟩
    show _ ∈ (S.e i).baseSet
    rw [S.baseSet_e]
    exact hi
  e_act i p hp t := trivMap_act _ _ (S.e_act i p (mem_trivMap_source _ _ hp) t)
  continuous_Φ := S.continuous_Φ
  proj_Φ := S.proj_Φ
  Φ_act := S.Φ_act

/-- **A spin structure on the cover with image `Q` exists iff cocycle lifts over all of the cover with
image `Q` exist.** -/
theorem coverSpin_iff_data (Q : Set (OFrT X)) :
    (∃ S : CoverSpin X, Set.range S.Φ = Q) ↔
      ∃ D : Gen.SpinLiftData (coverFS X), D.W = Set.univ ∧ Set.range D.Φ = Q := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.toGen.toData, rfl, S.toGen.range_Φ_eq.symm.trans hS⟩
  · rintro ⟨D, hW, hD⟩
    exact ⟨ofGen D.toStructure hW, hD⟩

/-! ### The instance over `ℝ⁴` -/

/-- `CoverSpin.Φ_eq_iff` for `coverSpin` (in the form with the action; `coverSpin_Φ_eq_iff` is the
coordinate form). -/
theorem coverSpin_Φ_eq_iff_actS (p q : coverSpin.P) :
    coverSpin.Φ p = coverSpin.Φ q ↔ q = p ∨ q = coverSpin.actS p negOne :=
  CoverSpin.Φ_eq_iff coverSpin p q

/-- `CoverSpin.isCoveringMap_Φ` for `coverSpin`. -/
theorem isCoveringMap_coverSpin : IsCoveringMap (Set.rangeFactorization coverSpin.Φ) :=
  CoverSpin.isCoveringMap_Φ coverSpin

/-- **Cocycle lifts over all of the cover of `Y13(ℝ⁴)` exist, with image the reduction `QT`.** -/
theorem exists_data_cover_R4 :
    ∃ D : Gen.SpinLiftData (coverFS R4), D.W = Set.univ ∧ Set.range D.Φ = QT :=
  (coverSpin_iff_data QT).mp ⟨coverSpin, range_coverSpin⟩
end

end GU.Library
