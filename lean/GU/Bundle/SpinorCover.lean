/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TimeCoverSpin
import Mathlib.Topology.VectorBundle.Constructions
import GU.Bundle.LocalPH
import GU.Spinor.Dirac

/-!
# The spinor bundle on the cover over `ℝ⁴`

`coverSpin` is a `Spin⁺(7,7)` structure of the chimeric bundle over the whole double cover
`Ytilde ℝ⁴` (its total space is `Ytilde ℝ⁴ × Spin(7,7)`, with a two-to-one equivariant map onto the
`SO₀`-reduction of the frames of `C`). Here, with the explicit Dirac representation `ρ_D`:

* **`SpinorBundle`**: the associated bundle `P̃ ×_{ρ_D} ℂ^{64,64}`, defined as the quotient of
  `P̃ × ℂ¹²⁸` by `[p·g, v] = [p, ρ_D(g) v]`, with the quotient topology, and its projection
  `spinorProj` to the cover.
* **`spinorTriv`**: a homeomorphism onto `Ytilde ℝ⁴ × ℂ¹²⁸` over the cover; **`toTrivial`**: the same
  onto Mathlib's trivial vector bundle `Bundle.Trivial (Ytilde ℝ⁴) ℂ¹²⁸` (`toTrivial_proj`). Each
  `p ∈ P̃` gives a bijection `v ↦ [p, v]` onto the fibre (`exists_unique_mk`), linear in the
  trivialisation (`spinorMk_linear`, it is `ρ_D(p₂)`), and a change of frame acts by the linear map
  `ρ_D(g)` (`spinorMk_act`). The fibre's `ℂ`-structure is the one transported along `spinorTriv`; no
  `Module` instance on the quotient fibres is declared.
* **The `U(64,64)` structure**: the form `⟨e, e'⟩ = vᴴ C w` in the trivialisation is Hermitian
  (`spinorForm_conj`) and nondegenerate (`spinorForm_nondegenerate`), and every frame `[p, ·]` is an
  isometry from `(ℂ¹²⁸, C)` (`spinorForm_mk`: independent of `p`, because `ρ_D` lands in the unitary
  group of `C`). `C` has signature `(64,64)` (`UC_equiv_U6464`).
* **`coverPH`**: the draft's `P_H = P̃ ×_{ρ_D} U(64,64)` (3.32) as a principal `U(64,64)`-bundle (set
  level, the existing `Extension` construction, the same term as `localPH` over another base). Its `P̃`
  is `coverSpin`'s total space with `coverSpin`'s action (`coverPH_spin`, `coverSpin_act_eq`, both by
  `rfl`), whose map `Φ` is two-to-one onto the `SO₀`-frames of `C` (`range_coverSpin`). No property of
  `coverPH` proved here uses `Φ`.

**Not built**: the topology or smoothness of `P_H` (it is set level); the relation of `SpinorBundle`
to the bundle associated with `P_H` (the draft's (3.36)); smoothness of the spinor bundle; a `Module`
instance on its fibres; the Weyl splitting on the bundle; functoriality in the spin structure (this is
the one `coverSpin`); connections and a Dirac operator; anything over `Y13` itself (only over the
cover); any `X` other than `ℝ⁴`. The reading of the draft's "double cover" as the cover's `Spin⁺(7,7)` structure is
ours.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ComplexOrder

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The spinor space `ℂ¹²⁸ = ℂ^{64,64}`. -/
abbrev SpC := Idx → ℂ

/-- The Dirac matrices `ρ_D(g)`. -/
def rhoM (g : Spin77) : Matrix Idx Idx ℂ := (rhoD g).1

lemma rhoM_mul (g h : Spin77) : rhoM (g * h) = rhoM g * rhoM h := by
  rw [rhoM, map_mul]; rfl

lemma rhoM_one : rhoM 1 = 1 := by rw [rhoM, map_one]; rfl

lemma rhoM_unitary (g : Spin77) : (rhoM g)ᴴ * Cc * rhoM g = Cc := (rhoD g).2

lemma rhoM_inv_mul (g : Spin77) : rhoM g⁻¹ * rhoM g = 1 := by rw [← rhoM_mul, inv_mul_cancel, rhoM_one]

lemma continuous_rhoM : Continuous rhoM := by
  have h1 : Continuous fun g : Spin77 => cliffordRep (g : Cl77) :=
    continuous_induced_dom.comp continuous_subtype_val
  have h2 : Continuous toC := continuous_id.matrix_map Complex.continuous_ofReal
  exact h2.comp h1

/-- The total space of `coverSpin` (`coverSpin_P`), with its right action (`coverSpin_actS`). -/
abbrev PS := Ytilde R4 × Spin77

/-- Right multiplication on the `Spin(7,7)` factor. -/
def actP (p : PS) (g : Spin77) : PS := (p.1, p.2 * g)

lemma coverSpin_P : coverSpin.P = PS := rfl

lemma coverSpin_actS (p : PS) (g : Spin77) : coverSpin.actS p g = actP p g := rfl

lemma coverSpin_projS (p : PS) : coverSpin.projS p = p.1 := rfl

lemma actP_one (p : PS) : actP p 1 = p := by simp [actP]

lemma actP_mul (p : PS) (g h : Spin77) : actP (actP p g) h = actP p (g * h) := by simp [actP, mul_assoc]

/-- `[p·g, v] = [p, ρ_D(g) v]`. -/
def spinorSetoid : Setoid (PS × SpC) where
  r a b := ∃ g : Spin77, b.1 = actP a.1 g ∧ a.2 = rhoM g *ᵥ b.2
  iseqv := by
    refine ⟨fun a => ⟨1, (actP_one a.1).symm, by rw [rhoM_one, one_mulVec]⟩, ?_, ?_⟩
    · rintro a b ⟨g, h1, h2⟩
      refine ⟨g⁻¹, ?_, ?_⟩
      · rw [h1, actP_mul, mul_inv_cancel, actP_one]
      · rw [h2, mulVec_mulVec, rhoM_inv_mul, one_mulVec]
    · rintro a b c ⟨g, h1, h2⟩ ⟨g', h1', h2'⟩
      refine ⟨g * g', ?_, ?_⟩
      · rw [h1', h1, actP_mul]
      · rw [h2, h2', mulVec_mulVec, ← rhoM_mul]

/-- **The spinor bundle** `P̃ ×_{ρ_D} ℂ^{64,64}` over the cover of `Y13(ℝ⁴)`. -/
def SpinorBundle : Type := Quotient spinorSetoid

instance : TopologicalSpace SpinorBundle := instTopologicalSpaceQuotient

/-- The class `[p, v]`. -/
def spinorMk (p : PS) (v : SpC) : SpinorBundle := Quotient.mk spinorSetoid (p, v)

lemma spinorMk_act (p : PS) (g : Spin77) (v : SpC) :
    spinorMk (actP p g) v = spinorMk p (rhoM g *ᵥ v) :=
  (Quotient.sound (s := spinorSetoid) (a := (p, rhoM g *ᵥ v)) (b := (actP p g, v))
    ⟨g, rfl, rfl⟩).symm

/-- The global frame in coordinates: `[(q, s), v] ↦ (q, ρ_D(s) v)`. -/
def trivRaw (a : PS × SpC) : Ytilde R4 × SpC := (a.1.1, rhoM a.1.2 *ᵥ a.2)

lemma trivRaw_eq {a b : PS × SpC} (h : spinorSetoid a b) : trivRaw a = trivRaw b := by
  obtain ⟨g, h1, h2⟩ := h
  obtain ⟨⟨q, s⟩, v⟩ := a
  obtain ⟨⟨q', s'⟩, w⟩ := b
  simp only at h1 h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
  simp only [trivRaw, h2, mulVec_mulVec, ← rhoM_mul]

/-- The trivialisation of the spinor bundle. -/
def spinorTrivFun : SpinorBundle → Ytilde R4 × SpC := Quotient.lift trivRaw fun _ _ h => trivRaw_eq h

/-- **The spinor bundle is homeomorphic to the trivial bundle** `Ytilde ℝ⁴ × ℂ¹²⁸`. -/
def spinorTriv : SpinorBundle ≃ₜ Ytilde R4 × SpC where
  toFun := spinorTrivFun
  invFun z := spinorMk (z.1, 1) z.2
  left_inv e := by
    induction e using Quotient.inductionOn with
    | h a =>
      obtain ⟨⟨q, s⟩, v⟩ := a
      show spinorMk (q, 1) (rhoM s *ᵥ v) = spinorMk (q, s) v
      exact (Quotient.sound ⟨s, by show (q, s) = (q, 1 * s); rw [one_mul], rfl⟩)
  right_inv z := by
    show (z.1, rhoM 1 *ᵥ z.2) = z
    rw [rhoM_one, one_mulVec]
  continuous_toFun := by
    refine Continuous.quotient_lift ?_ _
    exact (continuous_fst.comp continuous_fst).prodMk
      (((continuous_rhoM.comp (continuous_snd.comp continuous_fst))).matrix_mulVec continuous_snd)
  continuous_invFun := by
    refine continuous_quot_mk.comp ?_
    exact (continuous_fst.prodMk continuous_const).prodMk continuous_snd

/-- The projection to the cover. -/
def spinorProj (e : SpinorBundle) : Ytilde R4 := (spinorTriv e).1

lemma spinorTriv_mk (p : PS) (v : SpC) :
    spinorTriv (spinorMk p v) = (p.1, rhoM p.2 *ᵥ v) := rfl

/-- The trivialisation lies over the identity of the cover. -/
lemma spinorTriv_fst (e : SpinorBundle) : (spinorTriv e).1 = spinorProj e := rfl

lemma spinorProj_mk (p : PS) (v : SpC) : spinorProj (spinorMk p v) = p.1 := rfl

lemma continuous_spinorProj : Continuous spinorProj := continuous_fst.comp spinorTriv.continuous

/-- Every element of the fibre over `projS p` is `[p, v]` for a unique `v`. -/
lemma exists_unique_mk (p : PS) (e : SpinorBundle) (he : spinorProj e = p.1) :
    ∃! v, spinorMk p v = e := by
  refine ⟨rhoM p.2⁻¹ *ᵥ (spinorTriv e).2, ?_, ?_⟩
  · apply spinorTriv.injective
    rw [spinorTriv_mk, mulVec_mulVec, ← rhoM_mul, mul_inv_cancel, rhoM_one, one_mulVec]
    exact Prod.ext he.symm rfl
  · intro w hw
    rw [← hw, spinorTriv_mk, mulVec_mulVec, rhoM_inv_mul, one_mulVec]

/-- **Over the base, the spinor bundle is Mathlib's trivial vector bundle** `Ytilde ℝ⁴ × ℂ¹²⁸`
(`Bundle.Trivial`, a `VectorBundle ℂ` instance in Mathlib). -/
def toTrivial : SpinorBundle ≃ₜ TotalSpace SpC (Bundle.Trivial (Ytilde R4) SpC) :=
  spinorTriv.trans (Bundle.Trivial.homeomorphProd (Ytilde R4) SpC).symm

lemma toTrivial_proj (e : SpinorBundle) : (toTrivial e).proj = spinorProj e := rfl

/-- **The frames are linear**: in the trivialisation, `v ↦ [p, v]` is the linear map `ρ_D(p₂)`. -/
lemma spinorMk_linear (p : PS) (a : ℂ) (v w : SpC) :
    (spinorTriv (spinorMk p (a • v + w))).2 =
      a • (spinorTriv (spinorMk p v)).2 + (spinorTriv (spinorMk p w)).2 := by
  simp only [spinorTriv_mk, mulVec_add, mulVec_smul]

/-! ### The `U(64,64)` structure -/

/-- The Hermitian form in the trivialisation: `⟨e, e'⟩ = vᴴ C w`. -/
def spinorForm (e e' : SpinorBundle) : ℂ := star (spinorTriv e).2 ⬝ᵥ (Cc *ᵥ (spinorTriv e').2)

/-- **The form does not depend on the frame**: in the frame `p`, it is `vᴴ C w`. -/
theorem spinorForm_mk (p : PS) (v w : SpC) :
    spinorForm (spinorMk p v) (spinorMk p w) = star v ⬝ᵥ (Cc *ᵥ w) := by
  rw [spinorForm, spinorTriv_mk, spinorTriv_mk]
  simp only
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec,
    rhoM_unitary p.2]

/-- **The form is Hermitian.** -/
theorem spinorForm_conj (e e' : SpinorBundle) : spinorForm e e' = star (spinorForm e' e) := by
  rw [spinorForm, spinorForm, ← star_dotProduct_star, star_star, star_mulVec, Cc_conjTranspose,
    dotProduct_mulVec, dotProduct_comm]

/-- **The form is nondegenerate.** -/
theorem spinorForm_nondegenerate (p : PS) (v : SpC)
    (h : ∀ w, spinorForm (spinorMk p v) (spinorMk p w) = 0) : v = 0 := by
  have h0 := h (Cc *ᵥ v)
  rw [spinorForm_mk, mulVec_mulVec, Cc_mul_Cc, one_mulVec] at h0
  exact dotProduct_star_self_eq_zero.mp h0

/-! ### `P_H` over the cover -/

/-- `coverSpin`'s total space and action are those of the trivial `Spin(7,7)`-bundle over the
cover. -/
lemma coverSpin_act_eq (p : PS) (g : Spin77) :
    coverSpin.actS p g = (letI := spinAct (Ytilde R4); MulOpposite.op g • p) := rfl

/-- **The draft's `P_H` (3.32) over the cover of `Y13(ℝ⁴)`**, on the total space of `coverSpin`: a
principal `U(64,64)`-bundle (set level). -/
def coverPH : PrincipalBundle U6464 (PH (trivialSpinOver (Ytilde R4)) diracRep) (Ytilde R4) :=
  physicalBundle _

lemma coverPH_spin : (trivialSpinOver (Ytilde R4)).Ptilde = coverSpin.P := rfl

/-- Non-vacuity: the base is nonempty. -/
lemma nonempty_spinorBundle : Nonempty SpinorBundle :=
  ⟨spinorMk (Classical.choice (nonempty_tilde (0 : R4)), 1) 0⟩

end

end GU.Library
