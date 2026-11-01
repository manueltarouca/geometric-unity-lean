/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SpinorCover

/-!
# `P_H` on the cover over `ℝ⁴` as a topological bundle, and the draft's (3.36)

`coverPH` (`SpinorCover.lean`) is the draft's `P_H = P̃ ×_{ρ_D} U(64,64)` (3.32) on the total space of
`coverSpin`, at set level. Here:

* **`PHT`** carries the quotient topology. **`phTriv`**: a homeomorphism `PHT ≃ₜ Ytilde ℝ⁴ × U(64,64)`
  over the cover (`phTriv_fst`), equivariant for the right `U(64,64)` action (`phTriv_smul`); the
  projection and the action are continuous (`continuous_phProj`, `continuous_phAct`). So `P_H` is a
  topological principal `U(64,64)`-bundle over the cover, globally trivial (`coverPH_topological`).
  `U(64,64)` has the subspace topology of the complex matrices, with continuous multiplication.
* **(3.36)**: the bundle associated with `P_H` through the defining representation of `U(64,64)` on
  `ℂ^{64,64}`, **`AssocPH = P_H ×_{U(64,64)} ℂ^{64,64}`**, is homeomorphic over the cover to the spinor
  bundle `P̃ ×_{ρ_D} ℂ^{64,64}` (**`spinorIso`**). The map is the natural one,
  `[[p, k], v] ↦ [p, Q(k v)]` with `Q` the fixed change of basis between the draft's spinor basis and
  the standard `U(64,64)` basis (`spinorIso_mk`), and it carries the standard form `vᴴ J w` of
  `ℂ^{64,64}` to the spinor form (`spinorForm_spinorIso`).

The draft writes `P_H ×_{ϱ_D} ℂ^{64,64}`; the subscript on `P_H` is read as the defining
representation of `U(64,64)`. This reading is ours.

Not built: smoothness; a `Module` instance on the fibres of `AssocPH` (linearity is in the
trivialisations, `spinorIso_linear`); a link to Mathlib's `FiberBundle` API for `P_H`; the bundles
`ad`/`Ad` of (3.34)–(3.35); the draft's further structure on `P_H` (connections, the gauge group, the
action); anything over `Y13` itself or `X ≠ ℝ⁴`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor TopologicalSpace Topology MulOpposite

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### The standard `ℂ^{64,64}` and the change of basis -/

/-- Indices of the standard `ℂ^{64,64}`. -/
abbrev E64 := Fin 64 ⊕ Fin 64

/-- The standard `ℂ^{64,64}`. -/
abbrev V64 := E64 → ℂ

/-- The complexified change of basis `P` (`Basis.lean`). -/
def Pc : Matrix Idx Idx ℂ := toC P

lemma Pc_unitary : Pcᴴ * Pc = 1 := PcHPc

lemma Pc_unitary' : Pc * Pcᴴ = 1 := mul_eq_one_comm.mp PcHPc

set_option maxRecDepth 100000 in
lemma UC_equiv_val (A : UC) :
    ((UC_equiv_U6464 A : U6464) : Matrix E64 E64 ℂ) = (Pcᴴ * A.1 * Pc).submatrix splitIdx.symm splitIdx.symm :=
  rfl

/-- From the standard basis to the draft's spinor basis. -/
def Qv (v : V64) : SpC := Pc *ᵥ (v ∘ splitIdx)

/-- Its inverse. -/
def Qinv (w : SpC) : V64 := (Pcᴴ *ᵥ w) ∘ splitIdx.symm

lemma Qinv_Qv (v : V64) : Qinv (Qv v) = v := by
  funext i
  simp [Qinv, Qv, mulVec_mulVec, Pc_unitary]

lemma Qv_Qinv (w : SpC) : Qv (Qinv w) = w := by
  unfold Qv Qinv
  have : (Pcᴴ *ᵥ w) ∘ splitIdx.symm ∘ splitIdx = Pcᴴ *ᵥ w := by funext a; simp
  rw [Function.comp_assoc, this, mulVec_mulVec, Pc_unitary', one_mulVec]

lemma continuous_Qv : Continuous Qv :=
  (continuous_const.matrix_mulVec (continuous_pi fun a => continuous_apply (splitIdx a)))

lemma continuous_Qinv : Continuous Qinv :=
  continuous_pi fun _ => (continuous_apply _).comp (continuous_const.matrix_mulVec continuous_id)

/-- `Q` as a homeomorphism. -/
def Qhomeo : V64 ≃ₜ SpC where
  toFun := Qv
  invFun := Qinv
  left_inv := Qinv_Qv
  right_inv := Qv_Qinv
  continuous_toFun := continuous_Qv
  continuous_invFun := continuous_Qinv

lemma Qv_add_smul (a : ℂ) (v w : V64) : Qv (a • v + w) = a • Qv v + Qv w := by
  simp only [Qv]
  rw [show (a • v + w) ∘ splitIdx = a • (v ∘ splitIdx) + w ∘ splitIdx from rfl, mulVec_add, mulVec_smul]

/-- `Q` intertwines `U(64,64)` with the draft's `U(C)`. -/
lemma Qv_intertwine (A : UC) (v : V64) :
    Qv (((UC_equiv_U6464 A : U6464) : Matrix E64 E64 ℂ) *ᵥ v) = A.1 *ᵥ Qv v := by
  rw [UC_equiv_val, Qv, Qv, submatrix_mulVec_equiv, Equiv.symm_symm]
  have hc : ((Pcᴴ * A.1 * Pc) *ᵥ (v ∘ splitIdx)) ∘ splitIdx.symm ∘ splitIdx =
      (Pcᴴ * A.1 * Pc) *ᵥ (v ∘ splitIdx) := by funext a; simp
  rw [Function.comp_assoc, hc, mulVec_mulVec, mulVec_mulVec]
  congr 1
  simp only [← Matrix.mul_assoc, Pc_unitary', Matrix.one_mul]

/-- `Q` carries the standard form `vᴴ J w` to the spinor form `vᴴ C w`. -/
lemma Qv_form (v w : V64) :
    star (Qv v) ⬝ᵥ (Cc *ᵥ Qv w) = star v ⬝ᵥ (Jpq (Fin 64) (Fin 64) *ᵥ w) := by
  have hJ : Jpq (Fin 64) (Fin 64) = (Pcᴴ * Cc * Pc).submatrix splitIdx.symm splitIdx.symm := by
    rw [show Pcᴴ * Cc * Pc = toC D from PcHCPc, ← reindex_D]; rfl
  rw [hJ, submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm, Qv, Qv, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rfl

/-! ### `P_H` with its topology -/

/-- `U(64,64)` is a topological group: the inverse is `A ↦ J Aᴴ J`. -/
instance : IsTopologicalGroup U6464 where
  continuous_inv := ((continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
    continuous_const).subtype_mk _

/-- The right action on `P̃ = Ytilde ℝ⁴ × Spin(7,7)` (that of `trivialSpinOver`, i.e. of `coverSpin`). -/
local instance psAct : MulAction Spin77ᵐᵒᵖ PS := spinAct (Ytilde R4)

instance : TopologicalSpace (trivialSpinOver (Ytilde R4)).Ptilde := inferInstanceAs (TopologicalSpace PS)

/-- `P_H` on the cover. -/
abbrev PHT : Type := PH (trivialSpinOver (Ytilde R4)) diracRep

instance : TopologicalSpace PHT := instTopologicalSpaceQuotient

/-- `ρ_D` into the standard `U(64,64)`. -/
def rhoU (g : Spin77) : U6464 := diracRep.ρ g

set_option maxRecDepth 100000 in
lemma rhoU_val (g : Spin77) :
    ((rhoU g : U6464) : Matrix E64 E64 ℂ) = (Pcᴴ * rhoM g * Pc).submatrix splitIdx.symm splitIdx.symm := rfl

lemma rhoU_mul (g h : Spin77) : rhoU (g * h) = rhoU g * rhoU h := map_mul _ _ _

lemma continuous_rhoU : Continuous rhoU := by
  have h : Continuous fun g : Spin77 => (Pcᴴ * rhoM g * Pc).submatrix splitIdx.symm splitIdx.symm :=
    ((continuous_const.matrix_mul continuous_rhoM).matrix_mul continuous_const).matrix_submatrix _ _
  exact h.subtype_mk _

/-- The class `[p, k]`. -/
def phMk (p : PS) (k : U6464) : PHT := Extension.mk diracRep.ρ _ p k

lemma phMk_act (p : PS) (g : Spin77) (k : U6464) : phMk (actP p g) k = phMk p (rhoU g * k) :=
  ((Extension.mk_eq_mk diracRep.ρ _).mpr ⟨g, rfl, rfl⟩).symm

/-- The global trivialisation, on representatives. -/
def phRaw (a : PS × U6464) : Ytilde R4 × U6464 := (a.1.1, rhoU a.1.2 * a.2)

lemma phRaw_eq {a b : PS × U6464} (h : (Extension.setoid diracRep.ρ _) a b) : phRaw a = phRaw b := by
  obtain ⟨g, h1, h2⟩ := h
  obtain ⟨⟨q, s⟩, k⟩ := a
  obtain ⟨⟨q', s'⟩, k'⟩ := b
  have h1' : ((q', s') : PS) = (q, s * g) := h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1'
  simp only [phRaw]
  rw [show k = diracRep.ρ g * k' from h2, ← mul_assoc, rhoU_mul]
  rfl

/-- **The global trivialisation of `P_H`.** -/
def phTriv : PHT ≃ₜ Ytilde R4 × U6464 where
  toFun := Quotient.lift phRaw fun _ _ h => phRaw_eq h
  invFun z := phMk (z.1, 1) z.2
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a =>
      obtain ⟨⟨q, s⟩, k⟩ := a
      show phMk (q, 1) (rhoU s * k) = phMk (q, s) k
      rw [← phMk_act]
      show phMk (q, 1 * s) k = _
      rw [one_mul]
  right_inv z := by
    show (z.1, rhoU 1 * z.2) = z
    rw [show rhoU 1 = 1 from map_one _, one_mul]
  continuous_toFun := by
    refine Continuous.quotient_lift ?_ _
    exact (continuous_fst.comp continuous_fst).prodMk
      ((continuous_rhoU.comp (continuous_snd.comp continuous_fst)).mul continuous_snd)
  continuous_invFun := continuous_quot_mk.comp
    ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)

lemma phTriv_mk (p : PS) (k : U6464) : phTriv (phMk p k) = (p.1, rhoU p.2 * k) := rfl

/-- The projection of `P_H` (that of `coverPH`). -/
def phProj (x : PHT) : Ytilde R4 := coverPH.proj x

lemma phTriv_fst (x : PHT) : (phTriv x).1 = phProj x := by
  induction x using Quotient.inductionOn with
  | h a => rfl

/-- The right action of `U(64,64)`. -/
def phAct (x : PHT) (k : U6464) : PHT := op k • x

lemma phTriv_smul (x : PHT) (k : U6464) :
    phTriv (phAct x k) = ((phTriv x).1, (phTriv x).2 * k) := by
  induction x using Quotient.inductionOn with
  | h a =>
    show (a.1.1, rhoU a.1.2 * (a.2 * k)) = (a.1.1, rhoU a.1.2 * a.2 * k)
    rw [mul_assoc]

lemma continuous_phProj : Continuous phProj := by
  have : phProj = fun x => (phTriv x).1 := funext fun x => (phTriv_fst x).symm
  rw [this]; exact continuous_fst.comp phTriv.continuous

lemma continuous_phAct : Continuous fun xk : PHT × U6464 => phAct xk.1 xk.2 := by
  have e : (fun xk : PHT × U6464 => phAct xk.1 xk.2) =
      fun xk => phTriv.symm ((phTriv xk.1).1, (phTriv xk.1).2 * xk.2) := by
    funext xk
    rw [← phTriv_smul, Homeomorph.symm_apply_apply]
  rw [e]
  exact phTriv.symm.continuous.comp ((continuous_fst.comp (phTriv.continuous.comp continuous_fst)).prodMk
    ((continuous_snd.comp (phTriv.continuous.comp continuous_fst)).mul continuous_snd))

/-- **`P_H` on the cover is a topological principal `U(64,64)`-bundle** (globally trivial): continuous
projection and action, and a homeomorphism to the product over the base, equivariant for the action.
The set-level principal bundle structure is `coverPH`. -/
theorem coverPH_topological :
    Continuous phProj ∧ Continuous (fun xk : PHT × U6464 => phAct xk.1 xk.2) ∧
      (∀ x, (phTriv x).1 = phProj x) ∧
      (∀ x k, phTriv (phAct x k) = ((phTriv x).1, (phTriv x).2 * k)) :=
  ⟨continuous_phProj, continuous_phAct, phTriv_fst, phTriv_smul⟩

/-! ### (3.36): the associated bundle `P_H ×_{U(64,64)} ℂ^{64,64}` -/

lemma val_inv_mul (k : U6464) : ((k⁻¹ : U6464) : Matrix E64 E64 ℂ) * (k : Matrix E64 E64 ℂ) = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl

/-- `[x·k, v] = [x, k v]`. -/
def assocSetoid : Setoid (PHT × V64) where
  r a b := ∃ k : U6464, b.1 = phAct a.1 k ∧ a.2 = (k : Matrix E64 E64 ℂ) *ᵥ b.2
  iseqv := by
    refine ⟨fun a => ⟨1, (one_smul _ a.1).symm, by rw [show ((1 : U6464) : Matrix E64 E64 ℂ) = 1 from rfl,
      one_mulVec]⟩, ?_, ?_⟩
    · rintro a b ⟨k, h1, h2⟩
      refine ⟨k⁻¹, ?_, ?_⟩
      · rw [h1]; show _ = op k⁻¹ • op k • a.1
        rw [smul_smul, ← op_mul, mul_inv_cancel, op_one, one_smul]
      · rw [h2, mulVec_mulVec, val_inv_mul, one_mulVec]
    · rintro a b c ⟨k, h1, h2⟩ ⟨k', h1', h2'⟩
      refine ⟨k * k', ?_, ?_⟩
      · rw [h1', h1]; show op k' • op k • a.1 = op (k * k') • a.1
        rw [smul_smul, op_mul]
      · rw [h2, h2', mulVec_mulVec]; rfl

/-- **The bundle associated with `P_H`** through `U(64,64)` acting on `ℂ^{64,64}`. -/
def AssocPH : Type := Quotient assocSetoid

instance : TopologicalSpace AssocPH := instTopologicalSpaceQuotient

/-- The class `[x, v]`. -/
def assocMk (x : PHT) (v : V64) : AssocPH := Quotient.mk assocSetoid (x, v)

/-- Its trivialisation, on representatives. -/
def assocRaw (a : PHT × V64) : Ytilde R4 × V64 :=
  ((phTriv a.1).1, ((phTriv a.1).2 : Matrix E64 E64 ℂ) *ᵥ a.2)

lemma assocRaw_eq {a b : PHT × V64} (h : assocSetoid a b) : assocRaw a = assocRaw b := by
  obtain ⟨k, h1, h2⟩ := h
  obtain ⟨x, v⟩ := a
  obtain ⟨y, w⟩ := b
  simp only at h1 h2
  subst h1 h2
  simp only [assocRaw, phTriv_smul, mulVec_mulVec]
  rfl

/-- **The trivialisation of the associated bundle.** -/
def assocTriv : AssocPH ≃ₜ Ytilde R4 × V64 where
  toFun := Quotient.lift assocRaw fun _ _ h => assocRaw_eq h
  invFun z := assocMk (phTriv.symm (z.1, 1)) z.2
  left_inv e := by
    induction e using Quotient.inductionOn with
    | h a =>
      obtain ⟨x, v⟩ := a
      show assocMk (phTriv.symm ((phTriv x).1, 1)) (((phTriv x).2 : Matrix E64 E64 ℂ) *ᵥ v) = assocMk x v
      have hx : phAct (phTriv.symm ((phTriv x).1, 1)) (phTriv x).2 = x := by
        apply phTriv.injective
        rw [phTriv_smul, Homeomorph.apply_symm_apply, one_mul]
      refine Quotient.sound ⟨(phTriv x).2, hx.symm, rfl⟩
  right_inv z := by
    show ((phTriv (phTriv.symm (z.1, 1))).1, ((phTriv (phTriv.symm (z.1, 1))).2 : Matrix E64 E64 ℂ) *ᵥ z.2) = z
    rw [Homeomorph.apply_symm_apply]
    show (z.1, (1 : Matrix E64 E64 ℂ) *ᵥ z.2) = z
    rw [one_mulVec]
  continuous_toFun := by
    refine Continuous.quotient_lift ?_ _
    have h1 := phTriv.continuous.comp (continuous_fst : Continuous fun a : PHT × V64 => a.1)
    exact (continuous_fst.comp h1).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp h1)).matrix_mulVec continuous_snd)
  continuous_invFun := continuous_quot_mk.comp
    ((phTriv.symm.continuous.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd)

/-- **(3.36): the bundle associated with `P_H` is the spinor bundle**, as bundles over the cover. -/
def spinorIso : AssocPH ≃ₜ SpinorBundle :=
  (assocTriv.trans ((Homeomorph.refl (Ytilde R4)).prodCongr Qhomeo)).trans spinorTriv.symm

lemma spinorTriv_spinorIso (a : AssocPH) :
    spinorTriv (spinorIso a) = ((assocTriv a).1, Qv (assocTriv a).2) := by
  simp [spinorIso, Qhomeo]
  rfl

/-- It lies over the identity of the cover. -/
lemma spinorProj_spinorIso (a : AssocPH) : spinorProj (spinorIso a) = (assocTriv a).1 := by
  rw [← spinorTriv_fst, spinorTriv_spinorIso]

/-- **It is the natural map** `[[p, k], v] ↦ [p, Q(k v)]`. -/
theorem spinorIso_mk (p : PS) (k : U6464) (v : V64) :
    spinorIso (assocMk (phMk p k) v) = spinorMk p (Qv ((k : Matrix E64 E64 ℂ) *ᵥ v)) := by
  apply spinorTriv.injective
  rw [spinorTriv_spinorIso, spinorTriv_mk]
  show (p.1, Qv (((rhoU p.2 * k : U6464) : Matrix E64 E64 ℂ) *ᵥ v)) = (p.1, rhoM p.2 *ᵥ Qv _)
  rw [Submonoid.coe_mul, ← mulVec_mulVec]
  exact Prod.ext rfl (Qv_intertwine (rhoD p.2) _)

/-- **It is linear on fibres** (in the trivialisations). -/
lemma spinorIso_linear (y : Ytilde R4) (a : ℂ) (v w : V64) :
    spinorTriv (spinorIso (assocTriv.symm (y, a • v + w))) =
      (y, a • (spinorTriv (spinorIso (assocTriv.symm (y, v)))).2 +
        (spinorTriv (spinorIso (assocTriv.symm (y, w)))).2) := by
  simp only [spinorTriv_spinorIso, Homeomorph.apply_symm_apply, Qv_add_smul]

/-- The standard form on the associated bundle, in the trivialisation. -/
def assocForm (a b : AssocPH) : ℂ :=
  star (assocTriv a).2 ⬝ᵥ (Jpq (Fin 64) (Fin 64) *ᵥ (assocTriv b).2)

/-- It does not depend on the frame: `⟨[x, v], [x, w]⟩ = vᴴ J w`. -/
theorem assocForm_mk (x : PHT) (v w : V64) :
    assocForm (assocMk x v) (assocMk x w) = star v ⬝ᵥ (Jpq (Fin 64) (Fin 64) *ᵥ w) := by
  show star (((phTriv x).2 : Matrix E64 E64 ℂ) *ᵥ v) ⬝ᵥ
    (Jpq (Fin 64) (Fin 64) *ᵥ (((phTriv x).2 : Matrix E64 E64 ℂ) *ᵥ w)) = _
  have hk : ((phTriv x).2 : Matrix E64 E64 ℂ)ᴴ * Jpq (Fin 64) (Fin 64) * ((phTriv x).2 : Matrix E64 E64 ℂ) =
      Jpq (Fin 64) (Fin 64) := (phTriv x).2.2
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec, hk]

/-- **The isomorphism carries the `U(64,64)` form to the spinor form.** -/
theorem spinorForm_spinorIso (a b : AssocPH) : spinorForm (spinorIso a) (spinorIso b) = assocForm a b := by
  rw [spinorForm, spinorTriv_spinorIso, spinorTriv_spinorIso]
  exact Qv_form _ _

/-- Non-vacuity: the associated bundle is nonempty. -/
lemma nonempty_assocPH : Nonempty AssocPH :=
  ⟨assocMk (phMk (Classical.choice (nonempty_tilde (0 : R4)), 1) 1) 0⟩

end

end GU.Library
