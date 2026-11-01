/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinClosed

/-!
# **`Spin(7,7) → SO₀(7,7)` is a covering map**

`spinToSO0 : Spin77 →* SO₀(7,7)` (the identity component of the Lie group `O77`) is surjective
(`connectedComponent_O77`) and continuous (`continuous_spinToO77`). `Spin77` is closed in the
finite-dimensional `Cl(7,7)` (`isClosed_spin`), hence σ-compact; `SO₀` is closed in the locally
compact `O77`, hence Baire. The open mapping theorem (`MonoidHom.isOpenMap_of_sigmaCompact`) makes
`spinToSO0` open, hence a quotient map; its kernel `{±1}` (`vecRep_ker`) is finite, hence discrete;
so it is a quotient covering map (`isQuotientCoveringMap_of_isDiscrete_ker_monoidHom`):
**`isCoveringMap_spinToSO0`**. Its kernel is contained in `{±1}` (`ker_spinToSO0_finite`).
Not yet shown here: that `Spin77` is connected, which is what makes this the *nontrivial* double
cover rather than possibly `SO₀ × ℤ/2`.
-/

namespace GU.Spinor

open Matrix CliffordAlgebra GU.Library Topology

/-- `SO₀(7,7)`: the identity component of `O77`. -/
noncomputable abbrev SO0 : Subgroup O77 := Subgroup.connectedComponentOfOne O77

lemma spinToO77_mem (x : Spin77) : spinToO77 x ∈ SO0 := by
  show spinToO77 x ∈ connectedComponent (1 : O77)
  rw [connectedComponent_O77]; exact ⟨x, rfl⟩

/-- **The spin cover** `Spin(7,7) →* SO₀(7,7)`. -/
noncomputable def spinToSO0 : Spin77 →* SO0 := spinToO77.codRestrict SO0 spinToO77_mem

lemma spinToSO0_surjective : Function.Surjective spinToSO0 := by
  rintro ⟨A, hA⟩
  have : A ∈ connectedComponent (1 : O77) := hA
  rw [connectedComponent_O77] at this
  obtain ⟨x, rfl⟩ := this
  exact ⟨x, rfl⟩

lemma continuous_spinToSO0 : Continuous spinToSO0 := continuous_spinToO77.subtype_mk _

instance sigmaCompact_M128 : SigmaCompactSpace M128 := inferInstanceAs (SigmaCompactSpace (Idx → Idx → ℝ))

instance sigmaCompact_Cl77 : SigmaCompactSpace Cl77 :=
  cl77Homeomorph.isClosedEmbedding.sigmaCompactSpace

instance sigmaCompact_Spin77 : SigmaCompactSpace Spin77 := isClosed_spin.sigmaCompactSpace

instance locallyCompact_O77 : LocallyCompactSpace O77 := isClosed_O77.locallyCompactSpace

instance locallyCompact_SO0 : LocallyCompactSpace SO0 :=
  (isClosed_connectedComponent (x := (1 : O77))).locallyCompactSpace

lemma isOpenMap_spinToSO0 : IsOpenMap spinToSO0 :=
  spinToSO0.isOpenMap_of_sigmaCompact spinToSO0_surjective continuous_spinToSO0

lemma ker_spinToSO0_finite : (spinToSO0.ker : Set Spin77).Finite := by
  refine (Set.toFinite ({1, negOne} : Set Spin77)).subset fun x hx => ?_
  have hx' : spinToO77 x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hv : ∀ v, vecRep x v = v := fun v => by
    have h := of_spinMat_mulVec x v
    have h1 : spinMat x = Matrix.of.symm 1 := congrArg Subtype.val hx'
    rw [h1, Equiv.apply_symm_apply, one_mulVec] at h
    exact h.symm
  rcases vecRep_ker x hv with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- **`Spin(7,7) → SO₀(7,7)` is a covering map** (a quotient covering by its kernel, `{±1}`: `ker_spinToSO0_eq`). -/
theorem isQuotientCoveringMap_spinToSO0 : IsQuotientCoveringMap spinToSO0 spinToSO0.ker :=
  (isOpenMap_spinToSO0.isQuotientMap continuous_spinToSO0 spinToSO0_surjective)
    |>.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom ker_spinToSO0_finite.isDiscrete

theorem isCoveringMap_spinToSO0 : IsCoveringMap spinToSO0 :=
  isQuotientCoveringMap_spinToSO0.isCoveringMap

end GU.Spinor
