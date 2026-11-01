/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.Principal
import GU.Geometry.Signature
import GU.Geometry.IndefUnitary
import GU.Spinor.Basis

/-!
# The main principal bundle `P_H = P̃_Fr(C^{7,7}) ×_{ρ_D} U(64,64)` (draft (3.32))

Gaps are explicit hypotheses (structures), never global `axiom`s, so `#print axioms` shows only
Lean's standard axioms.

* `ChimericSpinStructure Y`: an arbitrary principal `Spin(7,7)`-bundle over an arbitrary base
  `Y`. **Nothing here ties it to `C = V ⊕ H*`, to `TY`, or to `Y = Met(X)`.** That link needs
  smooth frame bundles (roadblock R3) and is the main remaining gap (M2).
* `DiracRep`: a homomorphism `Spin(7,7) → U(64,64)`. Phase 3 constructs the draft's one
  explicitly as `diracRep` (see `GU/Spinor/`), and `GU.diracRep_faithful` (in
  `GU/Spinor/Faithful.lean`) proves it injective, the `↪` of (3.28).

`mainBundle` is the generic extension-of-structure-group theorem specialised to these groups.
`physicalBundle` instantiates it with the explicit `ρ_D`. `degenerateModel` shows the structures
are inhabited (point base, trivial bundle). It does **not** show a spin structure exists on the
real 14-dimensional `C`.
-/

namespace GU

open Matrix

universe u

/-- Synthetic axiom (gap M2): a spin structure on the chimeric bundle, as a principal
`Spin(7,7)`-bundle over `Y`. -/
structure ChimericSpinStructure (Y : Type u) where
  /-- total space of the spin double cover of the `SO₀(7,7)` frame bundle of `C`. -/
  Ptilde : Type u
  [act : MulAction Spin77ᵐᵒᵖ Ptilde]
  bundle : PrincipalBundle Spin77 Ptilde Y

attribute [instance] ChimericSpinStructure.act

/-- Interface for the Dirac representation (3.31). Originally a synthetic hypothesis (roadblock R4);
now instantiated by `diracRep` below. -/
structure DiracRep where
  ρ : Spin77 →* U6464

/-- The `↪` of (3.28). Proved for `diracRep` in `GU/Spinor/Faithful.lean`. -/
def DiracRep.Faithful (R : DiracRep) : Prop := Function.Injective R.ρ

variable {Y : Type u}

/-- Total space of `P_H = P̃(C) ×_{ρ_D} U(64,64)`. -/
abbrev PH (S : ChimericSpinStructure Y) (R : DiracRep) : Type u :=
  Extension.Space R.ρ S.Ptilde

/-- Extension of structure group: `P̃ ×_ρ U(64,64)` is a principal `U(64,64)`-bundle over `Y`. -/
def mainBundle (S : ChimericSpinStructure Y) (R : DiracRep) :
    PrincipalBundle U6464 (PH S R) Y :=
  Extension.bundle S.bundle

/-- The trivial `Spin(7,7)`-bundle over a point, acting by right multiplication. -/
def trivialSpin : ChimericSpinStructure.{0} PUnit where
  Ptilde := Spin77
  bundle :=
    { proj := fun _ => PUnit.unit
      proj_surjective := fun _ => ⟨1, rfl⟩
      proj_smul := fun _ _ => rfl
      free := fun p g h => by
        simpa using (show p * g = p from h)
      transitive := fun p q _ => ⟨p⁻¹ * q, by
        show p * (p⁻¹ * q) = q
        group⟩ }

/-- The draft's Dirac representation, constructed: `Spin(7,7) → U(C) ≃ U(64,64)`. -/
noncomputable def diracRep : DiracRep := ⟨Spinor.UC_equiv_U6464.toMonoidHom.comp Spinor.rhoD⟩

/-- (3.32): `P_H` with the explicit `ρ_D`. The only remaining hypothesis is the spin structure. -/
noncomputable def physicalBundle (S : ChimericSpinStructure Y) :
    PrincipalBundle U6464 (PH S diracRep) Y :=
  mainBundle S diracRep

/-- Degenerate model (point base, trivial bundle) with the real `ρ_D`. It shows the structures
are inhabited; it says nothing about spin structures on the real `C`. -/
noncomputable def degenerateModel : PrincipalBundle U6464 (PH trivialSpin diracRep) PUnit :=
  physicalBundle trivialSpin

end GU
