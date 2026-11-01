/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.MainBundle
import GU.Observerse.Manifold

/-!
# A trivial principal bundle and `P_H` over the type of an observerse chart

`trivialSpinOver B` is the trivial principal `Spin(7,7)`-bundle `B × Spin(7,7)` over an *arbitrary*
type `B`. With the explicit Dirac representation, `localPH` gives a principal `U(64,64)`-bundle over
the type `Y|_U`. This only shows the structures can be instantiated over that base. Its
identification with the spin cover of the frame bundle of `C` is **not** formalised (`C` is not
a bundle in Lean). Also, `Y|_U` contains the (3,1) sector, where `C` has signature (9,5), so a
Spin(7,7) structure of `C` makes sense only on the (1,3) component. Classically `C` is trivial
over such charts, so a (non-unique) spin structure exists there.

Global existence (obstruction theory on all of `Y`) remains open; this is only the local
statement. Topology/smoothness are not modelled, as in `Principal.lean`.
-/

namespace GU

open MulOpposite

/-- Right multiplication on the `Spin(7,7)` factor. -/
@[reducible] def spinAct (B : Type) : MulAction Spin77ᵐᵒᵖ (B × Spin77) where
  smul g p := (p.1, p.2 * g.unop)
  one_smul p := by show (p.1, p.2 * (1 : Spin77ᵐᵒᵖ).unop) = p; simp
  mul_smul a b p := by
    show (p.1, p.2 * (a * b).unop) = (p.1, p.2 * b.unop * a.unop)
    simp [mul_assoc]

/-- Trivial principal `Spin(7,7)`-bundle over any base. -/
def trivialSpinOver (B : Type) : ChimericSpinStructure.{0} B where
  Ptilde := B × Spin77
  act := spinAct B
  bundle := letI := spinAct B
    { proj := Prod.fst
      proj_surjective := fun b => ⟨(b, 1), rfl⟩
      proj_smul := fun _ _ => rfl
      free := fun p g h => by
        have : p.2 * g = p.2 := congrArg Prod.snd h
        simpa using this
      transitive := fun p q hpq => ⟨p.2⁻¹ * q.2, by
        show (p.1, p.2 * (p.2⁻¹ * q.2)) = q
        ext
        · exact hpq
        · simp⟩ }

/-- `P_H`-type bundle over the type `Y|_U`. -/
noncomputable def localPH (U : TopologicalSpace.Opens (Fin 4 → ℝ)) :
    PrincipalBundle U6464 (PH (trivialSpinOver (Observerse.Yloc U)) diracRep) (Observerse.Yloc U) :=
  physicalBundle _

end GU
