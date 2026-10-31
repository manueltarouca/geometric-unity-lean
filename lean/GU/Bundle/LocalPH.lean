import GU.Bundle.MainBundle
import GU.Observerse.Manifold

/-!
# `P_H` over a chart of the observerse (local closure of gap M2)

Over a chart `Y|_U` (`GU.Observerse.Yloc U`), the chimeric bundle is trivial (it is a product
over `U × LorFiber`). A spin structure is then the trivial principal bundle
`Y|_U × Spin(7,7)` with right multiplication (`trivialSpinOver`). With the explicit Dirac
representation this gives `P_H|_{Y|_U}` as a principal `U(64,64)`-bundle (`localPH`).

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
def trivialSpinOver (B : Type) [Nonempty B] : ChimericSpinStructure.{0} B where
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

/-- `P_H` over an observerse chart with nonempty `U`. -/
noncomputable def localPH (U : TopologicalSpace.Opens (Fin 4 → ℝ)) [Nonempty (Observerse.Yloc U)] :
    PrincipalBundle U6464 (PH (trivialSpinOver (Observerse.Yloc U)) diracRep) (Observerse.Yloc U) :=
  physicalBundle _

end GU
