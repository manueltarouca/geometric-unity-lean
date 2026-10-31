import GU.Gauge.Inhomogeneous
import GU.Bundle.Principal

/-!
# (6.12): `𝒢 → N` is a principal `𝓗`-bundle under the tilted action

`𝓗` acts on the right of `𝒢` by `g · h = g τ₋(h)`. With projection `π_{A0}` this is a
principal bundle in the sense of `GU.PrincipalBundle`: `π` is onto, `τ₋`-invariant, the action is
free, and it is transitive on fibres (`pi_eq_iff`).
-/

namespace GU.GaugeData

open MulOpposite

variable {H N : Type*} [Group H] [AddCommGroup N] (D : GaugeData H N)

/-- Right action of `𝓗` on `𝒢` through `τ₋`. -/
instance tiltedAction : MulAction Hᵐᵒᵖ (IG D) where
  smul h g := g * D.tau (-1) h.unop
  one_smul g := by show g * D.tau (-1) 1 = g; simp
  mul_smul a b g := by
    show g * D.tau (-1) (a * b).unop = g * D.tau (-1) b.unop * D.tau (-1) a.unop
    rw [unop_mul, map_mul, mul_assoc]

/-- **(6.12)**: `𝒢` is a principal `𝓗`-bundle over `N` with projection `π_{A0}`. -/
def principalG : PrincipalBundle H (IG D) N where
  proj := D.pi
  proj_surjective := D.pi_surjective
  proj_smul g h := D.pi_invariant_tau_neg g h
  free g h hgh := by
    have : g * D.tau (-1) h = g * 1 := by rw [mul_one]; exact hgh
    exact D.tau_injective (-1) (by rw [mul_left_cancel this, map_one])
  transitive g g' hgg := by
    obtain ⟨h, hh⟩ := (D.pi_eq_iff g g').mp hgg
    exact ⟨h, hh.symm⟩

end GU.GaugeData
