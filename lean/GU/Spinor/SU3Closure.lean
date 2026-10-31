import GU.Spinor.SMGroup

/-!
# `su3` and `su2` close under commutators

For every pair of generators, `[A, B]` is `0`, or `c·g` for a generator `g` with `c ∈ {±2, ±4, ±6, ±8}`,
or an integer combination `a H₁ + b H₂` of the Cartan elements with `|a|, |b| ≤ 4`
(`su3_closed`, checked by `decide`). Likewise for `su2` (`su2_closed`). With
`su3_linIndep` this makes the 8 elements an 8-dimensional Lie algebra commuting with the
centre, of the form expected for `su(3)` (the identification itself is classical).
-/

namespace GU.Spinor

open CSum

def coeffs : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def inSpan (S : List CSum) (H1 H2 : CSum) (X : CSum) : Bool :=
  isZero X ||
  S.any (fun g => [-8, -6, -4, -2, 2, 4, 6, 8].any fun c => isZero (X ++ smul c g)) ||
  coeffs.any fun a => coeffs.any fun b => isZero (X ++ smul a H1 ++ smul b H2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem su3_closed :
    su3.all (fun A => su3.all fun B =>
      inSpan su3 (su3.getD 6 []) (su3.getD 7 []) (comm A B)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem su2_closed :
    su2.all (fun A => su2.all fun B => inSpan su2 (su2.getD 2 []) [] (comm A B)) = true := by
  decide +kernel

end GU.Spinor
