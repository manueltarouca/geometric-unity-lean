import GU.synthetic_predictions

/-!
# Explicit `su(3) ⊕ su(2) ⊕ u(1)_Y ⊕ u(1)_{B−L}` generators in `spin(6,4)` (draft (4.6))

With `P_k` the plane rotations and `X_ij = b(p_i1,p_j1) + b(p_i2,p_j2)`,
`Y_ij = b(p_i1,p_j2) − b(p_i2,p_j1)` (same-type planes):
* `su3`: `X₀₁, Y₀₁, X₀₂, Y₀₂, X₁₂, Y₁₂, P₀−P₁, P₀+P₁−2P₂` (8, colour planes);
* `su2`: `X₃₄, Y₃₄, P₃−P₄` (3, weak planes).

Proved (`decide`): both sets commute with the central `J₊`, `J₋` (hence with `Ŷ` and B−L); `su3`
and `su2` commute with each other; each set is linearly independent (diagonal trace-Gram); and
the sample Cartan relation `[X₀₁, Y₀₁] = 4(P₀ − P₁)` holds. Together with `center_two_u1`, this
exhibits the Standard Model algebra plus `u(1)_{B−L}` explicitly inside the observerse's
`spin(6,4) ⊂ cl(7,7)`.

Closure under all brackets is proved in `SU3Closure.lean`. Not proved: that these span the full centraliser (which relies on the classical dimension count). So "su(3)" here
means 8 independent, centre-commuting elements of the expected form.
-/

namespace GU.Spinor

open CSum GU.Predictions

def Pk (k : ℕ) : CSum := let p := planes.getD k ((0, false), (0, false)); biv p.1 p.2
def Xij (i j : ℕ) : CSum :=
  let p := planes.getD i ((0, false), (0, false)); let q := planes.getD j ((0, false), (0, false))
  biv p.1 q.1 ++ biv p.2 q.2
def Yij (i j : ℕ) : CSum :=
  let p := planes.getD i ((0, false), (0, false)); let q := planes.getD j ((0, false), (0, false))
  biv p.1 q.2 ++ neg (biv p.2 q.1)

def su3 : List CSum := [Xij 0 1, Yij 0 1, Xij 0 2, Yij 0 2, Xij 1 2, Yij 1 2, Pk 0 ++ neg (Pk 1), Pk 0 ++ Pk 1 ++ smul (-2) (Pk 2)]
def su2 : List CSum := [Xij 3 4, Yij 3 4, Pk 3 ++ neg (Pk 4)]

set_option maxRecDepth 100000 in
theorem sm_commutes_center :
    (su3 ++ su2).all (fun A => isZero (comm A Jpos) && isZero (comm A Jneg)) = true ∧
      su3.all (fun A => su2.all fun B => isZero (comm A B)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem su3_gram : ∀ i j : Fin 8, i ≠ j → trPair (su3.getD i []) (su3.getD j []) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem su3_gram_diag : ∀ i : Fin 8, trPair (su3.getD i []) (su3.getD i []) ≠ 0 := by decide +kernel

theorem su3_linIndep : LinearIndependent ℝ (fun i : Fin 8 => toMat (su3.getD i [])) :=
  linIndep_of_gram _ su3_gram su3_gram_diag

set_option maxRecDepth 100000 in
theorem su2_linIndep : LinearIndependent ℝ (fun i : Fin 3 => toMat (su2.getD i [])) :=
  linIndep_of_gram _ (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem cartan_relation : isZero (comm (Xij 0 1) (Yij 0 1) ++ smul (-4) (Pk 0 ++ neg (Pk 1))) = true := by
  decide +kernel

end GU.Spinor
