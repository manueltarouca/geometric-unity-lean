import GU.Spinor.Reductions

/-!
# Pati–Salam Lie algebra structure (draft §4.2, (4.8)–(4.9))

Within `cl(7,7)`, using the CSum calculus:
* `so6_closed`: the 15 bivectors of the positive 6 generators close under commutators. Each
  `[b, b']` is `0` or `±2` times another bivector of the set, so they form a Lie algebra
  (its identification with `so(6) ≅ su(4)` is standard), the colour-lepton factor.
* `su2L_su2R`: on the negative 4 generators, `Rs = (b₀₁+b₂₃, b₀₂−b₁₃, b₀₃+b₁₂)` (contains
  `P₃+P₄ = J₋ ∝ T₃ᴿ`, so this is su(2)_R) and `Ls = (b₀₁−b₂₃, b₀₂+b₁₃, b₀₃−b₁₂)` (= `SMGroup.su2`,
  the weak su(2)_L) commute and close: `so(4) = su(2)_L ⊕ su(2)_R` as in (4.8).
* `so6_so4_commute`: the two blocks commute.
-/

namespace GU.Spinor

open CSum

def pos6 : List Gen := [(1, false), (2, false), (3, false), (4, false), (5, false), (6, false)]
def neg4 : List Gen := [(3, true), (4, true), (5, true), (6, true)]

def bivsOf (L : List Gen) : List CSum :=
  ((List.range L.length).flatMap fun i => (List.range L.length).filterMap fun j =>
    if i < j then some (biv (L.getD i (0, false)) (L.getD j (0, false))) else none)

def so6 : List CSum := bivsOf pos6
def so4 : List CSum := bivsOf neg4

def closesIn (S : List CSum) (A B : CSum) : Bool :=
  isZero (comm A B) || S.any fun C => isZero (comm A B ++ smul 2 C) || isZero (comm A B ++ smul (-2) C)

set_option maxRecDepth 100000 in
theorem so6_closed : so6.length = 15 ∧ so6.all (fun A => so6.all fun B => closesIn so6 A B) = true := by
  decide +kernel

def nb (i j : ℕ) : CSum := biv (neg4.getD i (0, false)) (neg4.getD j (0, false))
def Rs : List CSum := [nb 0 1 ++ nb 2 3, nb 0 2 ++ neg (nb 1 3), nb 0 3 ++ nb 1 2]
def Ls : List CSum := [nb 0 1 ++ neg (nb 2 3), nb 0 2 ++ nb 1 3, nb 0 3 ++ neg (nb 1 2)]

def cyc3 : List (ℕ × ℕ × ℕ) := [(0, 1, 2), (1, 2, 0), (2, 0, 1)]

set_option maxRecDepth 100000 in
theorem su2L_su2R :
    cyc3.all (fun t => isZero (comm (Rs.getD t.1 []) (Rs.getD t.2.1 []) ++ smul (-4) (Rs.getD t.2.2 []))) = true ∧
    cyc3.all (fun t => isZero (comm (Ls.getD t.1 []) (Ls.getD t.2.1 []) ++ smul 4 (Ls.getD t.2.2 []))) = true ∧
    Ls.all (fun A => Rs.all fun B => isZero (comm A B)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem so6_so4_commute : so6.all (fun A => so4.all fun B => isZero (comm A B)) = true := by
  decide +kernel

end GU.Spinor
