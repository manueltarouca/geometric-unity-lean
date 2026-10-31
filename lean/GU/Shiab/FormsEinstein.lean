import GU.Shiab.FormsWitness

/-!
# Einstein output of the printed (9.3) *with Hodge stars*, checked in Lean (n = 4, Euclidean)

Using the computable forms layer of `FormsWitness.lean`: for every Kulkarni–Nomizu product
`R = h ⊙ k` of elementary symmetric 4×4 integer matrices (these 55 tensors span all algebraic
curvature tensors), the doubled printed Shiab of the curvature form
`ξ_R = Σ_{a<b} e^{ab} ⊗ Σ_{c<d} R_abcd γ_cγ_d` equals `−4 ⋆(Σ_a e^a ⊗ Σ_b G_ab γ_b)` with
`G = Ric − ½ R g` (`einstein_all`). So in Euclidean signature, with these conventions, the
printed coefficient `−½` gives the Einstein tensor, Hodge stars included. The Clifford-core
theorem `shiab_einstein` is reproduced at form level. By linearity it holds for all algebraic
curvature tensors (linearity of the list-based operations is not formalised).
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

/-- Elementary symmetric matrix `E_ij + E_ji` (or `E_ii`). -/
def esym (i j : Fin 4) (a b : Fin 4) : ℤ := if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0

/-- Kulkarni–Nomizu product. -/
def kn (h k : Fin 4 → Fin 4 → ℤ) (a b c d : Fin 4) : ℤ :=
  h a c * k b d + h b d * k a c - h a d * k b c - h b c * k a d

def pairs : List (Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap fun a => (List.finRange 4).filterMap fun b => if a < b then some (a, b) else none

def curvForm (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ) : Form :=
  pairs.map fun ab => ([ab.1, ab.2],
    pairs.flatMap fun cd => smul (R ab.1 ab.2 cd.1 cd.2) (mul (γ4 cd.1) (γ4 cd.2)))

def ric (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ) (b d : Fin 4) : ℤ :=
  ((List.finRange 4).map fun a => R a b a d).sum

def scal (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ) : ℤ := ((List.finRange 4).map fun b => ric R b b).sum

/-- `−4 ⋆(Σ_a e^a ⊗ Σ_b G_ab γ_b)` with `2G = 2Ric − R g`, written integrally. -/
def einsteinForm (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ) : Form :=
  star ((List.finRange 4).map fun a => ([a],
    (List.finRange 4).flatMap fun b =>
      smul (-2 * (2 * ric R a b - (if a = b then scal R else 0))) (γ4 b)))

def allIdx : List Idx4 :=
  (List.range 16).map fun m => (List.finRange 4).filter fun i => m.testBit i.val

def coefAt (A : Form) (I : Idx4) : CSum := (A.filter fun x => x.1 == I).flatMap (·.2)

/-- Decidable equality test for forms (coefficientwise via the certified zero test). -/
def formEq (A B : Form) : Bool := allIdx.all fun I => isZero (coefAt A I ++ neg (coefAt B I))

def checkKN (p q : Fin 4 × Fin 4) : Bool :=
  let R := kn (esym p.1 p.2) (esym q.1 q.2)
  formEq (twoShiab (curvForm R)) (einsteinForm R)

def symPairs : List (Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap fun a => (List.finRange 4).filterMap fun b => if a ≤ b then some (a, b) else none

/-- Unordered pairs of symmetric generators (55 KN products). -/
def knPairs : List ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) :=
  (symPairs.zip (List.range symPairs.length)).flatMap fun p =>
    (symPairs.zip (List.range symPairs.length)).filterMap fun q =>
      if p.2 ≤ q.2 then some (p.1, q.1) else none

theorem knPairs_length : knPairs.length = 55 := by decide

end GU.FormsW
