import GU.Spinor.PSum

/-!
# A Lean-checked counterexample: the printed (9.3) is not formally self-adjoint

A small *computable* exterior algebra over `Fin 4` with coefficients in `CSum` (Clifford
elements), using the four Euclidean generators `γ_a = gen (a,+)` of `Cl(7,7)` (a `Cl(4,0)` inside;
the trace is the 128-dimensional one, i.e. 32 times the 4-dimensional trace).

* `wedge br`: wedge of forms with a bracket on the values; `star`: Euclidean Hodge star
  (`e^I ∧ ⋆e^I = vol`); `Φ₁ = Σ e^a⊗γ_a`, `Φ₂ = Σ_{a<b} e^{ab}⊗γ_aγ_b`.
* `twoShiab ξ = 2[Φ₁∧⋆ξ] − ⋆{Φ₁∧⋆{Φ₂∧⋆ξ}}`: twice the printed (9.3) with the Einstein-type
  brackets (commutator, anticommutator, anticommutator).
* `S(α,β) = tr(top part of α ∧ twoShiab(ξ∧β))`.

`not_selfadjoint`: with `ξ = e⁰`, `α = e¹⊗γ₁`, `β = e¹⊗γ₀γ₁`, `S(α,β) + S(β,α) ≠ 0`. So the
symbol pairing is not antisymmetric and `⧉∘d_B` is not formally self-adjoint, which the
variational step (9.4) → (9.7) needs. (Same witness as experiments/shiab_adjoint.py.)
Conventions: Euclidean signature, trace pairing; see the log for convention caveats.
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

abbrev Idx4 := List (Fin 4)
abbrev Form := List (Idx4 × CSum)

def γ4 (a : Fin 4) : CSum := [gammaP (a.castLE (by decide), false)]

/-- Sign of concatenating two strictly increasing index lists (0 if they overlap). -/
def mergeSign (I J : Idx4) : ℤ :=
  if I.any (fun i => J.contains i) then 0
  else (-1) ^ ((I.map fun i => (J.filter fun j => j < i).length).sum)

def sortIdx (I : Idx4) : Idx4 := (List.finRange 4).filter fun i => I.contains i

def wedge (br : CSum → CSum → CSum) (A B : Form) : Form :=
  A.flatMap fun x => B.filterMap fun y =>
    let s := mergeSign x.1 y.1
    if s = 0 then none else some (sortIdx (x.1 ++ y.1), smul s (br x.2 y.2))

def compl (I : Idx4) : Idx4 := (List.finRange 4).filter fun i => !I.contains i

/-- Euclidean Hodge star: `⋆e^I = sign(I, Iᶜ) e^{Iᶜ}`. -/
def star (A : Form) : Form := A.map fun x => (compl x.1, smul (mergeSign x.1 (compl x.1)) x.2)

def cm (x y : CSum) : CSum := comm x y
def acm (x y : CSum) : CSum := mul x y ++ mul y x
def pl (x y : CSum) : CSum := mul x y

def Φ1 : Form := (List.finRange 4).map fun a => ([a], γ4 a)
def Φ2 : Form := ((List.finRange 4).flatMap fun a => (List.finRange 4).filterMap fun b =>
  if a < b then some ([a, b], mul (γ4 a) (γ4 b)) else none)

/-- Twice the printed Shiab (Einstein brackets). -/
def twoShiab (ξ : Form) : Form :=
  (wedge cm Φ1 (star ξ)).map (fun x => (x.1, smul 2 x.2)) ++
    (star (wedge acm Φ1 (star (wedge acm Φ2 (star ξ))))).map (fun x => (x.1, neg x.2))

def topTrace (A : Form) : ℤ :=
  ((A.filter fun x => x.1 == [0, 1, 2, 3]).map fun x => (x.2.map PString.tr).sum).sum

def ξ0 : Form := [([0], [⟨1, fun _ => .one⟩])]

def Spair (α β : Form) : ℤ := topTrace (wedge pl α (twoShiab (wedge pl ξ0 β)))

def α0 : Form := [([1], γ4 1)]
def β0 : Form := [([1], mul (γ4 0) (γ4 1))]

theorem not_selfadjoint : Spair α0 β0 + Spair β0 α0 ≠ 0 := by decide

/-- The value (128-dim trace, doubled Shiab). -/
theorem witness_value : Spair α0 β0 + Spair β0 α0 = 2 * 8 * 32 ∨
    Spair α0 β0 + Spair β0 α0 = -(2 * 8 * 32) := by decide

/-- Twice the synthetic `⧉_GU` (Euclidean sign): the second term uses both bracket pairings. -/
def twoShiabGU (ξ : Form) : Form :=
  twoShiab ξ ++ (star (wedge cm Φ1 (star (wedge cm Φ2 (star ξ))))).map (fun x => (x.1, neg x.2))

def SpairGU (α β : Form) : ℤ := topTrace (wedge pl α (twoShiabGU (wedge pl ξ0 β)))

/-- `⧉_GU` passes the same test: the symmetric part vanishes on the witness. -/
theorem GU_witness_ok : SpairGU α0 β0 + SpairGU β0 α0 = 0 := by decide

end GU.FormsW
