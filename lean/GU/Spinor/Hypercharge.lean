import GU.Spinor.Reductions

/-!
# Hypercharges from the five planes of `N^{6,4}` (draft §4, §11.3)

The plane operators `π_k = γ_{a_k} γ_{b_k}` (`k = 0..4`, three colour planes in the positive
block, two weak planes in the negative block):
* square to `−1` and commute pairwise (`planes_sq`, `planes_comm`), so they have simultaneous
  eigenvalues `−i s_k`, `s_k = ±1` (convention of `WeightSpaces.lean`: on `range P_s`,
  `π_k = −i s_k`);
* multiply to the (6,4) volume element: `ω₁₀ = π₀π₁π₂π₃π₄` (`ω10_planes`). So a fixed
  `N`-chirality fixes the parity of the number of `s_k = −1`; each parity gives the 16 weights
  of a Weyl spinor of `Spin(6,4)`.

Hypercharge as a combination of `J₊` (colour, `B−L`) and `J₋` (weak, `J₋/i ∝ T₃ᴿ`), in integer form.
It is the standard `Spin(10) ⊃ SU(5) ⊃ SM` branching of the 16; the direction is forced by
`su(3,2)`-tracelessness (`GU.Predictions.hypercharge_forced`):
`12 Y = −2(s₀+s₁+s₂) + 3(s₃+s₄)`. Over the 16 odd-parity weights (`hypercharge_table`) this
takes exactly the values of one Standard Model generation plus `ν^c`:
`Q (×6): 2`, `u^c (×3): −8`, `d^c (×3): 4`, `L (×2): −6`, `e^c (×1): 12`, `ν^c (×1): 0`,
i.e. `Y = 1/6, −2/3, 1/3, −1/2, 1, 0`.
-/

namespace GU.Spinor

open CSum

/-- Plane operator `π_k`. -/
def planeOp (k : Fin 5) : PString :=
  let p := planes.get (Fin.cast (by decide) k)
  gammaP p.1 * gammaP p.2

theorem planes_sq : ∀ k : Fin 5, PString.beq (planeOp k * planeOp k) (PString.neg PString.one) = true := by
  decide

theorem planes_comm : ∀ k l : Fin 5, PString.beq (planeOp k * planeOp l) (planeOp l * planeOp k) = true := by
  decide

/-- `ω₁₀` is exactly the product of the five plane operators. -/
theorem ω10_planes : ω10P = planeOp 0 * planeOp 1 * planeOp 2 * planeOp 3 * planeOp 4 :=
  PString.eq_of_beq (by decide)

/-- Weights `s ∈ {±1}⁵`, encoded by `Bool` (`true ↦ −1`). -/
def sgn (b : Bool) : ℤ := if b then -1 else 1

def allWeights : List (Fin 5 → Bool) :=
  (List.finRange 32).map fun n k => n.val.testBit k.val

/-- Parity of the number of `−1`s: fixes the `Spin(6,4)` Weyl chirality. -/
def parity (s : Fin 5 → Bool) : ℕ := ((List.finRange 5).countP fun k => s k) % 2

/-- Odd chirality (contains one SM generation). -/
def oddWeights : List (Fin 5 → Bool) := allWeights.filter fun s => parity s == 1

/-- Even chirality (contains the conjugate generation). -/
def evenWeights : List (Fin 5 → Bool) := allWeights.filter fun s => parity s == 0

/-- `12 Y`. -/
def twelveY (s : Fin 5 → Bool) : ℤ := -2 * (sgn (s 0) + sgn (s 1) + sgn (s 2)) + 3 * (sgn (s 3) + sgn (s 4))

theorem weights_length : oddWeights.length = 16 ∧ evenWeights.length = 16 := by decide

/-- **One SM generation (+ ν^c) emerges** on the odd chirality: the multiset of `12Y`. -/
theorem hypercharge_table :
    (oddWeights.map twelveY).Perm [2, 2, 2, 2, 2, 2, -8, -8, -8, 4, 4, 4, -6, -6, 12, 0] := by
  decide

/-- The other chirality carries exactly the opposite hypercharges (antiparticles). -/
theorem hypercharge_table_conj :
    (evenWeights.map twelveY).Perm [-2, -2, -2, -2, -2, -2, 8, 8, 8, -4, -4, -4, 6, 6, -12, 0] := by
  decide

/-- Electric-charge sanity check: `Q = T₃ᴸ + Y` with `T₃ᴸ = (s₃ − s₄)/4` gives the familiar
charges (×12): `{2+3,2-3 (u,d)×3, −8, 4, −6±6, 12, 0}` → `Q ∈ {2/3,−1/3,−2/3,1/3,0,−1,1,0}`. -/
def twelveQ (s : Fin 5 → Bool) : ℤ := twelveY s + 3 * (sgn (s 3) - sgn (s 4))

theorem charge_table :
    (oddWeights.map twelveQ).Perm [8, 8, 8, -4, -4, -4, -8, -8, -8, 4, 4, 4, 0, -12, 12, 0] := by
  decide

end GU.Spinor
