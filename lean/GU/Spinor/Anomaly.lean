import GU.Spinor.Hypercharge

/-!
# Anomaly cancellation for the generation produced by `N^{6,4}` (Phase 1 gap: "anomaly")

The draft gives no anomaly-cancellation mechanism. We check the perturbative gauge anomaly
coefficients of the 16 weights of one `N`-chirality (`hypercharge_table`), labelled by plane
weights `s`. Reading them as one left-handed 16 needs the Majorana reality of the 128
(`Cl(7,7) ≅ ℝ(128)`) plus a fixed chirality convention, neither formalised here; each weight space
is rank 4 in `ℂ¹²⁸`. `X` here is the `J₊`/B−L direction, which spans the centre together with `Y`. Classification:
* colour triplet iff the three colour signs are not all equal (singlet iff `s₀ = s₁ = s₂`);
* weak doublet iff `s₃ ≠ s₄`.

All anomaly coefficients vanish (`anomaly_free`):
* `U(1)_Y³`: `Σ Y³ = 0`;  gravitational `U(1)_Y`: `Σ Y = 0`;
* `SU(3)²U(1)_Y`: `Σ_{coloured} Y = 0`;  `SU(2)²U(1)_Y`: `Σ_{doublets} Y = 0`;
* with the extra `U(1)_X`, `X ∝ s₀+s₁+s₂` (the `B−L`-like direction of `J₊`):
  `Σ X³ = Σ X = Σ X²Y = Σ XY² = 0`, and `SU(3)²X`, `SU(2)²X` vanish too.

The opposite chirality carries the conjugates, so the full non-chiral spectrum on `Y` is
vector-like (trivially anomaly free). The point here is that the *effective chiral* generation
is anomaly free on its own. Global and gravitational anomalies in 14 dimensions are not addressed.
-/

namespace GU.Spinor

def colored (s : Fin 5 → Bool) : Bool := !(s 0 == s 1 && s 1 == s 2)
def doublet (s : Fin 5 → Bool) : Bool := s 3 != s 4

/-- `X ∝ B−L`-like charge from `J₊`. -/
def Xc (s : Fin 5 → Bool) : ℤ := sgn (s 0) + sgn (s 1) + sgn (s 2)

def sumOver (L : List (Fin 5 → Bool)) (f : (Fin 5 → Bool) → ℤ) : ℤ := (L.map f).sum

theorem anomaly_free :
    sumOver oddWeights (fun s => twelveY s ^ 3) = 0 ∧
    sumOver oddWeights twelveY = 0 ∧
    sumOver (oddWeights.filter colored) twelveY = 0 ∧
    sumOver (oddWeights.filter doublet) twelveY = 0 ∧
    sumOver oddWeights (fun s => Xc s ^ 3) = 0 ∧
    sumOver oddWeights Xc = 0 ∧
    sumOver oddWeights (fun s => Xc s ^ 2 * twelveY s) = 0 ∧
    sumOver oddWeights (fun s => Xc s * twelveY s ^ 2) = 0 ∧
    sumOver (oddWeights.filter colored) Xc = 0 ∧
    sumOver (oddWeights.filter doublet) Xc = 0 := by
  decide

/-- Sanity: the generation has 12 coloured states (Q: 6, u^c: 3, d^c: 3) and 8 doublet states
(Q: 6, L: 2). -/
theorem multiplet_counts :
    (oddWeights.filter colored).length = 12 ∧ (oddWeights.filter doublet).length = 8 := by decide

end GU.Spinor
