import Mathlib

/-!
# The chimeric metric on `C = V ⊕ H*` has signature (7,7) (draft (3.9)–(3.10), §3.5)

At the point `g = η` of `Y` the chimeric bundle is `C_η = Sym²(ℝ⁴) ⊕ ℝ⁴`. The metric is
* on `V = Sym²`: the DeWitt supermetric `tr(ηAηB) − λ tr(ηA) tr(ηB)` (gap M1);
* on `H*`: the inverse metric `η⁻¹ = η`;
with `V ⊥ H*`.

-- AI_BREAKTHROUGH_PATCH_V1 (synthetic choices narrowing M1): `λ = 1`, the classical DeWitt
value, which makes the trace direction negative so `V` has signature (6,4); and the relative
sign `+DeWitt ⊕ +g⁻¹` between `V` and `H*`, which remains a convention (the draft, p. 22:
(7,7) vs (9,5) "not yet forced"). With these, `C` has signature (7,7) at (1,3) points. At
(3,1) points the same formula gives (9,5) (the DeWitt part is even in `g`, the `H*` part odd).

Lean gives a diagonal Gram matrix for 14 vectors; that they span the 14-dimensional
`Sym² ⊕ ℝ⁴` and Sylvester's law are not formalised.

Proved by an explicit orthogonal basis (`chimBasis`) whose Gram matrix is checked by `decide`
over `ℤ` to be diagonal, with 7 positive and 7 negative entries.
-/

namespace GU.Chimeric

open Matrix

/-- The 10 symmetric-matrix basis directions used for `V`. -/
def symE (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun a b =>
  if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0

def diagM (d : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ := diagonal d

/-- A vector of `C_η`: a symmetric matrix (vertical part) and a covector (horizontal part). -/
abbrev Cvec := Matrix (Fin 4) (Fin 4) ℤ × (Fin 4 → ℤ)

/-- `η = diag(1,-1,-1,-1)` over `ℤ` (it is its own inverse). -/
def ηZ : Matrix (Fin 4) (Fin 4) ℤ := diagonal ![1, -1, -1, -1]

/-- Integer DeWitt form at `η` (same formula as `GU.deWitt`, which lives over `ℚ`). -/
def deWittZ (lam : ℤ) (A B : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  trace (ηZ * A * ηZ * B) - lam * trace (ηZ * A) * trace (ηZ * B)

/-- The chimeric bilinear form at `η` with DeWitt parameter `λ`. -/
def chimForm (lam : ℤ) (x y : Cvec) : ℤ :=
  deWittZ lam x.1 y.1 + ∑ i, ηZ i i * x.2 i * y.2 i

/-- Orthogonal basis of `C_η`:
mixed `S₀ᵢ` (3, norm −2), spatial `Sᵢⱼ` (3, norm +2), diagonal `u = (1,−1,−1,−1)` (−12),
`w₁ = (1,1,0,0)` (2), `w₂ = (1,−1,2,0)` (6), `w₃ = (1,−1,−1,3)` (12), then `e⁰` (+1), `eⁱ` (−1). -/
def chimBasis : Fin 14 → Cvec :=
  ![(symE 0 1, 0), (symE 0 2, 0), (symE 0 3, 0),
    (symE 1 2, 0), (symE 1 3, 0), (symE 2 3, 0),
    (diagM ![1, -1, -1, -1], 0), (diagM ![1, 1, 0, 0], 0), (diagM ![1, -1, 2, 0], 0),
    (diagM ![1, -1, -1, 3], 0),
    (0, Pi.single 0 1), (0, Pi.single 1 1), (0, Pi.single 2 1), (0, Pi.single 3 1)]

/-- Expected norms. -/
def chimNorms : Fin 14 → ℤ := ![-2, -2, -2, 2, 2, 2, -12, 2, 6, 12, 1, -1, -1, -1]

theorem chimBasis_gram : ∀ i j : Fin 14,
    chimForm 1 (chimBasis i) (chimBasis j) = if i = j then chimNorms i else 0 := by
  decide

theorem chim_signature :
    (Finset.univ.filter fun i => 0 < chimNorms i).card = 7 ∧
      (Finset.univ.filter fun i => chimNorms i < 0).card = 7 := by
  decide

end GU.Chimeric
