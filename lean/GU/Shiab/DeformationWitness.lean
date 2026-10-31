import GU.Shiab.FormsWitness

/-!
# Lean-checked: the deformation complex (10.1) is not exact for the printed Shiab (n = 4)

Principal symbols at `ξ = e⁰` (Euclidean, `n = 4`, Clifford values in four generators of `Cl(7,7)`):
`σ₁(φ) = (ξ⊗φ, 0)`, `σ₂(α, φ) = ⧉(ξ∧α) − κ⋆(ξ⊗φ)`.

Witness `α = e¹ ⊗ γ₂γ₃`, `φ = 0`:
* `sigma2_kills`: `⧉(ξ ∧ α) = 0` for the printed (9.3) (Einstein brackets), so `(α, 0) ∈ ker σ₂`;
* `not_in_image`: every `ξ ∧ φ` is supported on index sets containing `0`, while `α` lives on `{1}`,
  so `(α, 0) ∉ im σ₁`.
Hence `ker σ₂ ≠ im σ₁` at `ξ = e⁰`: the symbol sequence is not exact and (10.1) is not elliptic
for this operator. (Within the full twisted operator family, ellipticity is achievable; see the log.)
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

def αdef : Form := [([1], mul (γ4 2) (γ4 3))]

def allIdx4 : List Idx4 := (List.range 16).map fun m => (List.finRange 4).filter fun i => m.testBit i.val

/-- `⧉(ξ ∧ α)` is the zero form (all coefficients cancel). -/
theorem sigma2_kills : allIdx4.all (fun I =>
    isZero ((twoShiab (wedge pl ξ0 αdef)).filter (fun x => x.1 == I) |>.flatMap (·.2))) = true := by
  decide +kernel

/-- Images of `σ₁` only have index sets containing `0`; `α` has index set `[1]`. -/
theorem not_in_image (φ : Form) : ∀ x ∈ wedge pl ξ0 φ, (0 : Fin 4) ∈ x.1 := by
  intro x hx
  simp only [wedge, ξ0, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filterMap] at hx
  obtain ⟨y, -, hy⟩ := hx
  split_ifs at hy with h
  obtain rfl := Option.some.inj hy
  simp [sortIdx]

theorem alpha_support : αdef.all (fun x => !(x.1.contains 0)) = true := by decide

end GU.FormsW
