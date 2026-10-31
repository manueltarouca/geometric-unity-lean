import Mathlib

/-!
# Shiab operator: degree audit and the typed (9.3) (draft §8–9)

Correction (independent review, checked against the rendered PDF): (9.3) reads
`⧉_ε ξ = [ε⁻¹Φ¹ε ∧ ⋆ξ] − (⋆/2)[ε⁻¹Φ¹ε ∧ ⋆[ε⁻¹Φ²ε ∧ ⋆ξ]]`, with the outer Hodge star printed
over the ½. Text extraction had dropped that star. So **(9.3) has correct degrees**, and the
Phase 2 claim of a Shiab degree defect is withdrawn.

What survives (gap M11, a typo): the expanded integrand after (9.4), `Tr(T ∧ ⋆(⧉ξ))`, is a
2-form. The first line of (9.4), the L² pairing `⟨T, ⋆⧉(·)⟩ = ±∫ Tr(T ∧ ⧉(·))`, is correct.

1. `FExpr` is a degree-checking language; `draft93_ok` and the integrand theorems check the above.
2. `GradedForms` and `GaugeOnForms` give a typed model in which (9.3) is a map
   `Ω²(ad) → Ω¹³(ad)`. Its gauge equivariance (the "ship in a bottle" property (8.1)) is
   *proved* from the stated axioms. `GaugeOnForms.ad` is not required to be a group action;
   the equivariance proof doesn't need it.

Still open, and not assumed here: Weyl annihilation and the Bianchi-identity properties (§8.2).
-/

namespace GU

/-- Wedge/Hodge expressions with leaves of known degree. -/
inductive FExpr
  | leaf (deg : ℕ)
  | wedge (a b : FExpr)
  | star (a : FExpr)

namespace FExpr

/-- Degree on a `d`-manifold; `none` if a wedge overflows `d`. -/
def deg (d : ℕ) : FExpr → Option ℕ
  | leaf k => if k ≤ d then some k else none
  | wedge a b => do
      let x ← deg d a
      let y ← deg d b
      if x + y ≤ d then some (x + y) else none
  | star a => (deg d a).map (d - ·)

/-- Curvature-like input `ξ ∈ Ω²`. -/
def ξ : FExpr := leaf 2

/-- Draft (9.3), first term: `Φ₁ ∧ ⋆ξ`. -/
def draftRicciTerm : FExpr := wedge (leaf 1) (star ξ)

/-- Draft (9.3), second term as printed: `⋆[Φ₁ ∧ ⋆(Φ₂ ∧ ⋆ξ)]`. -/
def draftScalarTerm : FExpr := star (wedge (leaf 1) (star (wedge (leaf 2) (star ξ))))

theorem draftRicciTerm_ok : deg 14 draftRicciTerm = some 13 := by decide

/-- (9.3) is degree-correct as printed. -/
theorem draft93_ok : deg 14 draftScalarTerm = some 13 := by decide

/-- Dropping the outer star (the misreading Phase 2 made) gives a 3-form. -/
theorem withoutOuterStar : deg 14 (wedge (leaf 1) (star (wedge (leaf 2) (star ξ)))) = some 1 := by
  decide

/-- Draft integrand after (9.4): `Tr(T ∧ ⋆(⧉ ξ))` with `⧉ξ ∈ Ω¹³` is a 2-form. -/
theorem draftIntegrand_bad : deg 14 (wedge (leaf 1) (star (leaf 13))) = some 2 := by decide

/-- The pairing `⟨T, ⋆⧉ξ⟩ = ∫ Tr(T ∧ ⧉ξ)` is top degree. -/
theorem repairedIntegrand_ok : deg 14 (wedge (leaf 1) (leaf 13)) = some 14 := by decide

end FExpr

universe u

/-- Abstract graded ad-valued forms on a `d`-manifold. The wedge already includes the Lie
bracket on the ad-values (draft (8.1)). -/
structure GradedForms (d : ℕ) where
  Ω : ℕ → Type u
  [acg : ∀ k, AddCommGroup (Ω k)]
  [mod : ∀ k, Module ℝ (Ω k)]
  wedge : ∀ {a b : ℕ}, Ω a → Ω b → Ω (a + b)
  hodge : ∀ {k : ℕ}, Ω k →ₗ[ℝ] Ω (d - k)

attribute [instance] GradedForms.acg GradedForms.mod

/-- Gauge group action on forms, and the conjugation `Φ ↦ ε⁻¹ Φ ε` of the invariant elements. -/
structure GaugeOnForms {d : ℕ} (F : GradedForms.{u} d) (H : Type*) [Group H] where
  ad : ∀ {k : ℕ}, H → F.Ω k →ₗ[ℝ] F.Ω k
  ad_wedge : ∀ {a b : ℕ} (h : H) (x : F.Ω a) (y : F.Ω b),
    ad h (F.wedge x y) = F.wedge (ad h x) (ad h y)
  ad_hodge : ∀ {k : ℕ} (h : H) (x : F.Ω k), ad h (F.hodge x) = F.hodge (ad h x)
  /-- `conj ε Φ = ε⁻¹ Φ ε`. -/
  conj : ∀ {k : ℕ}, H → F.Ω k → F.Ω k
  conj_mul : ∀ {k : ℕ} (ε h : H) (Φ : F.Ω k), conj (ε * h) Φ = ad h (conj ε Φ)

variable {F : GradedForms.{u} 14} {H : Type*} [Group H]

/-- The draft's Shiab operator (9.3), typed as `Ω²(ad) → Ω¹³(ad)`:
`⧉_ε ξ = ε⁻¹Φ₁ε ∧ ⋆ξ − κ ⋆(ε⁻¹Φ₁ε ∧ ⋆(ε⁻¹Φ₂ε ∧ ⋆ξ))`. The draft has `κ = 1/2`. -/
def shiab (G : GaugeOnForms F H) (Φ₁ : F.Ω 1) (Φ₂ : F.Ω 2) (κ : ℝ) (ε : H) (ξ : F.Ω 2) :
    F.Ω 13 :=
  F.wedge (G.conj ε Φ₁) (F.hodge ξ) -
    κ • F.hodge (F.wedge (G.conj ε Φ₁) (F.hodge (F.wedge (G.conj ε Φ₂) (F.hodge ξ))))

/-- "Ship in a bottle" (draft §8): `⧉_{εh}(h⁻¹ξh) = h⁻¹(⧉_ε ξ)h`. -/
theorem shiab_equivariant (G : GaugeOnForms F H) (Φ₁ : F.Ω 1) (Φ₂ : F.Ω 2) (κ : ℝ)
    (ε h : H) (ξ : F.Ω 2) :
    shiab G Φ₁ Φ₂ κ (ε * h) (G.ad h ξ) = G.ad h (shiab G Φ₁ Φ₂ κ ε ξ) := by
  -- The degrees `13` and `1 + (14 - 2)` agree only up to defeq, so state each step at `k := 13`.
  have e1 : G.ad (k := 13) h (F.wedge (G.conj ε Φ₁) (F.hodge ξ))
      = F.wedge (G.conj (ε * h) Φ₁) (F.hodge (G.ad h ξ)) := by
    rw [G.conj_mul, ← G.ad_hodge]; exact G.ad_wedge (a := 1) (b := 12) h _ _
  have e2 : G.ad (k := 13) h
        (F.hodge (F.wedge (G.conj ε Φ₁) (F.hodge (F.wedge (G.conj ε Φ₂) (F.hodge ξ)))))
      = F.hodge (F.wedge (G.conj (ε * h) Φ₁)
          (F.hodge (F.wedge (G.conj (ε * h) Φ₂) (F.hodge (G.ad h ξ))))) := by
    rw [G.conj_mul, G.conj_mul, ← G.ad_hodge, ← G.ad_wedge, ← G.ad_hodge, ← G.ad_wedge]
    exact G.ad_hodge (k := 1) h _
  rw [shiab, shiab, map_sub, map_smul, e1, e2]

end GU
