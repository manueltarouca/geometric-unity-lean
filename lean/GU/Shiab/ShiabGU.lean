/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.Einstein

/-!
# A synthetic Shiab operator satisfying the draft's three requirements

-- AI_BREAKTHROUGH_PATCH_V1 (synthetic operator, found by the linear search in
-- experiments/shiab_search.py):

  `⧉_GU ξ = [Φ₁∧⋆ξ] − (⋆/2)·( [Φ₁∧⋆[Φ₂∧⋆ξ]] + {Φ₁∧⋆{Φ₂∧⋆ξ}} )`

the printed (9.3) with its second term taken as the *sum* of the commutator–commutator and
anticommutator–anticommutator versions. Numerically (n = 4, 6; Euclidean and Lorentzian-type
signatures; relative errors ~1e−16):
* it annihilates Weyl curvature;
* it maps Riemann curvature to the Einstein form;
* its symbol pairing `Tr(α ∧ ⧉(ξ∧β))` is antisymmetric, i.e. `⧉∘d_B` is formally self-adjoint.
  This is *necessary* for the quadratic part of the variation (9.4) → (9.7). The printed
  one-bracket (9.3) fails it (`FormsWitness.not_selfadjoint`).
* It is **not sufficient**: the cubic term `⅓Tr(T∧⧉[T,T])` still does not vary to
  `⟨α, ⧉[T,T]⟩` (sample-dependent ratio, experiments/cubic_check.py). So (9.7) does not follow
  from (9.4) with `⧉_GU` either (independent review 4).

Formalised here (Clifford core, as in `Einstein.lean`): on Riemann-type curvature the added
commutator–commutator piece vanishes (`scalar_term_comm`), so `⧉_GU` has the same Einstein
output (`shiabGU_einstein`). The self-adjointness is numerical only (forms are not modelled).
-/

namespace GU.CliffordBianchi

open Finset

variable {A : Type*} [Ring A] [Algebra ℝ A] {n : ℕ} {w : Fin n → ℝ} {γ : Fin n → A}

theorem shiabGU_einstein (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) (b : Fin n) :
    (∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) - γ x * γ y * γ a))
      + (1 / 2 : ℝ) • ((∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
            (γ a * γ c * (γ x * γ y) + γ x * γ y * (γ a * γ c))
          + ∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
            (γ a * γ c * (γ x * γ y) - γ x * γ y * (γ a * γ c))) * γ b)
      = (4 : ℝ) • ∑ y, (w y * einstein w R b y) • γ y := by
  rw [scalar_term_comm hR, add_zero]
  exact shiab_einstein h hw hR b

end GU.CliffordBianchi
