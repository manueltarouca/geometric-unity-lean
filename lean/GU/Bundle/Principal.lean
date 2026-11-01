/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import Mathlib

/-!
# Set-level principal bundles and extension of structure group (roadblock R1)

Mathlib has fiber and vector bundles but no principal bundles. This file provides the minimum the
draft's (3.32) needs: a principal `G`-bundle (free right action, invariant projection, transitive
on fibers) and the extension `P ×_ρ K` along a homomorphism `ρ : G →* K`, which is again a
principal `K`-bundle.

Topology and smoothness (local triviality, smooth action) are deliberately left out; they are
the next layer once Mathlib or this project has the infrastructure.
Right actions are encoded as `MulAction Gᵐᵒᵖ P`, written `p <• g`.
-/

namespace GU

open MulOpposite

/-- A principal `G`-bundle over `B`, at the level of sets. -/
structure PrincipalBundle (G : Type*) [Group G] (P B : Type*) [MulAction Gᵐᵒᵖ P] where
  proj : P → B
  proj_surjective : Function.Surjective proj
  proj_smul : ∀ (p : P) (g : G), proj (op g • p) = proj p
  free : ∀ (p : P) (g : G), op g • p = p → g = 1
  transitive : ∀ p q : P, proj p = proj q → ∃ g : G, op g • p = q

namespace Extension

variable {G K : Type*} [Group G] [Group K] (ρ : G →* K) (P : Type*) [MulAction Gᵐᵒᵖ P]

/-- `(p, k) ~ (p', k')` iff `p' = p · g` and `k = ρ(g) k'` for some `g`, i.e. `[p·g, k] = [p, ρ(g)k]`. -/
def setoid : Setoid (P × K) where
  r x y := ∃ g : G, y.1 = op g • x.1 ∧ x.2 = ρ g * y.2
  iseqv := by
    refine ⟨fun x => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, h1, h2⟩
      refine ⟨g⁻¹, ?_, ?_⟩
      · rw [h1, smul_smul, ← op_mul, mul_inv_cancel, op_one, one_smul]
      · rw [h2, map_inv, inv_mul_cancel_left]
    · rintro x y z ⟨g, h1, h2⟩ ⟨g', h1', h2'⟩
      refine ⟨g * g', ?_, ?_⟩
      · rw [h1', h1, smul_smul, ← op_mul]
      · rw [h2, h2', map_mul, mul_assoc]

/-- The total space `P ×_ρ K`. -/
def Space : Type _ := Quotient (setoid ρ P)

/-- The class `[p, k]`. -/
def mk (p : P) (k : K) : Space ρ P := Quotient.mk (setoid ρ P) (p, k)

lemma mk_eq_mk {p p' : P} {k k' : K} :
    mk ρ P p k = mk ρ P p' k' ↔ ∃ g : G, p' = op g • p ∧ k = ρ g * k' := Quotient.eq

/-- Right `K`-action `[p, k] · k₀ = [p, k k₀]`. -/
instance instMulAction : MulAction Kᵐᵒᵖ (Space ρ P) where
  smul k₀ := Quotient.map (fun x => (x.1, x.2 * k₀.unop)) (by
    rintro x y ⟨g, h1, h2⟩
    exact ⟨g, h1, by simp [h2, mul_assoc]⟩)
  one_smul x := by
    induction x using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (by simp)
  mul_smul a b x := by
    induction x using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (by simp [mul_assoc])

@[simp] lemma op_smul_mk (p : P) (k k₀ : K) : op k₀ • mk ρ P p k = mk ρ P p (k * k₀) := rfl

variable {ρ P} {B : Type*}

/-- `P ×_ρ K` is a principal `K`-bundle over the same base. -/
def bundle (π : PrincipalBundle G P B) : PrincipalBundle K (Space ρ P) B where
  proj := Quotient.lift (fun x => π.proj x.1) (by
    rintro x y ⟨g, h1, -⟩
    simp [h1, π.proj_smul])
  proj_surjective b := by
    obtain ⟨p, rfl⟩ := π.proj_surjective b
    exact ⟨mk ρ P p 1, rfl⟩
  proj_smul x k := by
    induction x using Quotient.inductionOn
    rfl
  free x k₀ hx := by
    induction x using Quotient.inductionOn with
    | h x =>
      obtain ⟨g, h1, h2⟩ := (mk_eq_mk ρ P).mp hx
      have hg : g = 1 := π.free _ g h1.symm
      simpa [hg] using h2
  transitive x y hxy := by
    induction x using Quotient.inductionOn with
    | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      obtain ⟨g, hg⟩ := π.transitive x.1 y.1 hxy
      refine ⟨x.2⁻¹ * ρ g * y.2, ?_⟩
      show mk ρ P x.1 (x.2 * (x.2⁻¹ * ρ g * y.2)) = mk ρ P y.1 y.2
      rw [mk_eq_mk]
      exact ⟨g, hg.symm, by group⟩

end Extension

end GU
