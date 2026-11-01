/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.FormsWitness

/-!
# Lean-checked: the cubic Chern–Simons term blocks (9.4) → (9.7) for `⧉_GU`

With `[T,T]` read as `T∧T` (the reading under which (9.4)'s `½, ⅓` reproduce `½·CS`), the
variation of `⅓ Tr(T ∧ ⧉[T,T])` equals `⟨α, ⧉[T,T]⟩` only if
`Tr(T ∧ ⧉([α,T] + [T,α])) = 2 Tr(α ∧ ⧉[T,T])` (with the commutator-wedge bracket the target is
`k = ½`; numerically infeasible for every `k`, see the log). For the synthetic `⧉_GU` (which passes the
quadratic self-adjointness test, `GU_witness_ok`) this fails at
`T = e⁰⊗γ₀ + e¹⊗γ₁γ₃`, `α = e²⊗γ₂γ₃` (`cubic_fails`). Numerically no Weyl-killing,
Einstein-producing member of the Def 8.1 family satisfies it for any coefficient (see log).
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

def Tw : Form := [([0], γ4 0), ([1], mul (γ4 1) (γ4 3))]
def αw : Form := [([2], mul (γ4 2) (γ4 3))]

def cubicL : ℤ := topTrace (wedge pl Tw (twoShiabGU (wedge cm αw Tw ++ wedge cm Tw αw)))
def cubicR : ℤ := topTrace (wedge pl αw (twoShiabGU (wedge cm Tw Tw)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cubic_fails : cubicL ≠ 2 * cubicR := by decide +kernel

end GU.FormsW
