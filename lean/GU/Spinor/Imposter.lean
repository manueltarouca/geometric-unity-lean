/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Anomaly
import GU.Spinor.BminusL

/-!
# Charge content of the spin-3/2 sector `144 = 10 ⊗ 16 − 16̄` (draft §11.2, (11.6))

Weights are tracked in units `s = 2h`. The vector `10` of `Spin(6,4)` has weights `±2e_k`
(`k` = colour plane 0..2 or weak plane 3,4). Then `12Y(v) = ∓4` (colour) or `±6` (weak), and
`3(B−L)(v) = ∓2` (colour) or `0` (weak). The 160 weights of `10 ⊗ 16` are sums of a vector weight
and a spinor weight. Removing the 16 weights of the opposite chirality `16̄` (the γ-trace part)
leaves the 144.

Proved (`decide`, combinatorics only):
* `count_144`: `160 − 16 = 144` weights;
* `anomaly_144`: `Σ Y`, `Σ Y³`, `Σ (B−L)`, `Σ (B−L)³` all vanish on the 144. This is automatic for any
  `so(10)` representation (traceless Cartan elements, no cubic Casimir), so it is bookkeeping, not
  evidence. The draft's "imposter generation" is a proper subset of the 144; the rest carry
  exotic charges (e.g. `Y = 3/2, 7/6, 5/6`), and nothing here addresses that subset alone.
-/

namespace GU.Spinor

/-- Vector weights: (plane, sign). -/
def vecW : List (Fin 5 × Bool) := (List.finRange 5).flatMap fun k => [(k, false), (k, true)]

def yVec (v : Fin 5 × Bool) : ℤ := (if v.1.val < 3 then -4 else 6) * sgn v.2
def blVec (v : Fin 5 × Bool) : ℤ := (if v.1.val < 3 then -2 else 0) * sgn v.2

/-- `12Y` and `3(B−L)` on `10 ⊗ 16` (odd chirality spinor). -/
def tensorCharges : List (ℤ × ℤ) :=
  vecW.flatMap fun v => oddWeights.map fun s => (yVec v + twelveY s, blVec v + threeBL s)

/-- Charges on `16̄` (the even chirality). -/
def barCharges : List (ℤ × ℤ) := evenWeights.map fun s => (twelveY s, threeBL s)

/-- The 144: remove `16̄` from `10 ⊗ 16` as multisets. -/
def charges144 : List (ℤ × ℤ) := tensorCharges.diff barCharges

set_option maxRecDepth 100000 in
theorem count_144 : tensorCharges.length = 160 ∧ charges144.length = 144 := by decide +kernel

set_option maxRecDepth 100000 in
theorem bar_sub : barCharges.Subperm tensorCharges := by decide +kernel

set_option maxRecDepth 100000 in
theorem anomaly_144 :
    (charges144.map (·.1)).sum = 0 ∧ (charges144.map fun c => c.1 ^ 3).sum = 0 ∧
    (charges144.map (·.2)).sum = 0 ∧ (charges144.map fun c => c.2 ^ 3).sum = 0 := by decide +kernel

end GU.Spinor
