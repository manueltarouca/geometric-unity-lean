/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.Isometry77

/-!
# A set-level spin lift of the orthonormal frame bundle of `C` over `Y₁₃`

`P̃ = Y₁₃ × Spin(7,7)` with `lift (y, s) = (y, T_P ∘ spinToOG s)`, where `T_P` is the reference
orthonormal frame at `y` (`TP` with a chosen `P`). Proved: `lift` covers the identity on `Y₁₃`
(`lift_proj`) and is equivariant along `spinToOG` (`lift_equivariant`):
`lift (p · g) = lift p · spinToOG g`.

**Caveat.** As with `frameBundle`/`orthoFrameBundle`, everything here is set level: the frame bundle
is a product `Y × G` with no topology, so this lift exists trivially and says nothing about the
genuine obstruction (`w₂` of `C`, continuity/smoothness of frames). It closes the *algebraic*
chain `Spin(7,7) → O(7,7) → frames → P_H`; the topological spin structure remains open.
-/

namespace GU

open MulOpposite GU.Iso77 GU.Observerse
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Reference orthonormal frame at a (1,3) point (choice of `P`). -/
noncomputable def refFrame (y : Y13 X) : {f : CFib ≃ₗ[ℝ] CFib // ∀ u v, Bmod (Gpt y.1) (f u) (f v) = Bη u v} :=
  ⟨TP y.2.choose y.2.choose_spec.1, fun u v =>
    (congrArg (fun G => Bmod G (TP y.2.choose y.2.choose_spec.1 u) (TP y.2.choose y.2.choose_spec.1 v))
      y.2.choose_spec.2).trans (TP_isometry _ _ u v)⟩

/-- The lift `Y₁₃ × Spin(7,7) → OFrames`. -/
noncomputable def lift (p : Y13 X × Spin77) : OFrames X :=
  ⟨p.1, ⟨(spinToOG p.2).1.trans (refFrame p.1).1, fun u v => by
    show Bmod (Gpt p.1.1) ((refFrame p.1).1 ((spinToOG p.2).1 u)) ((refFrame p.1).1 ((spinToOG p.2).1 v)) = Bη u v
    rw [(refFrame p.1).2, (spinToOG p.2).2 u v]⟩⟩

theorem lift_proj (p : Y13 X × Spin77) : (lift p).1 = p.1 := rfl

theorem lift_equivariant (p : Y13 X × Spin77) (g : Spin77) :
    lift (p.1, p.2 * g) = op (spinToOG g) • lift p := by
  simp only [lift]
  show (⟨p.1, _⟩ : OFrames X) = ⟨p.1, _⟩
  congr 2
  apply LinearEquiv.ext; intro u
  simp [map_mul]

end GU
