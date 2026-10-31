import GU.Bundle.LocalFrames
import GU.Spinor.SpinConnected

/-!
# The Pati–Salam subgroup of the chimeric structure group `O(7,7)`

`Spin6`, `Spin4 ⊆ Spin(7,7)` (`PatiSalamGroup.lean`; the draft's Pati–Salam `Spin(6) × Spin(4)`,
(4.8)–(4.9), embedded here on the fibre blocks of `Spin(7,7)` rather than in `Spin(6,4)`) are pushed
into the structure group `O77` of the chimeric orthonormal frame bundle by the spin cover. Since the
cover kills `−1 ∈ Spin6 ∩ Spin4`, the images are the block `SO(6)` and `SO(4)` (and their product
`SO(6) × SO(4)`; the `ℤ₂` collapses):
* `PS6`, `PS4` **commute** (`PS6_PS4_commute`) and lie in **`SO₀(7,7)`** (`PS6_le_SO0`, `PS4_le_SO0`);
* each **fixes the complement of its block** (`PS6_fixes`: basis vectors outside
  `W6 = span(e₁..e₆)`; `PS4_fixes`: outside `W4 = span(e₁₀..e₁₃)`);
* hence **both preserve the four base legs `e₀, e₇, e₈, e₉` of every chimeric frame**
  (`PS6_preserves_base_legs`, `PS4_preserves_base_legs`).
This is **not** a reduction of the structure group: no sub-bundle, section or Higgs-type field is
constructed (cf. `PHASE1_BLUEPRINT.md` §4.1). The `U(3,2)` reduction is formalised only at the
Lie-algebra level (`Reductions.lean`).
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor
open scoped ContDiff

/-- The image of the Pati–Salam `Spin6` in `O77` (the block `SO(6)`). -/
noncomputable def PS6 : Subgroup O77 := Spin6.map spinToO77
/-- The image of the Pati–Salam `Spin4` in `O77` (the block `SO(4)`). -/
noncomputable def PS4 : Subgroup O77 := Spin4.map spinToO77

/-- **The two Pati–Salam factors commute in `O(7,7)`.** -/
theorem PS6_PS4_commute {g h : O77} (hg : g ∈ PS6) (hh : h ∈ PS4) : g * h = h * g := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨y, hy, rfl⟩ := hh
  rw [← map_mul, ← map_mul, spin6_spin4_commute hx hy]

lemma range_le_SO0 (H : Subgroup Spin77) : H.map spinToO77 ≤ SO0 := by
  rintro _ ⟨x, -, rfl⟩
  exact spinToO77_mem x

/-- **Both factors lie in the identity component `SO₀(7,7)`.** -/
theorem PS6_le_SO0 : PS6 ≤ SO0 := range_le_SO0 _
theorem PS4_le_SO0 : PS4 ≤ SO0 := range_le_SO0 _

lemma single_perp {S : Finset (Fin 14)} {j : Fin 14} (hj : j ∉ S) :
    (Pi.single j 1 : Fin 14 → ℝ) ∈ perpOf S := by
  intro a ha
  refine polar_disjoint (S := S) (T := {j}) (Finset.disjoint_singleton_right.mpr hj) ha ?_
  intro i hi
  rw [Finset.mem_singleton] at hi
  simp [hi]

/-- **Block structure**: `PS6` fixes every basis vector outside `W6`. -/
theorem PS6_fixes {g : O77} (hg : g ∈ PS6) {j : Fin 14} (hj : j ∉ S6) :
    Matrix.of (g : Mat 14) *ᵥ Pi.single j 1 = Pi.single j 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  show Matrix.of (spinMat x) *ᵥ _ = _
  rw [of_spinMat_mulVec]
  exact spin6_fixes hx (single_perp hj)

/-- **Block structure**: `PS4` fixes every basis vector outside `W4`. -/
theorem PS4_fixes {g : O77} (hg : g ∈ PS4) {j : Fin 14} (hj : j ∉ S4) :
    Matrix.of (g : Mat 14) *ᵥ Pi.single j 1 = Pi.single j 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  show Matrix.of (spinMat x) *ᵥ _ = _
  rw [of_spinMat_mulVec]
  exact spin4_fixes hx (single_perp hj)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The base directions `e₀, e₇, e₈, e₉` (the (1,3) part). -/
def SB : Finset (Fin 14) := {0, 7, 8, 9}

lemma ractM_leg (q : HomTotM X) (g : Mat 14) (j : Fin 14)
    (hg : Matrix.of g *ᵥ Pi.single j 1 = Pi.single j 1) :
    (show HomF from (ractM q g).2) (Pi.single j 1) = (show HomF from q.2) (Pi.single j 1) := by
  show (show HomF from q.2) (matCLM g (Pi.single j 1)) = _
  rw [matCLM_apply, hg]

/-- **`PS6` preserves the four base legs of every chimeric frame.** -/
theorem PS6_preserves_base_legs (q : HomTotM X) {g : O77} (hg : g ∈ PS6) {j : Fin 14} (hj : j ∈ SB) :
    (show HomF from (ractM q g).2) (Pi.single j 1) = (show HomF from q.2) (Pi.single j 1) :=
  ractM_leg q g j (PS6_fixes hg (by revert hj; revert j; decide))

/-- **`PS4` preserves the four base legs of every chimeric frame.** -/
theorem PS4_preserves_base_legs (q : HomTotM X) {g : O77} (hg : g ∈ PS4) {j : Fin 14} (hj : j ∈ SB) :
    (show HomF from (ractM q g).2) (Pi.single j 1) = (show HomF from q.2) (Pi.single j 1) :=
  ractM_leg q g j (PS4_fixes hg (by revert hj; revert j; decide))

end GU.Library
