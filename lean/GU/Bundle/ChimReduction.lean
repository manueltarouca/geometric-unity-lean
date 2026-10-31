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
**Caveat (index alignment, `ΦL_horiz`, `ΦL_vert`)**: under the identification `Φ : ℝ¹⁴ ≃ CFib`
used for `O77 ≃* O(Bη)`, the horizontal `H*` (base) directions are `SH = {e₆, e₁₁, e₁₂, e₁₃}`, and
the vertical `V` (signature (6,4)) ones are the other ten. `PatiSalamGroup.lean`'s blocks
(`W6 = {1..6}`, `W4 = {10..13}`, base `{0,7,8,9}`) are an abstract `(1,3) ⊕ (6) ⊕ (4)` choice that
is **not** aligned with `V ⊕ H*` under `Φ` (`e₆ ∈ W6` is horizontal). So `PS6`/`PS4` and the "base
legs" `SB` below are not literally the chimeric `V`-blocks and `H*`; a `Φ`-aligned Pati–Salam would use
`W6' = {0..5}`, `W4' = {7..10}`, base `SH`.

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

/-! ### The chimeric splitting `C = V ⊕ H*` in the `Φ` basis -/

/-- The horizontal (`H*`, base `(1,3)`) indices of `ℝ¹⁴` under `Φ`: `Φ eᵢ ∈ H*` exactly for these. -/
def SH : Finset (Fin 14) := {6, 11, 12, 13}

/-- **`Φ eᵢ` is horizontal** (no `V`-component) for `i ∈ SH`. -/
theorem ΦL_horiz (i : Fin 14) (hi : i ∈ SH) : (ΦL (Pi.single i 1 : Fin 14 → ℝ)).1 = 0 := by
  simp only [SH, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
  simp [ΦL, GU.Iso77.Φiso, GU.Iso77.Ψ, GU.Iso77.Bon_apply, GU.Iso77.toCFL, GU.Iso77.toCF,
    GU.Chimeric.chimVec, GU.Chimeric.chimCoord, GU.Iso77.σl, Module.Basis.equivFun_symm_apply,
    Pi.single_apply] <;> exact Or.inr rfl

/-- **`Φ eᵢ` is vertical** (no `H*`-component) for `i ∉ SH`. -/
theorem ΦL_vert (i : Fin 14) (hi : i ∉ SH) : (ΦL (Pi.single i 1 : Fin 14 → ℝ)).2 = 0 := by
  fin_cases i <;> simp only [SH, Finset.mem_insert, Finset.mem_singleton] at hi <;>
  first
  | (exfalso; revert hi; decide)
  | (simp [ΦL, GU.Iso77.Φiso, GU.Iso77.Ψ, GU.Iso77.Bon_apply, GU.Iso77.toCFL, GU.Iso77.toCF,
      GU.Chimeric.chimVec, GU.Chimeric.chimCoord, GU.Iso77.σl, Module.Basis.equivFun_symm_apply,
      Pi.single_apply]
     first | done | (rw [show (fun _ : Fin 4 => (0 : ℝ)) = 0 from rfl, smul_zero]
                     ext v; simp [GU.Iso77.dotCLM]))

end GU.Library
