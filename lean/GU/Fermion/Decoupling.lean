import Mathlib

/-!
# §12.9: chirality is effective, a decoupling theorem

Stylised system (12.12) on a module `V` over a field `K`, with Dirac operator `D : V →ₗ V`
and scalar coupling `Λ` (`= R/4`):

  `−Λ ψ_L + D ψ_R = 0`,  `D ψ_L − Λ ψ_R = 0`.

Proved:
* `system_iff`: equivalent to the coupled pair (12.13)–(12.14), `D ψ_L = Λ ψ_R`, `D ψ_R = Λ ψ_L`.
* `second_order`: every solution satisfies the massive equation `D² ψ_L = Λ² ψ_L` (mass `R/4`).
* `decouple_iff`: a *chiral* solution (`ψ_R = 0`, `ψ_L ≠ 0`) exists iff `Λ = 0` and `D` has
  nontrivial kernel. Chirality appears only where the scalar coupling vanishes (12.15)–(12.17).
* `mirror`: `(ψ_L, ψ_R) ↦ (ψ_R, ψ_L)` maps solutions to solutions. The fundamental theory is
  non-chiral (L ↔ R symmetric).

-- AI_BREAKTHROUGH_PATCH_V1: `Λ` is a constant scalar on the region (the draft's "approximately
constant" scalar curvature); `D` is an abstract linear operator (no spin geometry).
-/

namespace GU.Decoupling

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (D : V →ₗ[K] V) (Λ : K)

/-- The system (12.12). -/
def Solves (ψL ψR : V) : Prop := -(Λ • ψL) + D ψR = 0 ∧ D ψL - Λ • ψR = 0

theorem system_iff (ψL ψR : V) : Solves D Λ ψL ψR ↔ D ψL = Λ • ψR ∧ D ψR = Λ • ψL := by
  unfold Solves
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨sub_eq_zero.mp h2, by rw [← neg_add_eq_zero.mp h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h2]; abel, by rw [h1]; abel⟩

theorem second_order {ψL ψR : V} (h : Solves D Λ ψL ψR) : D (D ψL) = (Λ * Λ) • ψL := by
  obtain ⟨h1, h2⟩ := (system_iff D Λ ψL ψR).mp h
  rw [h1, map_smul, h2, smul_smul]

theorem mirror {ψL ψR : V} (h : Solves D Λ ψL ψR) : Solves D Λ ψR ψL := by
  obtain ⟨h1, h2⟩ := (system_iff D Λ ψL ψR).mp h
  exact (system_iff D Λ ψR ψL).mpr ⟨h2, h1⟩

theorem decouple_iff :
    (∃ ψL : V, ψL ≠ 0 ∧ Solves D Λ ψL 0) ↔ Λ = 0 ∧ ∃ ψ : V, ψ ≠ 0 ∧ D ψ = 0 := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    obtain ⟨h1, h2⟩ := (system_iff D Λ ψ 0).mp h
    rw [map_zero] at h2
    have hΛ : Λ = 0 := by
      by_contra hne
      exact hψ (by simpa [hne] using h2.symm)
    exact ⟨hΛ, ψ, hψ, by simpa [hΛ] using h1⟩
  · rintro ⟨hΛ, ψ, hψ, hD⟩
    exact ⟨ψ, hψ, (system_iff D Λ ψ 0).mpr ⟨by simp [hD, hΛ], by simp [hΛ]⟩⟩

end GU.Decoupling
