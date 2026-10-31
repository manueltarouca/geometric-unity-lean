import GU.Observerse.Manifold

/-!
# Observations `ι : X → Y` (Definition 3.1, Einsteinian case)

A metric field on a chart `U ⊆ ℝ⁴` is a map `g : ℝ⁴ → ℝ¹⁰` (symmetric-matrix coordinates)
taking Lorentzian values on `U`. Its observation is `ι(x) = (x, g(x)) ∈ Y|_U`. Proved:
* `ι` is a section: `π ∘ ι = id` (`proj_observe`);
* if `g` is smooth, then `ι` (composed with `Y|_U ⊆ ℝ¹⁴`) is smooth (`contMDiff_observe`);
* the Minkowski field `g ≡ η` is an observation on every chart (`minkowski`).
-/

namespace GU.Observerse

/-- Observation induced by a metric field `g`, Lorentzian on `U`. -/
def observe (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (g : (Fin 4 → ℝ) → (Fin 10 → ℝ))
    (hg : ∀ x ∈ U, g x ∈ LorFiber) (x : U) : Yloc U :=
  ⟨(x.1, g x.1), x.2, hg x.1 x.2⟩

theorem proj_observe (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (g : (Fin 4 → ℝ) → (Fin 10 → ℝ))
    (hg : ∀ x ∈ U, g x ∈ LorFiber) (x : U) : proj U (observe U g hg x) = x.1 := rfl

/-- Smoothness of the observation, stated for `ι` followed by the inclusion `Y|_U ⊆ ℝ¹⁴` (open
inclusions are local diffeomorphisms; Mathlib lacks the codomain-restriction lemma). -/
theorem contMDiff_observe (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (g : (Fin 4 → ℝ) → (Fin 10 → ℝ))
    (hg : ∀ x ∈ U, g x ∈ LorFiber) (hsmooth : ContDiff ℝ ⊤ g) :
    ContMDiff (modelWithCornersSelf ℝ (Fin 4 → ℝ)) (modelWithCornersSelf ℝ E14) ⊤
      (fun x : U => ((observe U g hg x : Yloc U) : E14)) :=
  ((contDiff_id.prodMk hsmooth).contMDiff).comp contMDiff_subtype_val

/-- The Minkowski field is an observation on every chart. -/
def minkowski (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (x : U) : Yloc U :=
  observe U (fun _ => ηv) (fun _ _ => ηv_mem) x

end GU.Observerse
