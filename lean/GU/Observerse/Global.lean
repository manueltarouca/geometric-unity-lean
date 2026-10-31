import GU.Observerse.Manifold

/-!
# The global Einsteinian observerse `Y = Met_Lor(X)` over an arbitrary 4-manifold

For a smooth manifold `X` modelled on `ℝ⁴` (so `T_xX = ℝ⁴` as a vector space), the fiber over `x`
is the set of symmetric bilinear forms on `T_xX` with negative determinant (signatures (1,3) and
(3,1)). The sign of the Gram determinant does not depend on the basis:
`det(Pᵀ g P) = det(P)² det g` (`det_congr_sign`). So `Y` is defined globally (`Yglob`) with
projection `π` onto `X`, and every fiber is in bijection with the chart model `LorFiber`
(`fiberEquiv`, via the symmetric-matrix coordinates).

Not formalised: the smooth/topological structure of `Yglob` and the transformation of the Gram
matrix under chart changes `g ↦ Pᵀ g P`. `det_congr_sign` is exactly the fact that makes the fiber
condition chart-independent; the gluing itself needs Mathlib's hom-bundle machinery and is left open.
-/

namespace GU.Observerse

open Matrix

variable {X : Type*}

/-- Basis-independence of the Lorentzian condition. -/
theorem det_congr_sign (g P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P.det) :
    (Pᵀ * g * P).det < 0 ↔ g.det < 0 := by
  rw [det_mul, det_mul, det_transpose]
  have hpos : 0 < P.det * P.det := mul_self_pos.mpr hP.ne_zero
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Lorentzian symmetric forms on `T_xX = ℝ⁴` (Gram matrix in the standard basis). -/
def LorForms : Set (Matrix (Fin 4) (Fin 4) ℝ) := {g | g.IsSymm ∧ g.det < 0}

/-- The global observerse: pairs `(x, g_x)`. -/
def Yglob (X : Type*) : Type _ := X × LorForms

/-- Projection `π : Y → X`. -/
def piGlob : Yglob X → X := Prod.fst

theorem piGlob_surjective : Function.Surjective (piGlob (X := X)) := by
  intro x
  refine ⟨(x, ⟨diagonal ![1, -1, -1, -1], ?_, ?_⟩), rfl⟩
  · exact (isSymm_diagonal _)
  · rw [det_diagonal, Fin.prod_univ_four]; norm_num

/-- Each fiber of `Y` is identified with the chart model `LorFiber` via `symMat` coordinates. -/
def fiberEquiv : LorFiber ≃ LorForms where
  toFun v := ⟨symMat v.1, symMat_isSymm v.1, v.2⟩
  invFun g := ⟨fun k => g.1 (![0, 0, 0, 0, 1, 1, 1, 2, 2, 3] k) (![0, 1, 2, 3, 1, 2, 3, 2, 3, 3] k), by
    have hg : g.1 = symMat (fun k => g.1 (![0, 0, 0, 0, 1, 1, 1, 2, 2, 3] k) (![0, 1, 2, 3, 1, 2, 3, 2, 3, 3] k)) := by
      ext i j
      have hs := g.2.1
      fin_cases i <;> fin_cases j <;> simp [symMat, symIdx] <;> exact (hs.apply _ _).symm
    show (symMat _).det < 0
    rw [← hg]; exact g.2.2⟩
  left_inv v := by
    ext k; fin_cases k <;> simp [symMat, symIdx]
  right_inv g := by
    ext i j
    have hs := g.2.1
    fin_cases i <;> fin_cases j <;> simp [symMat, symIdx] <;> exact (hs.apply _ _).symm

end GU.Observerse
