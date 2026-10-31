import Mathlib

/-!
# The Einsteinian observerse `Y = Met(X⁴)` as a 14-manifold (draft §3, Def. 3.1)

Locally `X⁴ ⊇ U` is an open subset of `ℝ⁴`, and `Y|_U = U × Met_Lor(ℝ⁴)`. Symmetric 4×4
matrices have 10 coordinates `v : Fin 10 → ℝ` (`symMat`). The Lorentzian fiber is
`{v | det(symMat v) < 0}`: the nondegenerate metrics with an odd number of negative eigenvalues,
i.e. signatures (1,3) and (3,1). The draft treats these as mirror images (§3.5).

Proved: the fiber is open and nonempty (it contains `η`), `Y|_U` is an open subset of `ℝ^{4+10}`,
hence a smooth boundaryless manifold modelled on a 14-dimensional space, and `π : Y → X`
is smooth.

-- AI_BREAKTHROUGH_PATCH_V1 (synthetic choice): the fiber is the union of the (1,3) and (3,1)
sectors rather than (1,3) alone. Separating them needs an eigenvalue/inertia argument; the
union is the open condition `det < 0`.
-/

namespace GU.Observerse

open Matrix

/-- Index of the `(i,j)` entry of a symmetric 4×4 matrix among its 10 independent entries. -/
def symIdx : Fin 4 → Fin 4 → Fin 10 :=
  ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 5, 7, 8], ![3, 6, 8, 9]]

lemma symIdx_symm (i j : Fin 4) : symIdx i j = symIdx j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Symmetric matrix with coordinates `v`. -/
def symMat (v : Fin 10 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => v (symIdx i j)

lemma symMat_isSymm (v : Fin 10 → ℝ) : (symMat v).IsSymm := by
  ext i j; simp [symMat, symIdx_symm]

lemma continuous_symMat : Continuous symMat :=
  continuous_pi fun i => continuous_pi fun j => continuous_apply (symIdx i j)

/-- The Lorentzian fiber `GL(4)/O(1,3) ∪ GL(4)/O(3,1)`. -/
def LorFiber : Set (Fin 10 → ℝ) := {v | (symMat v).det < 0}

theorem isOpen_LorFiber : IsOpen LorFiber :=
  isOpen_lt (continuous_symMat.matrix_det) continuous_const

/-- Coordinates of `η = diag(1,-1,-1,-1)`. -/
def ηv : Fin 10 → ℝ := ![1, 0, 0, 0, -1, 0, 0, -1, 0, -1]

theorem ηv_mem : ηv ∈ LorFiber := by
  have : symMat ηv = diagonal ![1, -1, -1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symMat, symIdx, ηv]
  show (symMat ηv).det < 0
  rw [this, det_diagonal, Fin.prod_univ_four]; norm_num

/-- Model space `ℝ⁴ × ℝ¹⁰` of the observerse. -/
abbrev E14 := (Fin 4 → ℝ) × (Fin 10 → ℝ)

theorem finrank_E14 : Module.finrank ℝ E14 = 14 := by simp

/-- `Y` over an open chart `U ⊆ ℝ⁴`. -/
def Yloc (U : TopologicalSpace.Opens (Fin 4 → ℝ)) : TopologicalSpace.Opens E14 :=
  ⟨U ×ˢ LorFiber, U.isOpen.prod isOpen_LorFiber⟩

/-- `Y|_U` is a smooth 14-manifold. -/
example (U : TopologicalSpace.Opens (Fin 4 → ℝ)) :
    IsManifold (modelWithCornersSelf ℝ E14) ⊤ (Yloc U) := inferInstance

/-- The projection `π : Y → X`, landing in the chart `U`. -/
def proj (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (y : Yloc U) : Fin 4 → ℝ := y.1.1

theorem proj_mem (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (y : Yloc U) : proj U y ∈ U := y.2.1

theorem contMDiff_proj (U : TopologicalSpace.Opens (Fin 4 → ℝ)) :
    ContMDiff (modelWithCornersSelf ℝ E14) (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ⊤ (proj U) :=
  (contDiff_fst.contMDiff).comp contMDiff_subtype_val

/-- The fiber over a point contains the Minkowski metric, so `π` is onto `U`. -/
theorem proj_surjective (U : TopologicalSpace.Opens (Fin 4 → ℝ)) (x : Fin 4 → ℝ) (hx : x ∈ U) :
    ∃ y : Yloc U, proj U y = x := ⟨⟨(x, ηv), hx, ηv_mem⟩, rfl⟩

end GU.Observerse
