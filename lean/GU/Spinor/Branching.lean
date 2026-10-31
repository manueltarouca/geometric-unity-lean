import GU.Spinor.Pauli
import GU.Spinor.Dirac

/-!
# Branching rule (12.20): chirality on `Y` factorises over `TX ⊕ N`

Under observation `ℷ*(TY) = TX^{1,3} ⊕ N^{6,4}` (12.19). We split the 14 generators into a
(1,3) block `gens4` and a (6,4) block `gens10`, with volume elements `ω₄` and `ω₁₀`. Proved:

* `gens4` has signature (1,3) and `gens10` has (6,4) (`sig4`, `sig10`);
* `ω₄` anticommutes with the (1,3) generators and commutes with the (6,4) ones, and vice versa
  for `ω₁₀`. So they are the chirality operators of the two Clifford factors;
* `ω₄² = ω₁₀² = -1`, `ω₄ ω₁₀ = ω₁₀ ω₄`, and **`ω₄ ω₁₀ = Γ`** exactly;
* `tr ω₄ = tr ω₁₀ = tr Γ = 0`.

Over `ℂ`, `J₄ = iω₄` and `J₁₀ = iω₁₀` square to `1` and `J₄ J₁₀ = -Γ`. So the `Γ = +1` (left)
spinors of `Y` are exactly `{J₄ = -J₁₀}` = `(+,−) ⊕ (−,+)`, i.e. `S̸_L(Y) = S̸_±(TX) ⊗ S̸_∓(N)`.
Each joint eigenspace has complex dimension `32 = 2 · 16` (`joint_eigenspace_finrank`),
matching (12.20).
Which pair is called "left" depends on three independent sign conventions `Γ_V = ±(i)ω_V`
(for Y, X and N). This is a sign convention, *not* an orientation: with all signs `+` one gets
`LR ⊕ RL`, and the paper's `LL ⊕ RR` corresponds to flipping one of them.

Not formalised here: the module isomorphism `S̸(Y) ≅ S̸(X) ⊗ S̸(N)` under
`Spin(1,3) × Spin(6,4)`, and invariance of the joint eigenspaces under that subgroup. The
(anti)commutation lemmas below are the ingredients for it.
-/

namespace GU.Spinor

open Matrix

/-- (1,3) block: one `+` and three `−` generators. -/
def gens4 : List Gen := [(0, false), (0, true), (1, true), (2, true)]

/-- (6,4) block: the remaining six `+` and four `−` generators. -/
def gens10 : List Gen :=
  [(1, false), (2, false), (3, false), (4, false), (5, false), (6, false),
   (3, true), (4, true), (5, true), (6, true)]

theorem gens_partition : (gens4 ++ gens10).Perm (List.finRange 7 ×ˢ [false, true]) := by decide

theorem sig4 : (gens4.filter (·.2)).length = 3 ∧ (gens4.filter (! ·.2)).length = 1 := by decide
theorem sig10 : (gens10.filter (·.2)).length = 4 ∧ (gens10.filter (! ·.2)).length = 6 := by decide

/-- Volume element of the (1,3) block. -/
def ω4P : PString := gprod gens4
/-- Volume element of the (6,4) block. -/
def ω10P : PString := gprod gens10
/-- Chirality `σ₃^{⊗7}` as a string. -/
def ΓP : PString := ⟨1, fun _ => .s3⟩

theorem ω4P_sq : ω4P * ω4P = PString.neg PString.one :=
  PString.eq_of_beq (by decide)
theorem ω10P_sq : ω10P * ω10P = PString.neg PString.one :=
  PString.eq_of_beq (by decide)
theorem ω_comm : ω4P * ω10P = ω10P * ω4P :=
  PString.eq_of_beq (by decide)
theorem ω_prod : ω4P * ω10P = ΓP :=
  PString.eq_of_beq (by decide)
theorem ω4P_tr : ω4P.tr = 0 := by decide
theorem ω10P_tr : ω10P.tr = 0 := by decide

private theorem all_beq {L : List Gen} {F G : Gen → PString}
    (h : L.all (fun g => PString.beq (F g) (G g)) = true) : ∀ g ∈ L, F g = G g := by
  intro g hg
  exact PString.eq_of_beq (List.all_eq_true.mp h g hg)

theorem ω4_anticomm_gens4 : ∀ g ∈ gens4, gammaP g * ω4P = PString.neg (ω4P * gammaP g) :=
  all_beq (by decide)
theorem ω4_comm_gens10 : ∀ g ∈ gens10, gammaP g * ω4P = ω4P * gammaP g := all_beq (by decide)
theorem ω10_comm_gens4 : ∀ g ∈ gens4, gammaP g * ω10P = ω10P * gammaP g := all_beq (by decide)
theorem ω10_anticomm_gens10 :
    ∀ g ∈ gens10, gammaP g * ω10P = PString.neg (ω10P * gammaP g) := all_beq (by decide)

/-! ### Matrix statements -/

/-- `ω₄ = γ(0,+) γ(0,−) γ(1,−) γ(2,−)`. -/
def ω4 : M128 := ω4P.toMat
/-- `ω₁₀`, the product of the ten (6,4) generators. -/
def ω10 : M128 := ω10P.toMat

theorem ω4_eq : ω4 = (gens4.map gamma).prod := toMat_gprod _
theorem ω10_eq : ω10 = (gens10.map gamma).prod := toMat_gprod _

theorem ΓP_toMat : ΓP.toMat = Γ := by simp [PString.toMat, ΓP, Γ]

theorem ω4_sq : ω4 * ω4 = -1 := by
  rw [ω4, ← PString.toMat_mul, ω4P_sq, PString.toMat_neg, PString.toMat_one]

theorem ω10_sq : ω10 * ω10 = -1 := by
  rw [ω10, ← PString.toMat_mul, ω10P_sq, PString.toMat_neg, PString.toMat_one]

/-- **(12.20), algebraic core:** the chirality of `Y` is the product of the chiralities of the
(1,3) and (6,4) factors. -/
theorem Γ_factorises : Γ = ω4 * ω10 := by
  rw [ω4, ω10, ← PString.toMat_mul, ω_prod, ΓP_toMat]

theorem ω4_ω10_comm : ω4 * ω10 = ω10 * ω4 := by
  rw [ω4, ω10, ← PString.toMat_mul, ← PString.toMat_mul, ω_comm]

theorem trace_ω4 : trace ω4 = 0 := by rw [ω4, PString.trace_toMat, ω4P_tr]; simp
theorem trace_ω10 : trace ω10 = 0 := by rw [ω10, PString.trace_toMat, ω10P_tr]; simp
theorem trace_Γ : trace Γ = 0 := by
  rw [← ΓP_toMat, PString.trace_toMat]; norm_num [PString.tr, ΓP, F2.trace2]

lemma trace_toC (A : M128) : trace (toC A) = ((trace A : ℝ) : ℂ) := by
  simp only [trace, diag, toC, map_apply, Complex.ofRealHom_eq_coe]
  push_cast; rfl

/-- Trace identity (holds for all `a b`; it counts dimension only for `a, b = ±1`, see
`joint_eigenspace_finrank`). -/
theorem trace_PQ (a b : ℂ) :
    trace ((1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4) *
      ((1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10))) = 32 := by
  have t4 : trace (toC ω4) = 0 := by rw [trace_toC, trace_ω4]; simp
  have t10 : trace (toC ω10) = 0 := by rw [trace_toC, trace_ω10]; simp
  have t410 : trace (toC ω4 * toC ω10) = 0 := by
    rw [← toC_mul, ← Γ_factorises, trace_toC, trace_Γ]; simp
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, trace_smul, trace_add, trace_one, t4, t10, t410, smul_eq_mul,
    Matrix.smul_mul, Matrix.mul_smul, trace_smul]
  simp
  norm_num

lemma toC_ω4_sq : toC ω4 * toC ω4 = -1 := by
  rw [← toC_mul, ω4_sq, toC]; ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

lemma toC_ω10_sq : toC ω10 * toC ω10 = -1 := by
  rw [← toC_mul, ω10_sq, toC]; ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

lemma toC_ω_comm : toC ω4 * toC ω10 = toC ω10 * toC ω4 := by
  rw [← toC_mul, ← toC_mul, ω4_ω10_comm]

/-- `(1 + X)/2` is idempotent when `X² = 1`. -/
lemma half_idem {X : Matrix Idx Idx ℂ} (hX : X * X = 1) :
    IsIdempotentElem ((1 / 2 : ℂ) • (1 + X)) := by
  unfold IsIdempotentElem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hX]
  rw [show (1 : Matrix Idx Idx ℂ) + X + (X + 1) = (2 : ℂ) • (1 + X) by rw [two_smul]; abel, smul_smul]
  norm_num

lemma sq_scaled {X : Matrix Idx Idx ℂ} (hX : X * X = -1) {a : ℂ} (ha : a * a = 1) :
    ((a * Complex.I) • X) * ((a * Complex.I) • X) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX]
  have : a * Complex.I * (a * Complex.I) = -1 := by
    rw [show a * Complex.I * (a * Complex.I) = (a * a) * (Complex.I * Complex.I) by ring, ha,
      Complex.I_mul_I]; ring
  rw [this]; simp

/-- **(12.20), dimension count.** For `a, b ∈ {±1}`, the joint eigenprojector
`P_a Q_b = ((1 + a·iω₄)/2)((1 + b·iω₁₀)/2)` is idempotent and has rank `32 = 2·16`. -/
theorem joint_eigenspace_finrank (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    IsIdempotentElem ((1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4) *
        ((1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10))) ∧
      Module.finrank ℂ (LinearMap.range (Matrix.toLin'
        ((1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4) *
          ((1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10))))) = 32 := by
  set P := (1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4)
  set Q := (1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10)
  have hP : IsIdempotentElem P := half_idem (sq_scaled toC_ω4_sq ha)
  have hQ : IsIdempotentElem Q := half_idem (sq_scaled toC_ω10_sq hb)
  have hPQ : Commute P Q := by
    simp only [P, Q, Commute, SemiconjBy, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_smul, toC_ω_comm]
    module
  have hM : IsIdempotentElem (P * Q) := hP.mul_of_commute hPQ hQ
  refine ⟨hM, ?_⟩
  have hL : IsIdempotentElem (Matrix.toLin' (P * Q)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hM.eq]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hL).trace
  rw [Matrix.trace_toLin'_eq] at this
  have h32 := trace_PQ a b
  rw [show (1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4) * ((1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10))
    = P * Q from rfl, this] at h32
  exact_mod_cast h32

end GU.Spinor
