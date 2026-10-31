import Mathlib

/-!
# Clifford–Bianchi identities: the algebraic core of the Shiab contraction (9.3)

Setting: a ring `A` (an `ℝ`-algebra) with elements `γ a` satisfying the Clifford relations
`γ_a γ_b + γ_b γ_a = 2 w_a δ_ab` for weights `w_a = ±1` (any signature, any dimension `n`).

Main results:
* `three_gamma`: if `c_{bcd}` is antisymmetric in `(c,d)` and satisfies the cyclic Bianchi
  identity, then `Σ c_{bcd} γ_b γ_c γ_d = -2 Σ_{b,c} w_b c_{bcb} γ_c`. This is the 3-gamma
  identity behind the Lichnerowicz formula.
* `comm_term`: `Σ_{a,c,d} c_{acd} [γ_a, γ_c γ_d] = 4 Σ_{a,c} w_a c_{aca} γ_c`.
* `anticomm_term_zero`: under Bianchi, `Σ_{a,c,d} c_{acd} {γ_a, γ_c γ_d} = 0`.

For a curvature tensor this explains the numerical finding (experiments/shiab_weyl.py): the
Ricci-like term of (9.3) is a Ricci contraction with the commutator, and vanishes identically
with the anticommutator. Weyl annihilation follows because only the trace `c_{aca}` survives.
-/

namespace GU.CliffordBianchi

open Finset

variable {A : Type*} [Ring A] [Algebra ℝ A] {n : ℕ} (w : Fin n → ℝ) (γ : Fin n → A)

/-- `δ a b = 2 w_a` if `a = b`, else `0`. -/
def δ (a b : Fin n) : ℝ := if a = b then 2 * w a else 0

lemma δ_comm (a b : Fin n) : δ w a b = δ w b a := by
  unfold δ; by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- Clifford relations. -/
def IsClifford : Prop := ∀ a b, γ a * γ b + γ b * γ a = δ w a b • (1 : A)

variable {w γ}

lemma swap (h : IsClifford w γ) (a b : Fin n) : γ a * γ b = δ w a b • (1 : A) - γ b * γ a := by
  rw [← h a b]; abel

/-- `γ_d γ_b γ_c = γ_b γ_c γ_d − δ_cd γ_b + δ_bd γ_c`. -/
lemma move_left (h : IsClifford w γ) (b c d : Fin n) :
    γ d * γ b * γ c = γ b * γ c * γ d - δ w c d • γ b + δ w b d • γ c := by
  rw [swap h d b, sub_mul, smul_mul_assoc, one_mul, mul_assoc, swap h d c, mul_sub,
    mul_smul_comm, mul_one, δ_comm w d b, δ_comm w d c]
  simp only [mul_assoc]; abel

/-- `γ_c γ_d γ_b = γ_b γ_c γ_d − δ_bc γ_d + δ_bd γ_c`. -/
lemma move_right (h : IsClifford w γ) (b c d : Fin n) :
    γ c * γ d * γ b = γ b * γ c * γ d - δ w b c • γ d + δ w b d • γ c := by
  rw [mul_assoc, swap h d b, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, swap h c b, sub_mul,
    smul_mul_assoc, one_mul, δ_comm w d b, δ_comm w c b]
  simp only [mul_assoc]; abel

/-- Triples as a single index type. -/
abbrev T (n : ℕ) := Fin n × Fin n × Fin n

/-- Cyclic shift `(b,c,d) ↦ (c,d,b)`. -/
def cyc (n : ℕ) : T n ≃ T n where
  toFun t := (t.2.1, t.2.2, t.1)
  invFun t := (t.2.2, t.1, t.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Algebra ℝ A] in
lemma sum_T (F : Fin n → Fin n → Fin n → A) :
    ∑ t : T n, F t.1 t.2.1 t.2.2 = ∑ b, ∑ c, ∑ d, F b c d := by
  rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]

/-- **3-gamma identity.** -/
theorem three_gamma (h : IsClifford w γ) (c : Fin n → Fin n → Fin n → ℝ)
    (anti : ∀ b x y, c b x y = -c b y x)
    (bianchi : ∀ b x y, c b x y + c x y b + c y b x = 0) :
    ∑ b, ∑ x, ∑ y, c b x y • (γ b * γ x * γ y) =
      (-2 : ℝ) • ∑ b, ∑ x, (w b * c b x b) • γ x := by
  set G : T n → A := fun t => γ t.1 * γ t.2.1 * γ t.2.2
  set C : T n → ℝ := fun t => c t.1 t.2.1 t.2.2
  set X := ∑ t : T n, C t • G t
  have hX : X = ∑ b, ∑ x, ∑ y, c b x y • (γ b * γ x * γ y) :=
    sum_T (fun b x y => c b x y • (γ b * γ x * γ y))
  -- Bianchi, summed against G, then relabelled by the cyclic shift.
  have h0 : ∑ t : T n, (C t + C (cyc n t) + C ((cyc n).symm t)) • G t = 0 := by
    refine sum_eq_zero fun t _ => ?_
    have := bianchi t.1 t.2.1 t.2.2
    simp only [C, cyc, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [this, zero_smul]
  have h2 : ∑ t : T n, C (cyc n t) • G t = ∑ t : T n, C t • G ((cyc n).symm t) :=
    (Equiv.sum_comp (cyc n) (fun t => C t • G ((cyc n).symm t))).symm.trans
      (by simp) |>.symm.trans (by simp)
  have h3 : ∑ t : T n, C ((cyc n).symm t) • G t = ∑ t : T n, C t • G (cyc n t) :=
    (Equiv.sum_comp (cyc n).symm (fun t => C t • G (cyc n t))).symm.trans (by simp) |>.symm
  simp only [add_smul, sum_add_distrib, h2, h3] at h0
  -- Reorder the cyclically shifted products.
  have hG : ∀ t : T n, G ((cyc n).symm t) + G (cyc n t) =
      (2 : ℝ) • G t - δ w t.2.1 t.2.2 • γ t.1 + (2 : ℝ) • (δ w t.1 t.2.2 • γ t.2.1)
        - δ w t.1 t.2.1 • γ t.2.2 := by
    intro t
    simp only [G, cyc, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [move_left h t.1 t.2.1 t.2.2, move_right h t.1 t.2.1 t.2.2, two_smul, two_smul]; abel
  have h0' : (3 : ℝ) • X - ∑ t : T n, C t • (δ w t.2.1 t.2.2 • γ t.1)
      + (2 : ℝ) • ∑ t : T n, C t • (δ w t.1 t.2.2 • γ t.2.1)
      - ∑ t : T n, C t • (δ w t.1 t.2.1 • γ t.2.2) = 0 := by
    rw [← h0, add_assoc, ← sum_add_distrib, ← sum_add_distrib]
    simp only [X, smul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [← smul_add, hG t]
    module
  -- Collapse the δ-sums.
  have e1 : ∑ t : T n, C t • (δ w t.2.1 t.2.2 • γ t.1) = 0 := by
    rw [sum_T (fun b x y => c b x y • (δ w x y • γ b))]
    refine sum_eq_zero fun b _ => ?_
    simp only [δ, ite_smul, zero_smul, smul_ite, smul_zero, sum_ite_eq, mem_univ, ite_true]
    refine sum_eq_zero fun x _ => ?_
    have : c b x x = 0 := by linarith [anti b x x]
    rw [this, zero_smul]
  have e2 : ∑ t : T n, C t • (δ w t.1 t.2.2 • γ t.2.1) = ∑ b, ∑ x, (2 * (w b * c b x b)) • γ x := by
    rw [sum_T (fun b x y => c b x y • (δ w b y • γ x))]
    refine sum_congr rfl fun b _ => sum_congr rfl fun x _ => ?_
    simp only [δ, ite_smul, zero_smul, smul_ite, smul_zero, sum_ite_eq, mem_univ, ite_true, smul_smul]
    congr 1; ring
  have e3 : ∑ t : T n, C t • (δ w t.1 t.2.1 • γ t.2.2) = -∑ b, ∑ x, (2 * (w b * c b x b)) • γ x := by
    rw [sum_T (fun b x y => c b x y • (δ w b x • γ y)), ← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single b]
    · rw [← sum_neg_distrib]
      refine sum_congr rfl fun y _ => ?_
      simp only [δ, ite_true, smul_smul]
      rw [anti b b y, ← neg_smul]; congr 1; ring
    · intro x _ hx
      refine sum_eq_zero fun y _ => ?_
      simp [δ, Ne.symm hx]
    · simp
  rw [e1, e2, e3] at h0'
  rw [← hX]
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have key : (3 : ℝ) • X = (3 : ℝ) • ((-2 : ℝ) • ∑ b, ∑ x, (w b * c b x b) • γ x) := by
    have e : ∑ b, ∑ x, (2 * (w b * c b x b)) • γ x = (2 : ℝ) • ∑ b, ∑ x, (w b * c b x b) • γ x := by
      simp only [smul_sum, smul_smul]
    rw [e] at h0'
    rw [← sub_eq_zero, ← h0']
    module
  exact smul_right_injective A h3ne key

lemma comm3 (h : IsClifford w γ) (a x y : Fin n) :
    γ a * (γ x * γ y) - γ x * γ y * γ a = δ w a x • γ y - δ w a y • γ x := by
  rw [move_right h a x y, ← mul_assoc]; abel

/-- Commutator contraction (Ricci-like term of (9.3)). -/
theorem comm_term (h : IsClifford w γ) (c : Fin n → Fin n → Fin n → ℝ)
    (anti : ∀ b x y, c b x y = -c b y x) :
    ∑ a, ∑ x, ∑ y, c a x y • (γ a * (γ x * γ y) - γ x * γ y * γ a) =
      (-4 : ℝ) • ∑ a, ∑ y, (w a * c a y a) • γ y := by
  simp only [comm3 h, smul_sub, sum_sub_distrib, smul_sum]
  have e1 : ∑ a, ∑ x, ∑ y, c a x y • δ w a x • γ y = ∑ a, ∑ y, (2 * w a * c a a y) • γ y := by
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun x _ hx => sum_eq_zero fun y _ => by simp [δ, Ne.symm hx])
      (by simp)]
    refine sum_congr rfl fun y _ => ?_
    simp only [δ, ite_true, smul_smul]; congr 1; ring
  have e2 : ∑ a, ∑ x, ∑ y, c a x y • δ w a y • γ x = ∑ a, ∑ x, (2 * w a * c a x a) • γ x := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single a (fun y _ hy => by simp [δ, Ne.symm hy]) (by simp)]
    simp only [δ, ite_true, smul_smul]; congr 1; ring
  rw [e1, e2, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [anti a a y, smul_smul, ← sub_smul]; congr 1; ring

/-- Anticommutator contraction vanishes under Bianchi. -/
theorem anticomm_term_zero (h : IsClifford w γ) (c : Fin n → Fin n → Fin n → ℝ)
    (anti : ∀ b x y, c b x y = -c b y x)
    (bianchi : ∀ b x y, c b x y + c x y b + c y b x = 0) :
    ∑ a, ∑ x, ∑ y, c a x y • (γ a * (γ x * γ y) + γ x * γ y * γ a) = 0 := by
  have e : ∀ a x y, γ a * (γ x * γ y) + γ x * γ y * γ a
      = (2 : ℝ) • (γ a * γ x * γ y) - (γ a * (γ x * γ y) - γ x * γ y * γ a) := by
    intro a x y; rw [two_smul]; simp only [mul_assoc]; abel
  calc ∑ a, ∑ x, ∑ y, c a x y • (γ a * (γ x * γ y) + γ x * γ y * γ a)
      = ∑ a, ∑ x, ∑ y, ((2 : ℝ) • (c a x y • (γ a * γ x * γ y))
          - c a x y • (γ a * (γ x * γ y) - γ x * γ y * γ a)) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        rw [e, smul_sub, smul_comm]
    _ = (2 : ℝ) • ∑ a, ∑ x, ∑ y, c a x y • (γ a * γ x * γ y)
          - ∑ a, ∑ x, ∑ y, c a x y • (γ a * (γ x * γ y) - γ x * γ y * γ a) := by
        simp only [sum_sub_distrib, smul_sum]
    _ = 0 := by
        rw [comm_term h c anti, three_gamma h c anti bianchi, smul_smul, sub_eq_zero]; norm_num

/-! ### Curvature tensors -/

/-- Algebraic curvature tensor (all indices down). -/
structure AlgCurv (R : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop where
  anti12 : ∀ a b c d, R a b c d = -R b a c d
  anti34 : ∀ a b c d, R a b c d = -R a b d c
  pair : ∀ a b c d, R a b c d = R c d a b
  bianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0

variable (w) in
/-- Ricci tensor `Ric_bd = Σ_a w_a R_abad` (`w_a = η^{aa}`). -/
def ric (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b d : Fin n) : ℝ := ∑ a, w a * R a b a d

variable (w) in
/-- Scalar curvature `Σ_b w_b Ric_bb`. -/
def scal (R : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ := ∑ b, w b * ric w R b b

/-- **Ricci term of (9.3)** with the commutator: for fixed form index `b`,
`Σ_{a,x,y} w_a w_x w_y R_abxy [γ_a, γ_x γ_y] = 4 Σ_y w_y Ric_by γ_y`. -/
theorem ricci_term (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1) {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : AlgCurv R) (b : Fin n) :
    ∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) - γ x * γ y * γ a) =
      (4 : ℝ) • ∑ y, (w y * ric w R b y) • γ y := by
  rw [comm_term h _ (fun a x y => by rw [hR.anti34 a b x y]; ring)]
  rw [sum_comm, smul_sum, smul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_smul, smul_smul, smul_smul, ric, mul_sum, mul_sum, mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [hR.anti34 a b y a]
  have := hw a
  calc -4 * (w a * (w a * w y * w a * -R a b a y)) = 4 * (w y * (w a * R a b a y)) * (w a * w a) := by ring
    _ = 4 * (w y * (w a * R a b a y)) := by rw [this]; ring

/-- **Weyl annihilation:** the Ricci term vanishes on Ricci-flat (in particular pure Weyl)
curvature. -/
theorem ricci_term_weyl (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) (hRic : ∀ b d, ric w R b d = 0)
    (b : Fin n) :
    ∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) - γ x * γ y * γ a) = 0 := by
  rw [ricci_term h hw hR b]; simp [hRic]

/-- With the anticommutator the Ricci-like term vanishes identically (first Bianchi identity). -/
theorem ricci_term_anticomm (h : IsClifford w γ) {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : AlgCurv R) (b : Fin n) :
    ∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) + γ x * γ y * γ a) = 0 :=
  anticomm_term_zero h _ (fun a x y => by rw [hR.anti34 a b x y]; ring) (fun a x y => by
    have := hR.bianchi b a x y
    rw [hR.anti12 a b x y, hR.anti12 x b y a, hR.anti12 y b a x]
    linear_combination (-(w a * w x * w y)) * this)

lemma ric_symm {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) (b d : Fin n) :
    ric w R b d = ric w R d b := by
  unfold ric; exact sum_congr rfl fun a _ => by rw [hR.pair a b a d]

/-- Symmetric contraction: `Σ s_ax γ_a γ_x = Σ_a w_a s_aa` for symmetric `s`. -/
lemma sym_contract (h : IsClifford w γ) (s : Fin n → Fin n → ℝ) (hs : ∀ a x, s a x = s x a) :
    ∑ a, ∑ x, s a x • (γ a * γ x) = (∑ a, w a * s a a) • (1 : A) := by
  have h2 : (2 : ℝ) • ∑ a, ∑ x, s a x • (γ a * γ x) = ∑ a, ∑ x, (s a x * δ w a x) • (1 : A) := by
    rw [two_smul]
    conv_lhs => arg 2; rw [sum_comm]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [hs x a, ← smul_add, h a x, smul_smul]
  have h3 : ∑ a, ∑ x, (s a x * δ w a x) • (1 : A) = (2 : ℝ) • (∑ a, w a * s a a) • (1 : A) := by
    rw [smul_smul, mul_sum, sum_smul]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [δ, Ne.symm hx]) (by simp)]
    simp only [δ, ite_true]; congr 1; ring
  exact smul_right_injective A (two_ne_zero (α := ℝ)) (h2.trans h3)

/-- **Lichnerowicz identity** (scalar core of (9.3)):
`Σ w_a w_b w_x w_y R_abxy γ_a γ_b γ_x γ_y = -2 · scal`. -/
theorem lichnerowicz (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) :
    ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ a * γ b * γ x * γ y) =
      (-2 * scal w R) • (1 : A) := by
  have inner : ∀ a, ∑ b, ∑ x, ∑ y, (w b * w x * w y * R a b x y) • (γ b * γ x * γ y) =
      (-2 : ℝ) • ∑ x, (w x * ric w R a x) • γ x := by
    intro a
    rw [three_gamma h (fun b x y => w b * w x * w y * R a b x y)
      (fun b x y => by rw [hR.anti34 a b x y]; ring)
      (fun b x y => by linear_combination (w b * w x * w y) * hR.bianchi a b x y)]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_smul, ric, mul_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    have e : R a b x b = R b a b x := by
      rw [hR.anti34 a b x b, hR.anti12 a b b x]; ring
    rw [e]
    linear_combination (w x * R b a b x * w b) * hw b
  calc ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ a * γ b * γ x * γ y)
      = ∑ a, (w a) • (γ a * ∑ b, ∑ x, ∑ y, (w b * w x * w y * R a b x y) • (γ b * γ x * γ y)) := by
        refine sum_congr rfl fun a _ => ?_
        simp only [mul_sum, smul_sum, mul_smul_comm, smul_smul]
        refine sum_congr rfl fun b _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        simp only [mul_assoc]
    _ = (-2 : ℝ) • ∑ a, ∑ x, (w a * (w x * ric w R a x)) • (γ a * γ x) := by
        simp only [inner, mul_smul_comm, mul_sum, smul_sum, smul_smul]
        refine sum_congr rfl fun a _ => sum_congr rfl fun x _ => ?_
        congr 1; ring
    _ = (-2 * scal w R) • (1 : A) := by
        rw [sym_contract h _ (fun a x => by rw [ric_symm hR a x]; ring), smul_smul, scal]
        congr 1; rw [mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        linear_combination (-2 * ric w R a a * w a) * hw a

omit [Algebra ℝ A] in
lemma sum4_swap (F : Fin n → Fin n → Fin n → Fin n → A) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ a, ∑ b, F a b x y := by
  have e1 : ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, F p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  have e2 : ∑ x, ∑ y, ∑ a, ∑ b, F a b x y = ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, F p.1 p.2 q.1 q.2 := by
    simp only [Fintype.sum_prod_type]
  rw [e1, e2, Finset.sum_comm]

/-- **Scalar term of (9.3)** with anticommutators: `Σ coef {γ_aγ_b, γ_xγ_y} = -4 · scal`. -/
theorem scalar_term_anticomm (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) :
    ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) •
      (γ a * γ b * (γ x * γ y) + γ x * γ y * (γ a * γ b)) = (-4 * scal w R) • (1 : A) := by
  have L := lichnerowicz h hw hR
  have swap2 : ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ x * γ y * (γ a * γ b))
      = ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ a * γ b * γ x * γ y) := by
    rw [sum4_swap]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun a _ =>
      sum_congr rfl fun b _ => ?_
    rw [hR.pair a b x y, ← mul_assoc]; congr 1; ring
  have assoc : ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ a * γ b * (γ x * γ y))
      = ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) • (γ a * γ b * γ x * γ y) := by
    simp only [mul_assoc]
  simp only [smul_add, sum_add_distrib]
  rw [assoc, swap2, L, ← add_smul]; congr 1; ring

/-- With the commutator the scalar term vanishes identically (pair symmetry). -/
theorem scalar_term_comm {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) :
    ∑ a, ∑ b, ∑ x, ∑ y, (w a * w b * w x * w y * R a b x y) •
      (γ a * γ b * (γ x * γ y) - γ x * γ y * (γ a * γ b)) = 0 := by
  simp only [smul_sub, sum_sub_distrib, sub_eq_zero]
  rw [sum4_swap (fun a b x y => (w a * w b * w x * w y * R a b x y) • (γ x * γ y * (γ a * γ b)))]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun x _ =>
    sum_congr rfl fun y _ => ?_
  rw [hR.pair x y a b]; congr 1; ring

end GU.CliffordBianchi
