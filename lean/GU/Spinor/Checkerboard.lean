import GU.Spinor.Dirac

/-!
# The Clifford checkerboard (3.26)–(3.27), proved for all monomials (draft footnote 3)

For any list `L` of *distinct* generators with product `γ_L`:
* `transpose_C`: `γ_Lᵀ C = (−1)^|L| C γ_{reverse L}` (move `C` through each `γ_aᵀ C = −C γ_a`);
* `reverse_prod`: `γ_{reverse L} = (−1)^{|L|(|L|−1)/2} γ_L` (distinct gammas anticommute);
* `checkerboard`: `γ_Lᵀ C = ε C γ_L` with `ε = (−1)^{k + k(k−1)/2}`, `k = |L|`;
* `eps_table`: for `k ≤ 14`, `ε = −1` iff `k ≡ 1, 2 (mod 4)`.

Hence `so(C) = so(64,64)` is spanned by grades `1,2,5,6,9,10,13,14` (3.26), and `u(C) = u(64,64)`
adds `i·`(grades `0,3,4,7,8,11,12`) (3.27). The decomposition the draft's footnote 3 asked to be
checked is correct.
-/

namespace GU.Spinor

open Matrix

lemma gamma_transpose_C (g : Gen) : (gamma g)ᵀ * C = -(C * gamma g) := by
  rw [C_gamma]; simp

theorem transpose_C (L : List Gen) :
    ((L.map gamma).prod)ᵀ * C = ((-1 : ℝ) ^ L.length) • (C * ((L.map gamma).reverse).prod) := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons, List.prod_cons, transpose_mul, List.reverse_cons, List.prod_append,
      List.prod_nil, Matrix.mul_one, List.length_cons, pow_succ]
    rw [Matrix.mul_assoc, gamma_transpose_C, Matrix.mul_neg, ← Matrix.mul_assoc, ih,
      Matrix.smul_mul, Matrix.mul_assoc, mul_neg_one, neg_smul]

lemma prod_mul_gamma (L : List Gen) (g : Gen) (hg : g ∉ L) :
    (L.map gamma).prod * gamma g = ((-1 : ℝ) ^ L.length) • (gamma g * (L.map gamma).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hga : g ≠ a := fun h => hg (h ▸ List.mem_cons_self ..)
    have hgL : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hac : gamma a * gamma g = -(gamma g * gamma a) := by
      rw [gamma_comm, sgn_prod_of_ne a g (Ne.symm hga)]; simp
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [Matrix.mul_assoc, ih hgL, Matrix.mul_smul, ← Matrix.mul_assoc, hac, Matrix.neg_mul,
      smul_neg, ← neg_smul, mul_neg_one, Matrix.mul_assoc]

theorem reverse_prod (L : List Gen) (hL : L.Nodup) :
    ((L.map gamma).reverse).prod = ((-1 : ℝ) ^ (L.length * (L.length - 1) / 2)) • (L.map gamma).prod := by
  induction L with
  | nil => simp
  | cons g L ih =>
    obtain ⟨hg, hL'⟩ := List.nodup_cons.mp hL
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      Matrix.mul_one, List.length_cons]
    rw [ih hL', Matrix.smul_mul, prod_mul_gamma L g hg, smul_smul, ← pow_add]
    congr 2
    generalize L.length = n
    rw [Nat.add_sub_cancel]
    cases n with
    | zero => rfl
    | succ k =>
      rw [show (k + 1 + 1) * (k + 1) = (k + 1) * (k + 1 - 1) + (k + 1) * 2 by
        rw [Nat.add_sub_cancel]; ring, Nat.add_mul_div_right _ _ (by norm_num)]

/-- `ε_k = (−1)^{k + k(k−1)/2}`. -/
def epsR (k : ℕ) : ℝ := (-1) ^ (k + k * (k - 1) / 2)

theorem checkerboard (L : List Gen) (hL : L.Nodup) :
    ((L.map gamma).prod)ᵀ * C = epsR L.length • (C * (L.map gamma).prod) := by
  rw [transpose_C, reverse_prod L hL, Matrix.mul_smul, smul_smul, ← pow_add, epsR]

/-- Mod-4 pattern for all grades `k ≤ 14`. -/
theorem eps_table : ∀ k ∈ List.range 15,
    (k + k * (k - 1) / 2) % 2 = if k % 4 = 1 ∨ k % 4 = 2 then 1 else 0 := by decide

end GU.Spinor
