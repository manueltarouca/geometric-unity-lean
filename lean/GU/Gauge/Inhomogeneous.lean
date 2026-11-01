/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import Mathlib

/-!
# The inhomogeneous gauge group 𝒢 = 𝓗 ⋉ N (GU draft §5–7), algebraic core

Infinite-dimensional Lie groups are not available in Mathlib (roadblock R9), so we keep only the
algebra the draft actually uses:

* `ad ϖ h`  stands for `h⁻¹ ϖ h`, the right `𝓗`-module structure on `N = Ω¹(Y, ad P_H)`;
* `θ h`     stands for `h⁻¹ (d_{A0} h)`, the Maurer–Cartan form of the base connection `A0`.
  Its only property used anywhere in §6–7 is the cocycle (Leibniz) rule `θ_mul`.

Connections are identified with `N` through `A ↦ A - A0` (draft, remark before (6.2)).

Main results:
* `IG` with the multiplication (5.9) is a group; `tau c` is an injective homomorphism for every
  `c : ℤ` (Lemma 6.1 holds for either sign).
* `rightAct` is a right action (5.10)/(6.2); its stabilizer of `A0` is `tau (-1)` (§6.2).
* `leftAct` is a left action (Lemma 6.4).
* Gap M7 (footnote 7): `pi_mul_tau` / `T_mul_tau` show that, *as printed*, Lemma 6.3 needs
  `c = -1` while Lemmas 6.5 / 7.2 need `c = +1`. `no_common_section` proves no section of any
  form serves both unless `2 • θ = 0`, and `u1_no_common_convention` gives the U(1) model where
  that fails. The defect is a sign slip, not a structural obstruction: `piPlus` (one sign flipped
  in (6.11)) is `τ₊`-invariant, so `τ₊` makes §6.3–7 consistent.
-/

namespace GU

/-- Algebraic shadow of a gauge group acting on ad-valued 1-forms, together with the
Maurer–Cartan form `θ h = h⁻¹ d_{A0} h` of a base connection. -/
structure GaugeData (H N : Type*) [Group H] [AddCommGroup N] where
  /-- `ad ϖ h = h⁻¹ ϖ h`. -/
  ad : N → H → N
  ad_one : ∀ n, ad n 1 = n
  ad_mul : ∀ n a b, ad n (a * b) = ad (ad n a) b
  ad_add : ∀ m n h, ad (m + n) h = ad m h + ad n h
  /-- `θ h = h⁻¹ (d_{A0} h)`. -/
  θ : H → N
  θ_mul : ∀ a b, θ (a * b) = ad (θ a) b + θ b

namespace GaugeData

variable {H N : Type*} [Group H] [AddCommGroup N] (D : GaugeData H N)

/-- `ad · h` as an additive endomorphism. -/
def adHom (h : H) : N →+ N := AddMonoidHom.mk' (fun n => D.ad n h) (fun m n => D.ad_add m n h)

@[simp] lemma adHom_apply (h : H) (n : N) : D.adHom h n = D.ad n h := rfl

@[simp] lemma ad_zero (h : H) : D.ad 0 h = 0 := (D.adHom h).map_zero
@[simp] lemma ad_neg (n : N) (h : H) : D.ad (-n) h = -D.ad n h := (D.adHom h).map_neg n
@[simp] lemma ad_sub (m n : N) (h : H) : D.ad (m - n) h = D.ad m h - D.ad n h :=
  (D.adHom h).map_sub m n
@[simp] lemma ad_zsmul (c : ℤ) (n : N) (h : H) : D.ad (c • n) h = c • D.ad n h :=
  (D.adHom h).map_zsmul c n

@[simp] lemma θ_one : D.θ 1 = 0 := by
  have h := D.θ_mul 1 1
  rw [mul_one, D.ad_one] at h
  simpa using h

lemma ad_ad_inv (n : N) (h : H) : D.ad (D.ad n h) h⁻¹ = n := by
  rw [← D.ad_mul, mul_inv_cancel, D.ad_one]

lemma ad_inv_ad (n : N) (h : H) : D.ad (D.ad n h⁻¹) h = n := by
  rw [← D.ad_mul, inv_mul_cancel, D.ad_one]

lemma ad_eq_zero {n : N} {h : H} (hn : D.ad n h = 0) : n = 0 := by
  rw [← D.ad_ad_inv n h, hn, D.ad_zero]

end GaugeData

/-- Elements `(ε, ϖ)` of the inhomogeneous gauge group `𝒢 = 𝓗 ⋉ N` (Definition 5.1). -/
@[ext]
structure IG {H N : Type*} [Group H] [AddCommGroup N] (D : GaugeData H N) where
  ε : H
  ϖ : N

namespace IG

variable {H N : Type*} [Group H] [AddCommGroup N] {D : GaugeData H N}

/-- (5.9): `(ε₁, ϖ₁)(ε₂, ϖ₂) = (ε₁ε₂, ε₂⁻¹ϖ₁ε₂ + ϖ₂)`. -/
instance : Mul (IG D) := ⟨fun g k => ⟨g.ε * k.ε, D.ad g.ϖ k.ε + k.ϖ⟩⟩
instance : One (IG D) := ⟨⟨1, 0⟩⟩
instance : Inv (IG D) := ⟨fun g => ⟨g.ε⁻¹, -D.ad g.ϖ g.ε⁻¹⟩⟩

@[simp] lemma mul_ε (g k : IG D) : (g * k).ε = g.ε * k.ε := rfl
@[simp] lemma mul_ϖ (g k : IG D) : (g * k).ϖ = D.ad g.ϖ k.ε + k.ϖ := rfl
@[simp] lemma one_ε : (1 : IG D).ε = 1 := rfl
@[simp] lemma one_ϖ : (1 : IG D).ϖ = 0 := rfl
@[simp] lemma inv_ε (g : IG D) : g⁻¹.ε = g.ε⁻¹ := rfl
@[simp] lemma inv_ϖ (g : IG D) : g⁻¹.ϖ = -D.ad g.ϖ g.ε⁻¹ := rfl

instance : Group (IG D) where
  mul_assoc a b c := by ext <;> simp [mul_assoc, D.ad_add, D.ad_mul, add_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp [D.ad_one]
  inv_mul_cancel a := by ext <;> simp [D.ad_inv_ad]

end IG

namespace GaugeData

variable {H N : Type*} [Group H] [AddCommGroup N] (D : GaugeData H N)

/-- The tilted map with sign convention `c`: `τ_c(h) = (h, c · h⁻¹ d_{A0} h)`.
The draft's (6.4) is `c = -1`; the proofs of (6.20) and (7.4) silently use `c = +1`. -/
def tau (c : ℤ) : H →* IG D where
  toFun h := ⟨h, c • D.θ h⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [D.θ_mul, smul_add]

@[simp] lemma tau_ε (c : ℤ) (h : H) : (D.tau c h).ε = h := rfl
@[simp] lemma tau_ϖ (c : ℤ) (h : H) : (D.tau c h).ϖ = c • D.θ h := rfl

/-- Lemma 6.1 (for either sign): `τ_c` is an injective group homomorphism. -/
theorem tau_injective (c : ℤ) : Function.Injective (D.tau c) := fun a b h => by
  simpa using congrArg IG.ε h

/-- Ordinary gauge action on connections (offsets from `A0`): `A0 + α ↦ ε⁻¹(A0 + α)ε`. -/
def gauge (α : N) (ε : H) : N := D.ad α ε + D.θ ε

/-- (5.10)/(6.2): right action of `𝒢` on connections, `A · (ε, ϖ) = A · ε + ϖ`. -/
def rightAct (α : N) (g : IG D) : N := D.gauge α g.ε + g.ϖ

theorem rightAct_one (α : N) : D.rightAct α 1 = α := by
  simp [rightAct, gauge, D.ad_one]

theorem rightAct_mul (α : N) (g k : IG D) :
    D.rightAct α (g * k) = D.rightAct (D.rightAct α g) k := by
  simp only [rightAct, gauge, IG.mul_ε, IG.mul_ϖ, D.θ_mul, D.ad_mul, D.ad_add]
  abel

/-- §6.2: the stabilizer of the base connection `A0` (offset `0`) is exactly `τ₋(𝓗)`. -/
theorem stabilizer_eq_range_tau_neg (g : IG D) :
    D.rightAct 0 g = 0 ↔ g ∈ (D.tau (-1)).range := by
  constructor
  · intro hg
    refine ⟨g.ε, ?_⟩
    ext
    · rfl
    · simp only [rightAct, gauge, ad_zero, zero_add] at hg
      simp [eq_neg_of_add_eq_zero_right hg]
  · rintro ⟨h, rfl⟩
    simp [rightAct, gauge]

/-- (6.11): `π_{A0}(ε, ϖ) = ε ϖ ε⁻¹ + (d_{A0} ε) ε⁻¹`, written as `ad (ϖ + θ ε) ε⁻¹`. -/
def pi (g : IG D) : N := D.ad (g.ϖ + D.θ g.ε) g.ε⁻¹

/-- (7.3): augmented torsion `T(ε, ϖ) = ϖ - ε⁻¹ d_{A0} ε`. -/
def T (g : IG D) : N := g.ϖ - D.θ g.ε

/-- Lemma 6.5: bi-connection map, as offsets `(A_ω - A0, B_ω - A0)`. -/
def mu (g : IG D) : N × N := (g.ϖ, D.θ g.ε)

lemma ad_ad_mul_inv (x : N) (ε h : H) : D.ad (D.ad x h) (ε * h)⁻¹ = D.ad x ε⁻¹ := by
  rw [mul_inv_rev, ← D.ad_mul, mul_inv_cancel_left]

/-- How `π_{A0}` transforms under right multiplication by `τ_c(h)`. -/
theorem pi_mul_tau (c : ℤ) (g : IG D) (h : H) :
    D.pi (g * D.tau c h) = D.pi g + D.ad ((c + 1) • D.θ h) (g.ε * h)⁻¹ := by
  have key : D.ad g.ϖ h + c • D.θ h + D.θ (g.ε * h)
      = D.ad (g.ϖ + D.θ g.ε) h + (c + 1) • D.θ h := by
    rw [D.θ_mul, D.ad_add, add_smul, one_smul]; abel
  simp only [pi, IG.mul_ε, IG.mul_ϖ, tau_ε, tau_ϖ]
  rw [key, D.ad_add, D.ad_ad_mul_inv]

/-- How the augmented torsion transforms under right multiplication by `τ_c(h)`. -/
theorem T_mul_tau (c : ℤ) (g : IG D) (h : H) :
    D.T (g * D.tau c h) = D.ad (D.T g) h + (c - 1) • D.θ h := by
  simp only [T, IG.mul_ε, IG.mul_ϖ, tau_ε, tau_ϖ, D.θ_mul, D.ad_sub, sub_smul, one_smul]
  abel

/-- Lemma 6.3 holds for the stabilizer convention `c = -1`. -/
theorem pi_invariant_tau_neg (g : IG D) (h : H) : D.pi (g * D.tau (-1) h) = D.pi g := by
  simp [pi_mul_tau]

/-- Lemma 7.2 holds for the convention `c = +1`. -/
theorem T_equivariant_tau_pos (g : IG D) (h : H) :
    D.T (g * D.tau 1 h) = D.ad (D.T g) h := by
  simp [T_mul_tau]

/-- Lemma 6.5 holds for the convention `c = +1`: both components of `μ` gauge-transform. -/
theorem mu_equivariant_tau_pos (g : IG D) (h : H) :
    D.mu (g * D.tau 1 h) = (D.gauge (D.mu g).1 h, D.gauge (D.mu g).2 h) := by
  simp [mu, gauge, D.θ_mul]

/-- Lemma 7.2 fails for the stabilizer convention: torsion picks up `-2 θ h`. -/
theorem T_mul_tau_neg (g : IG D) (h : H) :
    D.T (g * D.tau (-1) h) = D.ad (D.T g) h - (2 : ℤ) • D.θ h := by
  rw [T_mul_tau]; simp only [sub_eq_add_neg, ← neg_smul]; norm_num

/-- **Gap M7, formalised (general form).** Let `s` be *any* candidate section `h ↦ (h, s h)`.
Lemma 6.3 at `g = 1` forces `s = -θ`, and Lemma 7.2 at `g = 1` forces `s = +θ`, so `2 θ = 0`. -/
theorem no_common_section (s : H → N)
    (hπ : ∀ h, D.pi (⟨h, s h⟩ : IG D) = D.pi 1)
    (hT : ∀ h, D.T (⟨h, s h⟩ : IG D) = D.ad (D.T 1) h) (h : H) :
    (2 : ℤ) • D.θ h = 0 := by
  have h1 : s h + D.θ h = 0 := by
    have := hπ h
    simp only [pi, IG.one_ϖ, IG.one_ε, θ_one, add_zero, inv_one, D.ad_one] at this
    exact D.ad_eq_zero this
  have h2 : s h - D.θ h = 0 := by
    have := hT h
    simpa [T] using this
  have : (2 : ℤ) • D.θ h = (s h + D.θ h) - (s h - D.θ h) := by rw [two_smul]; abel
  rw [this, h1, h2, sub_zero]

/-- Special case for the tilted maps `τ_c`. -/
theorem no_common_convention (c : ℤ)
    (hπ : ∀ (g : IG D) h, D.pi (g * D.tau c h) = D.pi g)
    (hT : ∀ (g : IG D) h, D.T (g * D.tau c h) = D.ad (D.T g) h) (h : H) :
    (2 : ℤ) • D.θ h = 0 :=
  D.no_common_section (fun h => c • D.θ h)
    (fun h => by have := hπ 1 h; rw [one_mul] at this; exact this)
    (fun h => by have := hT 1 h; rw [one_mul] at this; exact this) h

/-- **One-sign repair** (found in independent review). Replacing `+ (dε)ε⁻¹` by `- (dε)ε⁻¹` in
(6.11) gives `π⁺(g) = ε T_g ε⁻¹`. This is invariant under `τ₊`, the same convention under which
Lemmas 6.5 and 7.2 hold. The price: the fibres of `π⁺` are `τ₊(𝓗)`-orbits, while the stabilizer
of `A0` (§6.2) remains `τ₋(𝓗)`. -/
def piPlus (g : IG D) : N := D.ad (D.T g) g.ε⁻¹

theorem piPlus_invariant_tau_pos (g : IG D) (h : H) :
    D.piPlus (g * D.tau 1 h) = D.piPlus g := by
  simp only [piPlus, T_equivariant_tau_pos, IG.mul_ε, tau_ε, ad_ad_mul_inv]

/-- The abelian U(1) model: `𝓗 = ℤ` (multiplicatively), `N = ℤ`, trivial `ad`, `θ = id`. -/
def u1 : GaugeData (Multiplicative ℤ) ℤ where
  ad n _ := n
  ad_one _ := rfl
  ad_mul _ _ _ := rfl
  ad_add _ _ _ := rfl
  θ h := h.toAdd
  θ_mul a b := by simp [toAdd_mul]

/-- In the U(1) model no sign convention makes Lemmas 6.3 and 7.2 hold simultaneously. -/
theorem u1_no_common_convention :
    ¬ ∃ c : ℤ, (∀ (g : IG u1) h, u1.pi (g * u1.tau c h) = u1.pi g) ∧
      (∀ (g : IG u1) h, u1.T (g * u1.tau c h) = u1.ad (u1.T g) h) := by
  rintro ⟨c, hπ, hT⟩
  have := u1.no_common_convention c hπ hT (Multiplicative.ofAdd 1)
  simp [u1] at this

/-- Lemma 6.4: `g · γ = ε(ϖ + γ)ε⁻¹ + (d_{A0}ε)ε⁻¹` is a left action of `𝒢` on `N`. -/
def leftAct (g : IG D) (γ : N) : N := D.ad (g.ϖ + γ + D.θ g.ε) g.ε⁻¹

theorem leftAct_one (γ : N) : D.leftAct 1 γ = γ := by
  simp [leftAct, D.ad_one]

theorem leftAct_mul (g k : IG D) (γ : N) :
    D.leftAct (g * k) γ = D.leftAct g (D.leftAct k γ) := by
  have e : D.ad g.ϖ k.ε + k.ϖ + γ + D.θ (g.ε * k.ε)
      = D.ad (g.ϖ + D.θ g.ε) k.ε + (k.ϖ + γ + D.θ k.ε) := by
    rw [D.θ_mul, D.ad_add]; abel
  simp only [leftAct, IG.mul_ε, IG.mul_ϖ]
  rw [e, D.ad_add, D.ad_ad_mul_inv, mul_inv_rev, D.ad_mul]
  simp only [D.ad_add]
  abel

/-- Lemma 6.3 in full: `π_{A0}` is onto ... -/
theorem pi_surjective : Function.Surjective (D.pi) := fun γ => ⟨⟨1, γ⟩, by simp [pi, D.ad_one]⟩

/-- ... and its fibres are exactly the `τ₋(𝓗)`-orbits, so `𝒢 / τ₋(𝓗) ≅ N` as in (6.12). -/
theorem pi_eq_iff (g g' : IG D) : D.pi g = D.pi g' ↔ ∃ h, g' = g * D.tau (-1) h := by
  constructor
  · intro hp
    refine ⟨g.ε⁻¹ * g'.ε, ?_⟩
    have key : D.ad (g.ϖ + D.θ g.ε) (g.ε⁻¹ * g'.ε) = g'.ϖ + D.θ g'.ε := by
      have := congrArg (fun x => D.ad x g'.ε) hp
      simp only [pi] at this
      rwa [D.ad_inv_ad, ← D.ad_mul] at this
    set h := g.ε⁻¹ * g'.ε with hh
    have hθ : D.θ g'.ε = D.ad (D.θ g.ε) h + D.θ h := by
      rw [← D.θ_mul, hh, mul_inv_cancel_left]
    rw [D.ad_add, hθ] at key
    have h3 : D.ad g.ϖ h = g'.ϖ + D.θ h := by
      rw [← add_right_cancel_iff (a := D.ad (D.θ g.ε) h), key]; abel
    ext
    · simp [hh]
    · simp only [IG.mul_ϖ, tau_ϖ, tau_ε, neg_smul, one_smul, h3]
      abel
  · rintro ⟨h, rfl⟩
    exact (D.pi_invariant_tau_neg g h).symm

/-- Lemma 6.4 is the action induced on the quotient: `g · π(k) = π(g k)`. -/
theorem leftAct_pi (g k : IG D) : D.leftAct g (D.pi k) = D.pi (g * k) := by
  have e : D.ad g.ϖ k.ε + k.ϖ + D.θ (g.ε * k.ε)
      = D.ad (g.ϖ + D.θ g.ε) k.ε + (k.ϖ + D.θ k.ε) := by
    rw [D.θ_mul, D.ad_add]; abel
  simp only [leftAct, pi, IG.mul_ε, IG.mul_ϖ]
  rw [e]
  conv_rhs => rw [D.ad_add, D.ad_ad_mul_inv, mul_inv_rev, D.ad_mul]
  simp only [D.ad_add]
  abel

end GaugeData

end GU
