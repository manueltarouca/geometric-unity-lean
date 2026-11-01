/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TimeGaugeFrame
import GU.Bundle.SpinTwist
import GU.Bundle.AdaptedGram

/-!
# Phase 4, item 4 (continued): no largest base; the natural locus; a multi-chart witness

* **`no_largest_spinStructure`**, **`no_largest_frameSet`**: there is no largest open `W ⊆ Y13`
  carrying a spin structure, or a global frame. If one existed it would contain every local `W`
  (`exists_spinStructure_near`, `frame_locTriv`), so it would be all of `Y13`, contradicting the
  obstruction. A canonical natural base (the time-orientation double cover) is not addressed here.
* **`mem_gaugeSet_iff`**: among metrics `G = Q ηR Qᵀ` of signature (1,3), `gaugeSet` is exactly
  `G₀₀ > 0`. Here `G = g⁻¹` is contravariant, so this says the covector `dx⁰` is timelike.
* **`exists_spinLiftData_R4`**: the concrete case. Over `X = ℝ⁴`, a spin structure exists on the
  whole locus `{G₀₀ > 0}` of `Y13` (fibrewise, the metrics for which `dx⁰` is timelike).
* **`twoChart`**, **`twoChart_h`**, **`twoCharts_iso`**: two charts with the same domain `W` and constant
  transition `t`, and a sign change of them. The lift is a `Spin77`-coboundary, so the glued bundle is
  trivial; this checks that lifts `≠ 1` are handled and that a sign change alters the lift but not the
  isomorphism class. It is not a nontrivial gluing.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **There is no largest open subset of `Y13` carrying a spin structure** (for nonempty `X`). -/
theorem no_largest_spinStructure (S : SpinStructure X) (hmax : ∀ S' : SpinStructure X, S'.W ⊆ S.W)
    (x : X) : False := by
  refine no_spinStructure_univ S (Set.eq_univ_of_forall fun b => ?_) x
  obtain ⟨S', hb⟩ := exists_spinStructure_near (X := X) b
  exact hmax S' hb

/-- **There is no largest open subset of `Y13` with a global frame of `OFr`** (for nonempty `X`). -/
theorem no_largest_frameSet (W₀ : Set (Y13o X)) (hW₀ : IsOpen W₀) (σ₀ : Y13o X → OFr X)
    (hc : ContinuousOn σ₀ W₀) (hp : ∀ y ∈ W₀, projOFr (σ₀ y) = y)
    (hmax : ∀ (W : Set (Y13o X)) (σ : Y13o X → OFr X), IsOpen W → ContinuousOn σ W →
      (∀ y ∈ W, projOFr (σ y) = y) → W ⊆ W₀) (x : X) : False := by
  have huniv : W₀ = Set.univ := Set.eq_univ_of_forall fun b => by
    let _ := regCharted (Fframe_regular (X := X))
    have _ := isManifold_regularLevel (Fframe_regular (X := X))
    obtain ⟨V, hV, hb, σ, -, hσ, hσp, -, -⟩ := frame_locTriv (X := X) b
    exact hmax V σ hV hσ.continuousOn hσp hb
  refine no_spinLiftData (SpinLiftData.ofSection W₀ hW₀ σ₀ hc hp) x fun θ => ?_
  show _ ∈ W₀
  rw [huniv]; exact Set.mem_univ _

/-! ### The gauge locus is `G₀₀ > 0` -/

/-- The Lorentz form. -/
def etaF (u v : Fin 4 → ℝ) : ℝ := u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- **Reverse Cauchy–Schwarz**: the orthogonal complement of a timelike vector is spacelike. -/
lemma etaF_neg {u v : Fin 4 → ℝ} (hu : 0 < etaF u u) (huv : etaF u v = 0) (hv : v ≠ 0) :
    etaF v v < 0 := by
  unfold etaF at *
  set a := u 0; set b := u 1; set c := u 2; set d := u 3
  set p := v 0; set q := v 1; set r := v 2; set s := v 3
  have hap : a * p = b * q + c * r + d * s := by linarith
  have hcs : (b * q + c * r + d * s) ^ 2 ≤ (b ^ 2 + c ^ 2 + d ^ 2) * (q ^ 2 + r ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (b * r - c * q), sq_nonneg (b * s - d * q), sq_nonneg (c * s - d * r)]
  set A := a * a - b * b - c * c - d * d with hA
  have hS : (q ^ 2 + r ^ 2 + s ^ 2) ≥ 0 := by positivity
  have hmain : (a * a) * (p * p - q * q - r * r - s * s) ≤ -A * (q ^ 2 + r ^ 2 + s ^ 2) := by
    have e : (a * p) ^ 2 ≤ (b ^ 2 + c ^ 2 + d ^ 2) * (q ^ 2 + r ^ 2 + s ^ 2) := by rw [hap]; exact hcs
    nlinarith
  have ha2 : 0 < a * a := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  by_contra hcon
  have hge : 0 ≤ p * p - q * q - r * r - s * s := by linarith [not_lt.mp hcon]
  have h0 : -A * (q ^ 2 + r ^ 2 + s ^ 2) ≥ 0 := le_trans (mul_nonneg ha2.le hge) hmain
  have hS0 : q ^ 2 + r ^ 2 + s ^ 2 = 0 := by nlinarith
  have hq0 : q = 0 := by nlinarith [sq_nonneg q, sq_nonneg r, sq_nonneg s]
  have hr0 : r = 0 := by nlinarith [sq_nonneg q, sq_nonneg r, sq_nonneg s]
  have hs0 : s = 0 := by nlinarith [sq_nonneg q, sq_nonneg r, sq_nonneg s]
  have hp0 : p = 0 := by
    have : a * p = 0 := by rw [hap, hq0, hr0, hs0]; ring
    exact (mul_eq_zero.mp this).resolve_left (fun h => by rw [h] at ha2; simp at ha2)
  apply hv
  funext k
  fin_cases k
  · exact hp0
  · exact hq0
  · exact hr0
  · exact hs0

lemma dot_G_eq {G Q : M4} (hG : G = Q * ηR * Qᵀ) (w w' : Fin 4 → ℝ) :
    w ⬝ᵥ (G *ᵥ w') = etaF (Qᵀ *ᵥ w) (Qᵀ *ᵥ w') := by
  have h := dot_conj Qᵀ ηR w w'
  rw [Matrix.transpose_transpose, ← hG] at h
  rw [← h, GU.Iso77.ηR_eq]
  simp [etaF, ηr, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_four]
  ring

/-- **Among (1,3) metrics, the gauge locus is exactly `G₀₀ > 0`.** -/
theorem mem_gaugeSet_iff {G Q : M4} (hQ : IsUnit Q) (hG : G = Q * ηR * Qᵀ) :
    G ∈ gaugeSet ↔ 0 < G 0 0 := by
  refine ⟨fun h => h.1, fun ha => ?_⟩
  have hsG : G.IsSymm := by
    rw [hG]; unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    congr 2
    rw [GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose]
  have hsym : ∀ i j, G j i = G i j := fun i j => congrFun (congrFun hsG i) j
  have hinj : Function.Injective (Qᵀ *ᵥ ·) := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_transpose _).mpr hQ)
  have ha0 : G 0 0 ≠ 0 := ha.ne'
  -- the quadratic form of the Schur complement is positive definite
  have hq : ∀ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
      0 < schur G 1 1 * x ^ 2 + 2 * schur G 1 2 * x * y + 2 * schur G 1 3 * x * z +
        schur G 2 2 * y ^ 2 + 2 * schur G 2 3 * y * z + schur G 3 3 * z ^ 2 := by
    intro x y z hxyz
    set t := -(G 0 1 * x + G 0 2 * y + G 0 3 * z) / G 0 0
    let w : Fin 4 → ℝ := ![t, x, y, z]
    let e : Fin 4 → ℝ := ![1, 0, 0, 0]
    have hw : w ≠ 0 := fun h => by
      have h1 := congrFun h 1; have h2 := congrFun h 2; have h3 := congrFun h 3
      simp [w] at h1 h2 h3
      rcases hxyz with h | h | h <;> contradiction
    have heG : e ⬝ᵥ (G *ᵥ e) = G 0 0 := by simp [e, dotProduct, mulVec, Fin.sum_univ_four]
    have heW : e ⬝ᵥ (G *ᵥ w) = 0 := by
      simp only [e, w, dotProduct, mulVec, Fin.sum_univ_four]
      simp [t]; field_simp; ring
    have hneg := etaF_neg (u := Qᵀ *ᵥ e) (v := Qᵀ *ᵥ w)
      (by rw [← dot_G_eq hG, heG]; exact ha) (by rw [← dot_G_eq hG, heW])
      (fun h => hw (hinj (by simpa using h)))
    rw [← dot_G_eq hG] at hneg
    have hexp : w ⬝ᵥ (G *ᵥ w) = -(schur G 1 1 * x ^ 2 + 2 * schur G 1 2 * x * y +
        2 * schur G 1 3 * x * z + schur G 2 2 * y ^ 2 + 2 * schur G 2 3 * y * z +
        schur G 3 3 * z ^ 2) := by
      simp only [w, dotProduct, mulVec, Fin.sum_univ_four]
      simp [t, schur, hsym 0 1, hsym 0 2, hsym 0 3, hsym 1 2, hsym 1 3, hsym 2 3]
      field_simp; ring
    rw [hexp] at hneg
    linarith
  have h1 : 0 < schur G 1 1 := by simpa using hq 1 0 0 (Or.inl one_ne_zero)
  have hc1 : c11 G ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hc11 : c11 G * c11 G = schur G 1 1 := Real.mul_self_sqrt h1.le
  have e12 : schur G 1 2 = c11 G * c21 G := by unfold c21; field_simp
  have e13 : schur G 1 3 = c11 G * c31 G := by unfold c31; field_simp
  have h2 : 0 < m2 G := by
    have := hq (-(c21 G) / c11 G) 1 0 (Or.inr (Or.inl one_ne_zero))
    have e : schur G 1 1 * (-(c21 G) / c11 G) ^ 2 + 2 * schur G 1 2 * (-(c21 G) / c11 G) * 1 +
        2 * schur G 1 3 * (-(c21 G) / c11 G) * 0 + schur G 2 2 * 1 ^ 2 +
        2 * schur G 2 3 * 1 * 0 + schur G 3 3 * 0 ^ 2 = m2 G := by
      rw [← hc11, e12, m2]; field_simp; ring
    rwa [e] at this
  have hc2 : c22 G ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  have hc22 : c22 G * c22 G = m2 G := Real.mul_self_sqrt h2.le
  have e23 : schur G 2 3 = c21 G * c31 G + c22 G * c32 G := by unfold c32; field_simp; ring
  have e22 : schur G 2 2 = c21 G ^ 2 + c22 G * c22 G := by rw [hc22, m2]; ring
  have e33 : schur G 3 3 = c31 G ^ 2 + c32 G ^ 2 + m3 G := by rw [m3]; ring
  refine ⟨ha, h1, h2, ?_⟩
  set y := -(c32 G) / c22 G
  set x := -(c21 G * y + c31 G) / c11 G
  have ex : c11 G * x + c21 G * y + c31 G = 0 := by simp only [x]; field_simp; ring
  have ey : c22 G * y + c32 G = 0 := by simp only [y]; field_simp; ring
  have := hq x y 1 (Or.inr (Or.inr one_ne_zero))
  have e : schur G 1 1 * x ^ 2 + 2 * schur G 1 2 * x * y + 2 * schur G 1 3 * x * 1 +
      schur G 2 2 * y ^ 2 + 2 * schur G 2 3 * y * 1 + schur G 3 3 * 1 ^ 2 =
      (c11 G * x + c21 G * y + c31 G) ^ 2 + (c22 G * y + c32 G) ^ 2 + m3 G := by
    rw [← hc11, e12, e13, e22, e23, e33]; ring
  rw [e, ex, ey] at this
  simpa using this

/-! ### The concrete case `X = ℝ⁴` -/

section R4

abbrev R4 := Fin 4 → ℝ

set_option maxHeartbeats 400000 in
lemma chartDom_R4 (a : HomTotM R4) (y : Yobs R4) : y ∈ chartDom a := by
  have h1 : chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) a.proj =
      chartAt (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) y := rfl
  have h2 : (trivializationAt HomF (HomCb (X := R4)) a.proj) =
      (trivializationAt HomF (HomCb (X := R4)) y) := rfl
  refine ⟨?_, ?_⟩
  · rw [h2]; exact FiberBundle.mem_baseSet_trivializationAt HomF (HomCb (X := R4)) y
  · rw [h1]; exact mem_chart_source _ y

set_option maxHeartbeats 400000 in
lemma gaugeMetric_R4 (a : HomTotM R4) (y : Yobs R4) : gaugeMetric a y = Gpt y := by
  have h := (symCore (Zt R4)).coordChange_self ((symCore (Zt R4)).indexAt (πY y)) (πY y)
    ((symCore (Zt R4)).mem_baseSet_at _) ((y : Sym2TX R4).2)
  exact congrArg symMat h

/-- **The concrete case: over `X = ℝ⁴`, a spin structure exists on the locus `G₀₀ > 0` of all
of `Y13`.** -/
theorem exists_spinLiftData_R4 :
    ∃ D : SpinLiftData R4, D.W = {y : Y13o R4 | 0 < Gpt (y : Yobs R4) 0 0} := by
  let a : HomTotM R4 := pLoop (0 : R4) 0
  obtain ⟨D, hD⟩ := exists_spinLiftData_gauge a
  refine ⟨D, hD.trans (Set.ext fun y => ?_)⟩
  obtain ⟨P, hP, hG⟩ := y.2
  show (((y : Yobs R4) ∈ chartDom a) ∧ gaugeMetric a y ∈ gaugeSet) ↔ _
  rw [gaugeMetric_R4, mem_gaugeSet_iff hP hG]
  exact ⟨fun h => h.2, fun h => ⟨chartDom_R4 a y, h⟩⟩

end R4

/-! ### A two-chart witness -/

/-- Two charts over `W`, the second frame being the first one moved by `ρ(t)`. -/
def twoChart (W : Set (Y13o X)) (hW : IsOpen W) (σ : Y13o X → OFr X) (hσ : ContinuousOn σ W)
    (hσp : ∀ y ∈ W, projOFr (σ y) = y) (t : Spin77) : SpinLiftData X where
  W := W
  isOpen_W := hW
  ι := Bool
  V _ := W
  isOpen_V _ := hW
  V_sub _ := subset_rfl
  cover _ hy := ⟨false, hy⟩
  σ i y := if i then actOFr' (σ y) (spinToO77 t) else σ y
  cont_σ i := by
    cases i
    · exact hσ
    · have h : ContinuousOn (fun y => actOFr' (σ y) (spinToO77 t)) W :=
        continuous_actOFr'.comp_continuousOn (hσ.prodMk continuousOn_const)
      exact h
  proj_σ i y hy := by cases i <;> simp [projOFr_act, hσp y hy]
  h i j _ := (if i then t⁻¹ else 1) * (if j then t else 1)
  cont_h _ _ := continuousOn_const
  lift i j y _ := by
    cases i <;> cases j <;> simp [actOFr'_mul, actOFr'_one]
  cocycle i j k _ _ := by
    cases i <;> cases j <;> cases k <;> simp [mul_assoc]

/-- The lift between the two charts is `t`. -/
lemma twoChart_h (W : Set (Y13o X)) (hW : IsOpen W) (σ : Y13o X → OFr X) (hσ : ContinuousOn σ W)
    (hσp : ∀ y ∈ W, projOFr (σ y) = y) (t : Spin77) (y : Y13o X) :
    (twoChart W hW σ hσ hσp t).h false true y = t := by
  simp [twoChart]

/-- The sign `−1` on the second chart. -/
def signTwo (i : Bool) (_ : Y13o X) : Spin77 := if i then negOne else 1

/-- **A non-trivial sign change of the two-chart data is an isomorphism**: the lift between the
charts becomes `t · (−1)`, a different element, and the spin structures are isomorphic. -/
def twoCharts_iso (W : Set (Y13o X)) (hW : IsOpen W) (σ : Y13o X → OFr X) (hσ : ContinuousOn σ W)
    (hσp : ∀ y ∈ W, projOFr (σ y) = y) (t : Spin77) :
    SpinIso (twoChart W hW σ hσ hσp t).toStructure
      ((twoChart W hW σ hσ hσp t).twist signTwo
        (fun i _ _ => by cases i <;> simp [signTwo, IsSign])
        (fun _ => continuousOn_const)).toStructure :=
  SpinLiftData.twistIso _ _ _ _

lemma twoCharts_lift_ne (W : Set (Y13o X)) (hW : IsOpen W) (σ : Y13o X → OFr X)
    (hσ : ContinuousOn σ W) (hσp : ∀ y ∈ W, projOFr (σ y) = y) (t : Spin77) (y : Y13o X) :
    ((twoChart W hW σ hσ hσp t).twist signTwo
        (fun i _ _ => by cases i <;> simp [signTwo, IsSign])
        (fun _ => continuousOn_const)).h false true y ≠
      (twoChart W hW σ hσ hσp t).h false true y := by
  show signTwo false y * (twoChart W hW σ hσ hσp t).h false true y * signTwo true y ≠ _
  rw [twoChart_h]
  simp only [signTwo, Bool.false_eq_true, if_false, if_true, one_mul]
  exact fun h => negOne_ne_one (mul_eq_left.mp h)

/-- **Multi-chart instances exist near every point of `Y13`.** -/
theorem exists_twoChart_near (b : Y13o X) (t : Spin77) :
    ∃ D : SpinLiftData X, b ∈ D.W ∧ ∃ (i j : D.ι), ∀ y, D.h i j y = t := by
  let _ := regCharted (Fframe_regular (X := X))
  have _ := isManifold_regularLevel (Fframe_regular (X := X))
  obtain ⟨V, hV, hb, σ, -, hσ, hp, -, -⟩ := frame_locTriv (X := X) b
  exact ⟨twoChart V hV σ hσ.continuousOn hp t, hb, false, true,
    fun y => twoChart_h V hV σ hσ.continuousOn hp t y⟩

end

end GU.Library
