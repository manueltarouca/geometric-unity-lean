/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinCovering

/-!
# **`Spin(7,7)` is path-connected**: the spin cover is the nontrivial double cover

* `negOne_joined`: the path `t ↦ e₀(cos πt e₀ + sin πt e₁) = cos πt + sin πt e₀e₁` stays in
  `Spin77` (a product of two unit vectors, `pair_mem`) and joins `1` to `−1`.
* `SO₀(7,7)` is path-connected: it is the identity component of the manifold `O77`, which is
  locally path-connected.
* Path lifting through the covering `spinToSO0` (`comp_subtypeVal_pathComponent_surjective`):
  every fibre meets the path component of `1`; fibres are cosets of `ker ⊆ {±1}`, and `−1` is in
  that path component. Hence **`spin_pathConnected : PathConnectedSpace Spin77`**. With
  `ker_spinToSO0_eq : ker = {1, −1}` (and `negOne_ne_one`), `Spin(7,7) → SO₀(7,7)` is the connected,
  two-sheeted (nontrivial) double cover.
-/

namespace GU.Spinor

open Matrix CliffordAlgebra GU.Library Topology

lemma Q77_rot (c s : ℝ) : Q77 (c • eb 0 + s • eb 1) = c ^ 2 + s ^ 2 := by
  simp [Q77, QuadraticMap.weightedSumSquares_apply, eb, Pi.single_apply, Fin.sum_univ_succ]
  ring

/-- The rotor `e₀ (cos θ e₀ + sin θ e₁) ∈ Spin(7,7)`. -/
noncomputable def rotor (θ : ℝ) : Spin77 :=
  ⟨ι Q77 (eb 0) * ι Q77 (Real.cos θ • eb 0 + Real.sin θ • eb 1),
    pair_mem _ _ (by rw [Q_eb, Q77_rot, Real.cos_sq_add_sin_sq]; norm_num)⟩

lemma continuous_rotor : Continuous rotor := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_const.mul ((LinearMap.continuous_of_finiteDimensional (ι Q77)).comp ?_)
  exact (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

lemma rotor_zero : rotor 0 = 1 := by
  apply Subtype.ext
  show ι Q77 (eb 0) * ι Q77 (Real.cos 0 • eb 0 + Real.sin 0 • eb 1) = 1
  rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, ι_sq_scalar, Q_eb]
  simp

lemma rotor_pi : rotor Real.pi = negOne := by
  apply Subtype.ext
  show ι Q77 (eb 0) * ι Q77 (Real.cos Real.pi • eb 0 + Real.sin Real.pi • eb 1) = -1
  rw [Real.cos_pi, Real.sin_pi, zero_smul, add_zero, neg_one_smul, map_neg, mul_neg, ι_sq_scalar,
    Q_eb]
  simp

lemma negOne_joined : Joined (1 : Spin77) negOne := by
  refine ⟨⟨⟨fun t => rotor (Real.pi * t), ?_⟩, ?_, ?_⟩⟩
  · exact continuous_rotor.comp (continuous_const.mul continuous_subtype_val)
  · simp [rotor_zero]
  · simp [rotor_pi]

instance : LocallyPathConnectedSpace O77 := ChartedSpace.locallyPathConnectedSpace
  (Fin (fibreDim (Mat 14) (symS 14)) → ℝ) O77

instance : PathConnectedSpace SO0 := by
  have hopen : IsOpen (connectedComponent (1 : O77)) := isOpen_connectedComponent
  have : LocallyPathConnectedSpace SO0 := hopen.locallyPathConnectedSpace
  have : ConnectedSpace SO0 :=
    Subtype.connectedSpace (isConnected_connectedComponent (x := (1 : O77)))
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

lemma mem_ker_spinToSO0 {x : Spin77} (hx : x ∈ spinToSO0.ker) : x = 1 ∨ x = negOne := by
  have hx' : spinToO77 x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hv : ∀ v, vecRep x v = v := fun v => by
    have h := of_spinMat_mulVec x v
    have h1 : spinMat x = Matrix.of.symm 1 := congrArg Subtype.val hx'
    rw [h1, Equiv.apply_symm_apply, one_mulVec] at h
    exact h.symm
  rcases vecRep_ker x hv with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

lemma mem_pathComponent_one (x : Spin77) : x ∈ pathComponent (1 : Spin77) := by
  obtain ⟨⟨e, he⟩, hex⟩ :=
    isCoveringMap_spinToSO0.comp_subtypeVal_pathComponent_surjective (1 : Spin77) (spinToSO0 x)
  have hk : e⁻¹ * x ∈ spinToSO0.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hex, inv_mul_cancel]
  have hneg : negOne ∈ pathComponent (1 : Spin77) := negOne_joined
  have hx : x = e * (e⁻¹ * x) := by group
  rcases mem_ker_spinToSO0 hk with h | h
  · rw [hx, h, mul_one]; exact he
  · rw [hx, h]; exact (Subgroup.pathComponentOne Spin77).mul_mem he hneg

lemma negOne_mem_ker_spinToSO0 : negOne ∈ spinToSO0.ker :=
  MonoidHom.mem_ker.mpr (Subtype.ext spinToO77_neg_one)

/-- **The kernel of the spin cover is exactly `{±1}`** (two sheets, as `negOne ≠ 1`). -/
theorem ker_spinToSO0_eq : (spinToSO0.ker : Set Spin77) = {1, negOne} := by
  ext x
  constructor
  · intro hx; exact mem_ker_spinToSO0 hx
  · rintro (rfl | rfl)
    · exact spinToSO0.ker.one_mem
    · exact negOne_mem_ker_spinToSO0

/-- **`Spin(7,7)` is path-connected.** -/
instance spin_pathConnected : PathConnectedSpace Spin77 where
  nonempty := ⟨1⟩
  joined x y := (mem_pathComponent_one x).symm.trans (mem_pathComponent_one y)

theorem spin_connected : ConnectedSpace Spin77 := inferInstance

end GU.Spinor

