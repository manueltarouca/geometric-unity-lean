/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU

/-!
# Compiled baseline index (checked with `lake env lean Baseline.lean`)

One place that names the headline results of the formalisation, grouped by the program's items.
Each `example` elaborates only if the theorem exists with its proof, so this file is a cheap
machine check that the baseline is in place. Axioms: `lake env lean Audit.lean`.
-/

open GU GU.Observerse GU.Spinor GU.Library GU.Predictions

/-! ## 1. Topology: `X⁴` and the observerse `Y¹⁴` -/
example := @Yobs_isManifold          -- Y is a smooth 14-manifold over any smooth 4-manifold X
example := @finrank_model            -- model dimension 4 + 10 = 14
example := @contMDiff_Yobs_proj      -- π : Y → X is smooth
example := @signature_selected       -- orthonormal (7,7) frames exist exactly over (1,3) points

/-! ## 2. Chimeric geometry and reductions -/
example := @chimeric_vectorBundle    -- C = V ⊕ H* is a vector bundle over Y
example := @chimeric_smooth          -- ... and a smooth one
example := @u32_length               -- u(3,2): 25 independent elements commuting with J
example := @u32_commutes_J
example := @u32_linIndep
example := @pati_salam_split         -- so(6) ⊕ so(4) = 15 + 6 compact bivectors
noncomputable example := @spin6SU4Equiv            -- Spin(6) ≅ SU(4)
noncomputable example := @spin4SU2Equiv            -- Spin(4) ≅ SU(2) × SU(2)

/-! ## 3. Spin(7,7), O(7,7) and the double cover -/
example := @lieGroup_O77             -- O(7,7) is a 91-dimensional Lie group
noncomputable example := @orthOGEquiv              -- ... isomorphic to the frame-bundle structure group O(Bη)
example := @cc_O77_iff_spin          -- identity component = image of Spin(7,7)
example := @isCoveringMap_spinToSO0  -- Spin(7,7) → SO₀(7,7) is a covering map
example := @spin_pathConnected       -- Spin(7,7) is path-connected
example := @ker_spinToSO0_eq         -- kernel {±1}: the nontrivial double cover

example := @GU.Library.isManifold_regularLevel   -- regular value theorem on manifold domains
example := @GU.Library.isManifold_orthoFrames    -- (7,7)-orthonormal frames of C: smooth manifold
example := @GU.Library.contMDiff_orthoFrames_val -- ... a smooth submanifold of the frame bundle
example := @GU.Library.fibreDim_orthoFrames      -- ... of dimension 105 = 14 + 91

/-! ## 4. Gauge groups and synthetic predictions -/
example := @gauge_embedding          -- SM gauge algebra inside the observerse spin algebra
example := @particle_allocation      -- one generation from the (6,4) branching
example := @hypercharge_forced
example := @center_two_u1

/-! ## 5. Audit of the draft -/
example := @Ψu_blade                 -- (3.27): placement of i is correct
example := @Ψu_equivariant           -- ... Spin(7,7)-equivariant
example := @uC_nilpotent             -- §9.2: the trace pairing has isotropic elements
example := @GU.FormsW.einstein_all_real        -- (9.3) with Hodge stars gives Einstein on all curvature
