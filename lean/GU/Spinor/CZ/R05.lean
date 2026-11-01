/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow10 : ∀ j : Fin 20, (10 : Fin 20) ≠ j → trPair (V 10) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow11 : ∀ j : Fin 20, (11 : Fin 20) ≠ j → trPair (V 11) (V j) = 0 := by decide +kernel

end GU.Spinor
