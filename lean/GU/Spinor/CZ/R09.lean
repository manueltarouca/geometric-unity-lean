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
theorem Vrow18 : ∀ j : Fin 20, (18 : Fin 20) ≠ j → trPair (V 18) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow19 : ∀ j : Fin 20, (19 : Fin 20) ≠ j → trPair (V 19) (V j) = 0 := by decide +kernel

end GU.Spinor
