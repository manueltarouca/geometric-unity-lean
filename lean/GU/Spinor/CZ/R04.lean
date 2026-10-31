import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow8 : ∀ j : Fin 20, (8 : Fin 20) ≠ j → trPair (V 8) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow9 : ∀ j : Fin 20, (9 : Fin 20) ≠ j → trPair (V 9) (V j) = 0 := by decide +kernel

end GU.Spinor
