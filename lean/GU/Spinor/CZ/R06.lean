import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow12 : ∀ j : Fin 20, (12 : Fin 20) ≠ j → trPair (V 12) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow13 : ∀ j : Fin 20, (13 : Fin 20) ≠ j → trPair (V 13) (V j) = 0 := by decide +kernel

end GU.Spinor
