import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow4 : ∀ j : Fin 20, (4 : Fin 20) ≠ j → trPair (V 4) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow5 : ∀ j : Fin 20, (5 : Fin 20) ≠ j → trPair (V 5) (V j) = 0 := by decide +kernel

end GU.Spinor
