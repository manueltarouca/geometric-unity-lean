import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V_gram_diag : ∀ i : Fin 20, trPair (V i) (V i) ≠ 0 := by decide +kernel

end GU.Spinor
