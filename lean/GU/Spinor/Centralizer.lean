import GU.Spinor.Reductions

/-!
# Definitions for the centraliser of `J` in `spin(6,4)`

`u32c`, `allU = u32 ++ u32c`, and the index families `U`, `U25`, `Uc`, `V`. The theorems are in
`CentralizerMain.lean` (`centralizer_iff`) and `SpanFull.lean` (`allU_linIndep`, `span_eq`,
`centralizer_spin64`), with heavy Gram checks split into `CZ/` and `UG/`.
-/

namespace GU.Spinor

open Matrix CSum

def u32c : List CSum :=
  ((List.finRange 5).flatMap fun i => (List.finRange 5).filterMap fun j =>
    if i < j then some (i, j) else none).flatMap fun ij =>
      let p := planes.get ⟨ij.1, by simp [planes]⟩
      let q := planes.get ⟨ij.2, by simp [planes]⟩
      if sameType p q then
        [biv p.1 q.1 ++ neg (biv p.2 q.2), biv p.1 q.2 ++ biv p.2 q.1]
      else
        [biv p.1 q.1 ++ biv p.2 q.2, biv p.1 q.2 ++ neg (biv p.2 q.1)]

def allU : List CSum := u32 ++ u32c

theorem allU_length : allU.length = 45 := by decide
theorem u32c_length : u32c.length = 20 := by decide

def U (i : Fin 45) : CSum := allU.get (Fin.cast allU_length.symm i)

def U25 (i : Fin 25) : CSum := u32.get (Fin.cast u32_length.symm i)
def Uc (j : Fin 20) : CSum := u32c.get (Fin.cast u32c_length.symm j)
def V (j : Fin 20) : CSum := comm (Uc j) Jc

end GU.Spinor
