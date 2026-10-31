import Mathlib

/-!
# The internal dimension formula (4.2)–(4.3)

For `X` of signature `(i, j)`, `n = i + j`, the normal bundle `N` of the observation has rank
`N = n(n+1)/2` (the fiber of `Met(X)`). The draft's exponent satisfies
`i² + j² + 2ij + i + j = n² + n = 2N` (`exponent_eq`), so its Dirac count
`2^{(i²+j²+2ij+i+j)/4}` is `2^{N/2}`, the Dirac spinor dimension of `N` (`dirac_eq`, for `N` even),
and the Weyl count is half of it. For `(1,3)`: `N = 10`, Dirac 32, Weyl 16 (`physical`).
`N` is even exactly when `n ≡ 0, 3 (mod 4)` (`N_even_iff`, checked for `n ≤ 40`).
-/

namespace GU.InternalDim

theorem exponent_eq (i j : ℕ) : i ^ 2 + j ^ 2 + 2 * i * j + i + j = (i + j) * (i + j + 1) := by ring

theorem fiber_rank (n : ℕ) : n * (n + 1) = 2 * (n * (n + 1) / 2) := by
  have : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  omega

theorem dirac_eq (i j : ℕ) :
    2 ^ ((i ^ 2 + j ^ 2 + 2 * i * j + i + j) / 4) = 2 ^ (((i + j) * (i + j + 1) / 2) / 2) := by
  rw [exponent_eq]; congr 1; omega

theorem physical : (1 + 3) * (1 + 3 + 1) / 2 = 10 ∧ 2 ^ (10 / 2) = 32 ∧ 2 ^ (10 / 2 - 1) = 16 := by
  decide

theorem N_even_iff : ∀ n ∈ List.range 41, (n * (n + 1) / 2) % 2 = 0 ↔ n % 4 = 0 ∨ n % 4 = 3 := by
  decide

end GU.InternalDim
