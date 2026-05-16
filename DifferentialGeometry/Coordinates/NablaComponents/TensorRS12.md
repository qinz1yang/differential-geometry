# TensorRS12 Nabla Components

## 2026-05-12: `(1,2)` coordinate formula

- Added `upperIdx1` and `lowerIdx2` plus stable simp lemmas for the `Fin 1`,
  `Fin 2`, and `Function.update` bookkeeping.
- Proved `nablaRS_coordFrame_1_2_of_smooth`, the component formula
  `(nabla_X A)^k_ij = X(A^k_ij) + Gamma^k_m A^m_ij - Gamma^m_i A^k_mj - Gamma^m_j A^k_im`.
- A broad `simp` with additive commutativity timed out. The stable proof first
  rewrites by the general theorem, then uses a restricted `simp only` for the
  finite-index cleanup and finishes the additive regrouping with `abel`.

## 2026-05-14: Index helpers centralized

- Moved consumption of `upperIdx1`, `lowerIdx2`, and their update simp lemmas to
  the shared component-notation layer in `Coordinates/Tensor.lean`.
- This file now focuses only on the `(1,2)` covariant-derivative component
  specialization.
- Verification passed.
