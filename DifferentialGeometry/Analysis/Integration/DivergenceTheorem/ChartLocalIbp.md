# ChartLocalIbp status

## 2026-07-16

- `chart_local_ibp_lip` is proved and verified: a compactly supported scalar
  whose zero-extended chart pullback is Lipschitz satisfies chart-local
  integration by parts.
- Added `tangent_lip_int`. It reuses the two Euclidean summand-integrability
  witnesses already returned by `ibp_lip_index`, then transports their finite
  sum through the density-weighted chart map. No new analytic assumption was
  introduced.
- Focused and targeted verification passed.
- The remaining global assembly should use `chart_int_eq_global` to transfer
  each localized tangent action and cancel the finite partition-of-unity sum.
- Honest accounting: `weak_grad_of_lip` is not yet stated/proved here (0% as a
  theorem); its dedicated Lipschitz/IBP machinery is about 85%. The cutoff
  energy theorem and the Perelman noncollapsing endpoint remain 0% as endpoint
  theorems.
