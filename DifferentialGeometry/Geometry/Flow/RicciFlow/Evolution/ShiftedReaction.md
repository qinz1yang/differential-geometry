# ShiftedReaction

## 2026-07-12 — short-time branch alignment

- The apparent reaction-algebra failures were evaluation-API mismatches after `Tensor0SSpace` became opaque, not mathematical gaps.
- The tensor equalities now use `component0S` and basis extensionality. Natural-number scalar multiplication is handled separately from real scalar multiplication.
- Focused verification passed without `sorry`; no local blocker remains.
