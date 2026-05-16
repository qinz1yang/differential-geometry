# Tensor

## 2026-05-12: Heartbeat audit

- Reduced the multilinear tensor smoothness bump from `400000` to `250000`.
- Removing the bump entirely failed with a `whnf` timeout in the inverse fiberwise-equivalence smoothness proof.
- Verification passed at `250000`.
