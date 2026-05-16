# Contract

## 2026-05-12: Heartbeat audit

- Reduced the first contraction theorem-local bump from `800000` to `400000`.
- The first contraction proof failed at `250000` with a `whnf` timeout, so `400000` is the current minimal checked budget.
- The second contraction theorem still needs `800000`; a `400000` trial failed with `whnf` timeouts in the contravariant contraction proof.
- Verification passed with the current theorem-local budgets.
