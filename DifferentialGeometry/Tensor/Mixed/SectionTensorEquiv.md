# SectionTensorEquiv

## 2026-05-12: Heartbeat audit

- Kept the first mixed-section equivalence bump at `800000`; a `400000` trial failed with `whnf` timeouts in the bundle-trivialization proof.
- Reduced the later two theorem-local bumps from `400000` to `250000`.
- Verification passed with the current theorem-local budgets. Lean still reports
  existing unused-section-variable warnings.
