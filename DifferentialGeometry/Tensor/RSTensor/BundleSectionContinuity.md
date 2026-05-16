# BundleSectionContinuity

## 2026-05-12: Heartbeat audit

- Removed the file-level `synthInstance.maxHeartbeats` and `maxHeartbeats` bumps.
- The continuity API checks at the default heartbeat budget.
- Verification passed. Lean still reports existing unused-section-variable warnings.
