# Naturality

## 2026-05-12: Heartbeat audit

- Reduced the theorem-local `maxHeartbeats` bump from `800000` to `400000`.
- A `250000` trial failed with `whnf` timeouts in the naturality proof, so the remaining bump is still theorem-local and justified.
- Verification passed at `400000`.
