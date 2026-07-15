# CoordinateFrame — notes

Chart-induced coordinate tangent frame at a point (`coordinateFrameAt`, `coordinateFrameAt_toBasis`)
and the coordinate-frame component API (`coordComponent0SAt` = `component0S (toBasis)`,
`coordComponentRSAt` = `componentRS_gen (toBasis)`).

## 2026-06-14 — component-eval API hardening (item 4)
Added, next to `coordComponentRSAt_apply`:
- `coordComponent0SAt_congr_slots`, `coordComponentRSAt_congr_slots` — coord-frame slot-map rewrites.
- `coordExt0SAt`, `coordExtRSAt` — coordinate-frame tensor extensionality (equal coordinate components ⇒
  equal tensors), thin wrappers over `ext0S_basis` / `extRS_basis_gen` at `coordinateFrameAt_toBasis`.

`coordComponent*` delta-unfolds to `component*` cleanly, so the `coordExt*` wrappers compile without any
transparency hack. Additive, focused-check green. See `Tensor/RSTensor/ComponentEvalApiPlan.md` (incl. the
note that the chosen validation file `NablaComponents/Tensor0S.lean` was a mismatch — its hacks are
bundle-topology `synthInstanceFailed`, not component-eval).
