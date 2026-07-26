# CrossChartBoundStrictMemWkpHigherOrder

## 2026-07-19: joint arbitrary-order transfer

### Source state

- The existing arbitrary-`k` proof already constructed a compactly supported
  local representative in the target chart and proved its `MemWkp` membership.
- That membership was previously kept as a local fact; the public theorem
  exported only the norm inequality.
- `crossChartJointK` now exports the logically joint result: the cross-chart
  POU pullback/pushforward remains in `MemWkp k p` and obeys the same norm
  bound.
- The old long public name is retained unchanged as a norm-only compatibility
  wrapper.
- No new class, instance, notation, axiom, `sorry`, or `admit` was introduced.

### Verification state

- Source implementation: complete.
- Focused Lean verification: pending because this lane was explicitly
  source-only while another named build owned the shared verification slot.
- `ricci_flow_unif_existence`: still 0%.  This is generic spatial Sobolev
  completeness machinery, not the parabolic solver or the endpoint theorem.

