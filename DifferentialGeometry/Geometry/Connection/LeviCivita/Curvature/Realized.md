# Realized.lean

## 2026-06-13

Updated callers of the Levi-Civita curvature symmetry wrappers after those
wrappers stopped requiring a caller-supplied local smoothness proof.

Verification: checked through the downstream rebuild.  No new `sorry` or
`admit`.

## 2026-07-22

Added the two canonical realization helpers needed by the static Hamilton
identity:

- `canNabla2RicTrace` contracts canonical `nabla^2 Ric` in an arbitrary inverse
  metric basis.
- `canRm2Symm` exports the curvature symmetries of canonical `nabla^2 Rm04`.

Both helpers are focused-green and exact-green with no `sorry`, `admit`, or
`axiom`.  They are completed infrastructure; they do not by themselves state
or prove a Ricci-flow evolution theorem.
