# EdgeRiemCancel

## Current source state

`EdgeRiemCancel.lean` contains a source-level, placeholder-free exact
Riemann-cancellation producer.  Focused Lean verification is pending the
serialized shared-workspace schedule.

The file exports:

- `edgeRiem_cancel`, the algebraic fact that a complete Riemann refold cancels
  the Riemann half inserted in `edgeRicciHalf`;
- `edgeLie_inner` and `edgeLie_green`, the exact formal-partner and Green
  identities for the DeTurck Lie family alone; and
- `exists_edgeLieRef`, which rebuilds the canonical public Palatini and
  DeTurck refold data, cancels the Riemann block, and returns a normal form
  containing only the genuine Ricci connection-difference coefficient, a
  uniformly bounded order-zero family, the already visible lower arms, and
  the Lie pair family.

The producer adds no hypothesis.  Its internal finite jet radius is used only
to instantiate the already proved exact refold identities for the fixed smooth
edge tensor; no such radius appears in the theorem statement or downstream
estimate.

## Mathematical consequence

The earlier combined top coefficient spent a separate smallness budget on a
Riemann second-order partner.  That was unnecessary: the Riemann order-zero
and second-order pieces are the two sides of one exact Palatini identity.
After cancellation, only the Lie formal partner needs a boundary energy
estimate.

This does not by itself prove `ricci_flow_forward_unique`.  The unchanged
endpoint remains **0%** until all surviving Ricci/DeTurck arms are absorbed,
the closed-edge energy theorem is assembled, and geometric Ricci-flow gauge
uniqueness is completed.

## Verification

- Source placeholders (`sorry`, `admit`, axiom): none.
- Focused Lean check: pending serialized verification.
- `extends_of_rmBounded`: unchanged.
