# Metric tensor conversion

## 2026-07-14: joint product-base conversion

`joint_to02` is now the canonical low-level bridge from a jointly smooth
family of curried tangent-space bilinear forms over `M × ℝ` to the jointly
smooth family of uncurried `(0,2)` tensors.  The existing local-trivialization
identity was generalized to an arbitrary fibre bilinear map and reused; no
whole-Hom equality is exposed to consumers.

The focused file check passed.  The theorem adds no convergence predicate,
chart-local-constancy assumption, or Ricci-flow-specific wrapper.  It is a
reusable producer for the scalar nonautonomous coefficient route, not the A2
operator theorem itself.

Honest status: the A2 operator theorem remains unstated and unproved (0%).
Its dedicated coefficient/jet machinery is roughly 45% complete; this bridge
closes only the metric-to-covariant-tensor smoothness substep.  The Perelman
noncollapsing endpoint remains 0%, with its broader dedicated machinery still
at an early stage.
