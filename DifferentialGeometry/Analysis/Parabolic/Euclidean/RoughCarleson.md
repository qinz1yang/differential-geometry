# RoughCarleson

## Status

Focused Lean check passes with no warnings (2026-07-19).

## Mathematical role

The rough `C⁰` Ricci--DeTurck fixed-point space cannot require a bounded
spatial derivative at `t = 0`.  `GradCarl` records the scale-invariant
space--time estimate

`integral_(0,R²) integral_(B(x,R)) |Du|² <= C R^n`.

`bilinCarl` proves that a bounded bilinear expression in two such gradients
is an `L¹` Carleson source.  This is the honest target for the compensating
`DA(u)[Du] Dw` term produced by `coeffD2_refold`; the full quasilinear
principal term is retained.

`GradWt` and `SrcWt` remain available as auxiliary pointwise predicates, and
`bilinWt_of_bound` proves their elementary quadratic estimate.  They are not
the Koch--Lamm solution/source space used by the live rough-data lane: a
general divergence heat potential does not map an `L∞` flux to a weighted
pointwise `L∞` gradient.  The live carrier is `KLPath`/`KLSource0`/
`KLSource1` from `KochLammSpaces.lean`.

`InRoughPath` is a retained historical interface.  It combines the
positive-time `C⁰` path bound, the weighted gradient bound, and gradient
Carleson mass.  `InRoughSrc` combines the weighted and Carleson components of
the nondifferentiated source class.  A divergence flux uses the same two
gradient-shaped components as `d`.

For the local-addition HMF specialization, `linWt_of_bound` and
`linCarl_of_bound` are the key principal-flux estimates.  A prescribed
coefficient field `g(t)^{-1}-q^{-1}` with operator norm at most `epsilon`
multiplies the weighted flux bound by `epsilon` and its local `L²` Carleson
mass by `epsilon²`.  This is the genuine small parameter; no horizon power is
inserted.

`bilinCarl_bound` handles the local-addition quadratic gradient term with a
space--time dependent but uniformly bounded target coefficient, and
`srcCarl_add` combines its two difference arms.  Their measurability inputs
remain explicit for later chart specialization.

## Current frontier

- The definitions and bilinear Carleson product proof are verified.
- The repair added the required Borel-measurable Euclidean model instances
  and closed the existing order/algebra steps; no theorem statement changed.
- No initial-slice derivative hypothesis is used.
- The Carleson-to-early-value heat-potential estimate is proved downstream in
  `HeatEarlyGlobal.lean`; `KochLammEarly.lean` identifies the `KLSource0`
  local `L¹` arm with this input.

Endpoint accounting remains unchanged: `ricci_flow_forward_unique` is 0%
until its exact theorem is proved and checked.  This file is supporting
machinery only.
