# ConvFieldOpenScalar

## 2026-07-17 open-window scalar readout

`OpenConvOut.scalar_conv` chooses a canonical compact window containing each
carrier time of the book-facing open interval and invokes the pointwise
`ConvOut.scalar_conv_at` producer there.  One global subsequence and one global
limit metric family are inherited from `OpenConvOut`; no equality of
independently produced window limits and no whole-interval closed-window
containment is assumed.

Focused verification passes without warnings. This theorem is an additive
open-interval readout and has no existing downstream call site yet.

## 2026-07-18 grow-local input propagation

The scalar readout now carries the revised grow-local `hcovTail` interface.
Its proof is otherwise unchanged. Focused verification and the exact module
refresh pass.

## 2026-07-24 open-window Ricci-norm readout

`OpenConvOut.ricNorm_conv` uses the same canonical compact-window selection as
`scalar_conv` and reads the genuine pointwise `ConvOut.ricNorm_conv_at`
producer. Its result is the fully evaluated real-valued convergence from the
source-flow intrinsic squared Ricci norm to the AA limit metric's intrinsic
squared Ricci norm; no flow-limit cast or extra convergence assumption appears
at this layer.

Source wiring and focused verification pass with no diagnostics. The required
`ConvFieldPDE` producer and this open-window readout are both exact-current.
