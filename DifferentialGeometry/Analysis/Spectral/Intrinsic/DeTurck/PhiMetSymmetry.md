# Ricci--DeTurck top-coefficient symmetry

## 2026-07-15 arbitrary realized metric

`phiMet_symm_zero` proves that, at an arbitrary realized metric, the
Ricci--DeTurck top coefficient agrees with its pure-cometric part on tensors
which are symmetric in the two derivative slots.

`gradSwapCurvCoeff` fixes the background-curvature coefficient supplied by the
covariant-derivative commutator.  `phiMetCurvCoeff` composes it with the
non-pure top coefficient, and `phiMet_curv_fold` proves the exact identity
turning that coefficient applied to `nabla^2 S` into a zeroth-order coefficient
applied to `S`.  The fold holds for every covariant two-tensor `S`; no symmetry
hypothesis on `S` is used.

Focused verification passed.  A first local section-extensionality proof of
application associativity exposed a tensor-bundle instance inference problem.
The correct repair was to reuse the already public
`appCcRS_zero_eq_appCc`/`appCc_assoc` API rather than duplicate the old private
DeTurck helper.

At this historical checkpoint the fold theorem was complete (100%), while the
mixed `H^3 -> H^1` remainder theorem was unstated and its dedicated machinery
was estimated at 65%.  The proposed pointwise low-order-coefficient producer is
superseded by the 2026-07-18 normal-form ruling: that interface cannot be
closed on the candidate `H3`-bounded, `H2`-small Sobolev contraction ball, and
the viable replacement is the integral `H1 x H2 -> H1` product route recorded
in `LowRegRemainderH1.md`.

## 2026-07-16 public dependency migration

The module no longer imports the oversized remainder implementation. The Lie
principal readout now comes from `DeTurckLieCoeffAppCcValue`, and the gradient
slot commutator comes from the new public `gradSlot_sub_eq_curv` producer.

The source migration was complete, but its downstream focused verification was
temporarily blocked at this checkpoint.  The approximately 78% machinery
figure was historical and is superseded by the later route ruling.

## 2026-07-18 verification repair

The module already imported `GradSlotCurvature`, but its selective opening of
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral` omitted
`gradSlot_sub_eq_curv`.  Adding that one canonical name repairs the stale
visibility failure.  The named downstream target build and this file's focused
source check pass.  `phiMet_symm_zero` and `phiMet_curv_fold` remain 100%; the
unconditional mixed remainder and uniform-existence endpoint remain 0%.
