# SlotTransportPairing

## Purpose

This module is the generic home for the natural passenger-slot recurrence
needed to move powers of `1 - Δ∇` through an operator-field energy pairing.
The route keeps every newly differentiated slot as a leading passenger; it does
not use a slot swap or a `secondCovGrad` commutator.

## Current producer

- `slot_pair_step` is the exact single-step recurrence.  Green's identity
  lowers the connection-Laplacian power once, `covGrad_iterL` exposes the
  curvature commutator sum, and `covGrad_appCcRS_eq` separates the
  differentiated coefficient from the passenger-extended coefficient.  The
  unexpanded final pairing contains the next main term with `slotExtend C` and
  the three genuine error families.
- `slot_iterL_pair` is now stated and implemented in source.  Its top term uses
  the composition-friendly normal form `(s + 1) + n`,
  `slotExtendIter g (s + 1) (s + 1) n C₀`, and
  `iteratedCovGrad g 0 (s + 1) n (covGrad g 0 s U)`.
- `slot_iterL_unif` is the compact-parameter producer.  It assumes one
  pointwise jet envelope `B i` for the whole family on a parameter set and
  chooses a single slot-transport constant before the parameter and input
  tensor.

The internal route is rank-generic.  `slot_stage_bound` expands one recurrence
step and bounds the zeroth-order and differentiated-coefficient arms with
`iterL_window_pair`; both curvature arms use `curv_iterL_pair_le`.
`slot_main_bound` telescopes those stage estimates.  The public theorem then
adds the initial `covGrad_iterL` curvature sum and shifts the two gradient
windows back from `covGrad U` to `U`.

The uniform route factors the same proof through `ShiftWin`,
`shift_win_of_bdd`, `slot_stage_unif`, and `slot_main_bdd`.  Repeated
passenger extension costs the explicit intrinsic envelope
`(finrank ℝ E)^m * B i`; a differentiated coefficient uses `B (i + 1)`.

No new geometric, convergence, or consumer assumption is introduced.

## Proof accounting

The passenger recurrence is specialized at

`C = slotExtendIter g (s + 1) (s + 1) m C₀`

and the corresponding shifted covariant jet, then telescoped over `m < n`.
The endpoint bounds the difference between the initial pairing and the fully
passenger-extended top pairing by
`K * J_(n+1)(U) * J_(n+2)(U)`.

## Verification

Focused verification of the fixed theorem passes without warnings.  The proof required only
local normal-form repairs: direct additivity of the smooth `L²` pairing,
explicit finite-window indices, and fully parenthesized curvature summands.
No theorem statement or analytic assumption changed.

`slot_iterL_pair` and its dedicated passenger-slot machinery are complete
(100%) as declarations in this module.  This is a producer result only: it does
not by itself complete the scalar `cc_comm_pair` consumer, the non-autonomous
bootstrap, or the Perelman endpoint; those theorem-level percentages remain
governed by the live Perelman and project-map notes.

`slot_iterL_unif` and its uniform slot machinery are now 100% focused-verified.
The last repair was only the rank-zero base-case normalization
`(finrank ℝ E)^0 = 1` in `slot_iter_bdd`; no theorem statement or analytic
assumption changed.  The Perelman endpoint remains 0%.
