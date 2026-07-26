# MetricCovDerivConv

## Purpose

This file is the metric-free compact-open convergence layer for the component
covariant-derivative recursion. It is intentionally below the Step B1 metric
consumer: it does not mention stage comparison maps, pullback metrics, or any
compactness input bundle.

## Current state

The fixed polynomial one-step map and its local identification with the
constant-frame `iterCovComp` successor are complete. The public theorem
`iter_comp_conv` proves that compact-open smooth convergence of the base array
and Christoffel array propagates through every finite tower level.

The public specialization `iter_comp_zero` proves that when the base arrays
converge to zero, every finite component covariant-derivative tower converges
to zero. The public statements inline the constant model-space frame and do
not expose a private implementation definition. Both public theorems passed
focused verification without warnings, and the module refresh passed.

## Remaining B1 bridge

This module closes only the metric-free recurrence-continuity brick. The
Step B1 consumer still needs the following producer-side identifications:

1. Derive fixed-frame Christoffel-component convergence from normal-coordinate
   metric convergence. The intended existing chain is bilinear-to-linear
   conversion, `MapCInfConvOnCompacts.ringInv`,
   `IsCoercive.sharp_eq_inverse`, and the Koszul expression. The existing H6
   half-coercivity estimate supplies invertibility; this must not become a new
   compactness input.
2. Identify the coordinate pullback coefficient error with the fixed-frame
   components of
   `hpb.pullback - metricTensorField g` on the retained normal-coordinate core.
3. Apply `iter_comp_zero`, identify `iterCovComp` with `iterCov`, pass from the
   finite component bounds to the tensor norm, and transport the result by the
   existing normal-quarter partial diffeomorphism and `covNormWith_pd_zone`.
4. Run the reverse argument only for the exact local inverse. The opposite
   stage comparison map remains an approximate return map and is not the exact
   inverse required by `StepB1RawInput`.

No C4 consumer and no new input field are introduced here.

## Honest accounting

- `iter_comp_conv`: complete (100%).
- `iter_comp_zero`: complete (100%).
- Dedicated coordinate-jet-to-intrinsic-covariant-bound pipeline: about 25%;
  the recurrence-continuity core is now checked, while the Christoffel producer,
  exact coefficient realization, norm passage, and exact-inverse consumer
  remain.
- `StepB1RawInput` producer theorem: not yet proved (0%).
- Textbook Step B1 endpoint: not yet proved (0%).
