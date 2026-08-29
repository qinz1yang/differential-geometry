# CostContinuity

## Result

`lCost_lt_event` proves the fixed-positive-time endpoint upper-continuity
brick. If a global `C¹` competitor from `x` to `y` at backward time `tau` has
regularized action strictly below `A`, then for every sequence `q n -> y`, the
costs `lCost S T x (q n) tau` are eventually below `A`.

The theorem uses the weakest honest strict-upper-bound input: a supplied
competitor with action below `A`. It does not infer existence of a competitor
from an `sInf` inequality on a possibly empty path class.

## Native proof route

The proof chooses a terminal chart interval for the supplied competitor. In
that chart it adds an affine `timeH1.rampUp` whose endpoint is the coordinate
displacement from `y` to `q n`. Finite-dimensional continuity of the ramp,
compact chart buffering, and `lAction_h1_lim` give convergence of the terminal
regularized actions. `exists_chartH1_join` attaches the perturbed tail to the
unchanged head, and `lAction_c1_dense` produces global `C¹` competitors with
the required endpoint. Action additivity and `lRegCostC1_le` then give the
strict cost bound.

Focused verification passes without warnings. No `sorry`, `admit`, new class,
foundational wrapper, or stronger geometric assumption was added.

## Varying-time ray result

`lCost_le_ray` proves that the cost to the endpoint of any positive
regularized L-ray segment is no larger than that segment's action. A smooth
time clamp globalizes the ray without changing it on the segment, so the
global-C1 cost comparison applies without assuming that the totalized ray is
globally smooth.

`lCost_ray_event` combines this comparison with `lRayAct_tendsto`. If
`Z n -> Z0`, `tau n -> tau0 > 0`, and the limiting square-root time lies in
the regularized ray domain, every strict upper bound for the limiting ray
action eventually bounds
`lCost S T x (lExp S T x (Z n) (tau n)) (tau n)`.

Both the focused source check and the targeted module refresh pass without
warnings.

## Remaining time-variable frontier

The corresponding theorem, tentatively `lCost_lt_param`, with arbitrary
independent endpoints `q n -> y` and `tau n -> tau` is not stated or proved
(0%).  This is the first lower producer toward the joint `(T,x)` parameter
stability later needed for `redVolume_lsc`.
The exact missing lower-layer producer is varying-length chart-action
continuity: for `L n -> L > 0`, after pulling curves on `[c, c + L n]` back to
one fixed interval, strong chart-`H¹` convergence should imply convergence of
the regularized actions. The current `lAction_h1_lim` requires one fixed
`lSegLen`, so it cannot compare the dependent spaces `timeH1 E (L n)`.

Three routes were checked:

1. Rescaling the whole competitor reduces the problem to a moving upper
   integration limit; `lRegAction_deriv` only differentiates a smooth
   variation on one fixed interval.
2. Adding or removing a short constant tail handles neither side uniformly:
   the shortening case still needs a local connector and a varying-interval
   action estimate.
3. Reusing `lAction_h1_lim` directly fails at its fixed segment-length type;
   endpoint ramps solve the spatial endpoint but not the changing time domain.

This looks like a missing analytic API lemma rather than a mathematical
obstruction. The endpoint half is complete; the time-domain half should be
developed below the cost theorem rather than hidden behind a consumer
assumption.

## Honest progress

- `lCost_lt_event` at fixed positive time: 100%.
- Varying-time cost upper continuity along regularized rays: 100%.
- Arbitrary-endpoint varying-time cost upper continuity: theorem not started
  (0%); its fixed-time endpoint machinery is complete, while dedicated
  varying-domain machinery is about 10% (route and exact API identified only).
- Minimizing-vector limit stability: theorem not stated here (0%); this file
  now supplies its varying-time ray-action/cost upper-bound input.
- Dedicated L-geometry machinery for this compactness/stability brick: about
  70%.
- Generic reused compactness, chart, `timeH1`, and density infrastructure:
  about 90% available.
- `redVolume_anti`: 100%, proved separately and focused-check green.
- `redVolume_zero_lim`: 100%, proved separately and focused-check green.
- `smooth_nlc`: 0%; the theorem is not yet stated.
- The final `poincare_of_inputs` theorem remains 0%; whole-program
  infrastructure is currently estimated at 15--25% under the P0--P9 workload
  denominator.
