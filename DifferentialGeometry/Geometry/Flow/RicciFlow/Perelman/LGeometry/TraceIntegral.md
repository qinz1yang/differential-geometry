# TraceIntegral

## Route

`lTraceInt_eq` integrates `lTrace_deriv` along the canonical regularized
L-ray.  Pointwise orthonormality is propagated backward from the terminal
orthonormal family by `lAdapted_inner_eq`.

`lTraceInt_pos` is the positive-start counterpart on `0 < a < b`.  It applies
the weight `((s-a)/s)^2` to the existing derivative of `s^3 R`, equivalently
using

```text
G(s) = s * (s-a)^2 * R(s).
```

The private data proof derives integrability of the weighted Hamilton density
from the derivative and the supplied weighted index-density integrability; it
does not assume the desired identity or a Hamilton-integrand bound.  The
resulting integral is exactly the scalar density occurring in
`lIndex_trace_pos`.

`lKTail` packages twice this weighted square-root-time Hamilton integral, and
`lKTail_sq` proves its raw-time form with weight
`sqrt(rho) * (sqrt(rho)-a)^2` under only `0 <= a <= b`.

`lKTail_tendsto` rewrites the varying-lower-limit tail as a fixed `[0,b]`
interval integral with the indicator `a < s`.  The weight lies in `[0,1]`
there, so `|lHamSq|` dominates it; `lRayHam_int` supplies the honest L1 input.
For every `s > 0` the indicator is eventually active and the weight tends to
one, so filter dominated convergence gives the right-hand limit at zero.

Scalar curvature along the ray is proved smooth on the open maximal
regularized domain by composing `lRegCurve_smoothOn` with fixed initial
tangent and then composing with `scalar_joint`.  This makes the derivative of
`s^3 R` continuous and interval integrable.  Existing index-density
integrability and scalar-path continuity give the traced density integrable;
the pointwise derivative identity then also gives `lHamSq` integrable, so the
fundamental theorem of calculus applies without a separate Hamilton-integrand
regularity assumption.

## Status

Focused verification passed without warnings for the positive-start additions
and `lKTail_tendsto`.

## Project status

- `lTraceInt_eq`: proved and focused-check verified (100%).
- `lKTail`, `lKTail_sq`, and `lTraceInt_pos`: proved and focused-check verified
  (100%).
- `lKTail_tendsto`: proved and focused-check verified (100%); its dedicated
  fixed-interval dominated-convergence machinery is also 100%.
- Dedicated Hamilton trace integration machinery in this file: verified (100%).
- The downstream `redVolume_anti` capstone is now proved in
  `ReducedVolume.lean`; it is not counted as a theorem of this file.
- The all-point spacetime weak barrier, `exists_redLen_le`, `smooth_nlc`, and P2
  remain theorem endpoints at 0%; this trace brick does not count as completion
  of those consumers.  Dedicated L-geometry across the still-open L8--L9
  endpoints is about 56--58%, reused generic infrastructure is 100%, and
  whole P0--P9 infrastructure remains estimated at 15--25%.
