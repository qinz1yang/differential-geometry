# HamiltonBound

## Purpose

This module substitutes the integrated Hamilton trace identity into both the
strict-region and positive-start tail reduced-length Laplacian comparisons.

## Status

Focused verification passes without warnings.  The established strict endpoint
`redLength_lap_K` remains unchanged.  The new public endpoint `lTail_lap_K`
proves

```text
Delta branch(alpha(A0,b))
  <= n/(b-a) - 2*b*R(alpha(A0,b)) - lKTail(alpha(A0,-),a,b)/(b-a)^2.
```

It retains the exact full-span minimizing-ray and positive-start family prefix
of `lTail_lap_le`.  The only additional field data are a terminal-orthonormal
adapted family, its adapted ODE on `[a,b]`, and `C^8` smoothness on a neighborhood
of `[0,b]`.  Index-density and Ricci-density integrability are derived
internally.  There is no `CompactSpace`, scalar-sign, Hamilton-integrability,
desired-inequality, `sorry`, or `admit` assumption.

The family center is aligned with the canonical `lRegCurve` by existing germ
congruence APIs.  Tangent fields are transferred only through their model-space
values; the proof does not unfold or compare tangent-bundle or Hom
representations.  `lIndex_trace_pos` gives the traced index identity,
`lTraceInt_pos` supplies the Hamilton tail integral, and `lTail_lap_le` supplies
the raw branch Laplacian comparison.

Earlier failed elaboration attempts were local: dependent equality transport
through the totalized ray, ordered-interval coercions, and a division-ring
normalization.  Direct model-space transfer, explicit interval inclusions, and
the nonzero fact `b-a != 0` resolved them; no API or mathematical blocker
remains.

`lTail_lap_K` and its dedicated Hamilton-tail assembly are **100%**.  The
all-point spacetime weak upper support, `exists_redLen_le`,
`redVolume_late_low`, `smooth_nlc`, P2, the capstone `redVolume_anti`, and the
final Poincare endpoint remain **0% theorem endpoints**.  Dedicated L-geometry
across the still-open L8--L9 endpoints is about **60--62%**; reused generic
infrastructure is **100%**, and whole P0--P9 infrastructure remains
**15--25%**.

The next exact small theorem is the local fixed-time inverse compatibility
adapter `lTailInv_slice`.  It identifies the spatial component of the joint
endpoint-time local inverse with the fixed-`b` inverse near the central endpoint,
allowing one weak support function to consume both `lTailJoint_mfd` and
`lTail_lap_K`.  It should be proved by local inverse uniqueness, without a new
public equality assumption.
