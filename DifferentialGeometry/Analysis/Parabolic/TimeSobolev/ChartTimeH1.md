# ChartTimeH1

## Scope

This file is the generic fixed-chart bridge from a manifold-valued `C¹` curve
to the existing vector-valued `timeH1` API. It also records the chart-change
compatibility of arbitrary existing `timeH1` coordinate representatives of
one continuous manifold curve. It does not define a new manifold-valued
Sobolev space.

The chart condition is explicit: the curve maps the whole compact time
interval into the source of one fixed `chartAt`. The realized coordinate curve
is exactly `extChartAt I p ∘ gamma`.

## API

- `chartCoord_contDiff` proves that the fixed-chart coordinate curve is `C¹`.
- `chartTimeH1` applies the existing `timeH1.ofContDiffOn` constructor.
- `chartTimeH1_toFun` identifies its continuous representative.
- `chartTimeH1_deriv` identifies its weak derivative almost everywhere with
  the ordinary derivative of the coordinate curve.
- `curve_cont_of_h1` recovers continuity of a manifold curve from any fixed-
  chart `timeH1` representative on a subinterval; it does not require a
  supplied `C¹` proof for that curve.
- `curve_cont_local` gives the assembly-ready shifted version for a local
  representative on `[0, b-a]` of the original curve on `[a,b]`.
- `curve_mdiff_local` proves that such a representative makes the original
  curve manifold differentiable almost everywhere on the interior.  It uses
  the chart inverse only within `range I`, so it does not require
  `I.Boundaryless`.
- `chartH1_overlap` proves the genuine weak derivative transition law for any
  two `timeH1` coordinate representatives of the same curve.
- `chartH1_overlap_c1` specializes this law to the two canonical realizations
  of a `C¹` curve.

## Verification and frontier

Focused verification passes without warnings or placeholders. The upstream
`TimeH1` artifact was refreshed after the new `timeH1.chain_ae` export because
this downstream module uses it.  The local differentiability bridge also
passes focused verification.

The weak overlap theorem uses Mathlib's relative `tangentCoordChange`, so it
needs only `IsManifold I 1 M`; it does not strengthen consumers with
`I.Boundaryless`, finite dimensionality, compactness, a metric, or Ricci-flow
data. Finite time-chart localization is now available separately. The
remaining global direct-method work is finite diagonal extraction and assembly
of the local lower-semicontinuity inequalities, without introducing a
foundational manifold-H1 class.
