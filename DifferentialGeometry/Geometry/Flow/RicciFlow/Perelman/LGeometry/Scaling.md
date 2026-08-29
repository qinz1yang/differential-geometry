# Parabolic scaling for L-geometry

## Purpose

`Scaling.lean` proves that the regularized L-geodesic equation, its maximal
square-root-time domain, and the totalized L-exponential map commute with the
native parabolic rescaling of a Ricci flow.

Write `c = sqrt R`, `S_R = paraSolution S t0 R`, and
`T_R = paraBack t0 R T`.  A regularized curve for `S` is reparameterized by
`r ↦ alpha (c⁻¹ r)`, and its initial L-vector becomes `c⁻¹ Z`.  Conversely, a
curve for `S_R` is reparameterized by `s ↦ beta (c s)`.

## Verified API

- `lRegAccel_para`: the scaled regularized acceleration is `R⁻¹` times the
  original acceleration after square-root-time and velocity rescaling.
- `isLRegCurve_para`: sends an original regularized L-curve witness to a
  scaled witness.
- `isLRegCurve_unpara`: sends a scaled witness back to the original flow.
- `lRegDomain_para`: identifies the maximal regularized domain with
  `sqrt R • lRegDomain S T x Z`.
- `lRegCurve_para`: identifies the two totalized maximal regularized curves.
- `lExpDomain_para`: proves backward-time domain membership is invariant under
  `tau ↦ R * tau`.
- `lExp_para`: proves the corresponding equality of totalized L-exponential
  maps.

The connection step reuses `covDerivAlong_scale` from the generic Riemannian
layer.  The proof fully applies metrics and Ricci tensors to tangent vectors;
it does not compare bundle-valued or Hom-valued representations.

## Proof notes

The inverse-scaling route is proved directly.  Applying the forward theorem a
second time at reciprocal scale would require transporting between dependent
`RealTimeInterval` and `SolutionOn` structures, while the native inverse
rescaling API currently lives only at the `SolutionFamily` component level.

Two local elaboration issues were resolved without changing the mathematics:
the derivative scaling proof transports the scalar argument explicitly before
using linearity, and the initial-velocity identity uses commuting scalar
actions rather than normalization by ring automation.

## Verification and status

Focused verification passes without warnings.  The file has no `sorry`,
`admit`, or new axiom.  The parabolic-scaling part of L3 is complete.  The next
L3 endpoint is pullback naturality; L4 then begins with L-Jacobi fields and
second variation.

`redVolume_anti` remains unstated and unproved (0%).  Dedicated L-geometry
machinery is about 30%; generic infrastructure reused by this lane is about
75%; P2 itself remains below 1%, and the whole Poincare program remains about
3--5%.
