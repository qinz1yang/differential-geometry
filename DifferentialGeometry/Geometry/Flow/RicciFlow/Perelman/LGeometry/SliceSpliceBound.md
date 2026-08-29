# Fixed-slice uniform splice bound

`SliceSpliceBound.lean` specializes the verified finite-chart splice estimate
to two fixed forward slices `a0 < a1` and terminal times in a half-open bounded
interval.

## Results

- `sqrt_gap_low` rationalizes the difference
  `sqrt (T - a0) - sqrt (T - a1)` and bounds it below by the fixed positive
  number `(a1 - a0) / (2 * sqrt (omega - a0))`.
- `redLen_slice_bound` sets `b = sqrt (T - a0)` and
  `c = sqrt (T - a1)`.  It proves the affine splice stays between the two
  fixed slices, applies `redLen_cover_bound`, and bounds all numerator and
  denominator terms by one constant independent of `T`, the chart, and the
  concrete ray.

The second theorem still consumes a concrete minimizing ray and its
low-reduced-length estimate.  It does not assume that such a ray exists and
does not state a reduced-volume lower bound.

## Verification

Focused verification passed without warnings after repairing routine local
normalization and interval-projection issues.  The named module artifact was
refreshed successfully, and the source contains no `sorry`, `admit`, or added
axiom.

## Remaining late-time inputs

After verification, the geometric splice and half-open-time arithmetic will be
complete.  The genuine all-point barrier must still produce the concrete
low-reduced-length ray.  A later assembly theorem can then apply
`redVolume_set_low` to the measurable set and positive volume floor returned
here.

`redVolume_late_low` remains 0%.  Its dedicated late-time-floor machinery is
roughly 50--55% complete after this verified producer; generic reused
infrastructure is tracked separately.
