# ActionAttainC1

## Result

`exists_lRegMinC1On` combines relaxed attainment with the finite-node
regularity theorem. On a strict nondegenerate interval it returns a curve that
is `C¹` on the full closed interval, has the prescribed endpoints, attains the
exact value `lRegCostC1`, and satisfies the genuine comparison inequality
against every global fixed-endpoint `C¹` curve.

The finite subdivision, chart centers, local `timeH1` representatives, and
recovery sequence used in the proof are hidden from the public conclusion.
The direct-method inputs are those of `exists_lRegMinC1`, with `a ≤ b`
replaced by the strict inequality needed by `lMinCurve_c1`. The direct-method
producer itself does not need positive model dimension; this corollary retains
the ambient `NeZero (finrank E)` instance required by the current verified
finite-node regularity chain. This is not a supplied Euler equation or
regularity hypothesis.

## Boundary

This is a `C¹` relaxed-action minimizer. It does not assert
`IsLRegCurveOn`, the classical regularized L-geodesic equation, or the terminal
`exists_lMinimizer` endpoint. Those require the separate classical Euler
identification.

## Verification and progress

Focused verification and the targeted module refresh passed without warnings
or placeholders. The proof uses the refreshed `ActionMinC1` export.

- `exists_lRegMinC1On`: 100%.
- Terminal `exists_lMinimizer`: 0%.
- `redVolume_anti`: 0%.
- Dedicated L-geometry machinery is about 96--97%; reused generic
  infrastructure for this corollary is 100%.
- P2 remains below 1%, and the whole Poincare program remains about 3--5%.
