# ScalarPathReconstruct

## 2026-07-16 reconstruction and time derivative

The rank-zero reconstruction stage is now complete and focused verification
passes.  `scalarSpecSum` is the intrinsic scalar eigen-series.
`scalarMode_eq` and `scalarSpec_chart` identify its fully evaluated chart modes
without an equality of whole tensor or Hom objects.  `prodMode_majorant`,
`scalarMode_majorant`, `scalarTsum_chart`, and `scalarTsum_smooth` prove the
compact-patch M-test and full Euclidean-chart finite-order regularity.

`scalarSpec_local` composes the Euclidean scalar sum with
`x ↦ toEuclidean (extChartAt I α x)` on the actual chart source.
`scalar_path_recon` then globalizes by the chart-source open cover and proves
joint `C^N` regularity on `Icc a b × M`.  No global frame,
`HasLocallyConstantChartAt`, time-dependent smooth tensor representative, or
whole-bundle equality is used.

`scalarSpec_cc` now proves that the rank-zero spectral series of any smooth
tensor is its pointwise scalar readout.  The proof converges in one
supercritical spectral Sobolev space and applies the scalar point-evaluation
bound only after fully evaluating the rank-zero tensor.

`scalarSpec_d1` proves the exact pointwise termwise time-derivative statement
on a compact slab.  It applies `scalarMode_majorant` separately to the
coefficient family and its ordinary derivative, then uses the scalar
`hasFDerivWithinAt_tsum` engine.  The chart series is converted back with
`scalarSpec_chart`; no higher HeatSemigroup import or tensor-valued derivative
is introduced.  Focused verification passes.

The next frontier is the pointwise PDE assembly in
`ConjGalerkinClassical`: specialize this theorem to `galLim_jet_mass`, identify
the velocity series with a smooth-core frozen Laplacian, moving Laplacian
difference, and scalar-potential representative, then use the scalar
realization lemmas.  No new consumer assumption is required.

Honest accounting: `scalarSpec_cc`, `scalarSpec_d1`, and
`scalar_path_recon` are each proved (100%); their dedicated reconstruction and
time-differentiation machinery is complete (100%).  The intended
`heatpot_of_gallim` theorem is still unstated/unproved (0%) at this checkpoint;
its dedicated inputs are approximately 96%.  The broader classical
conjugate-heat machinery is approximately 96%, while the Perelman
noncollapsing endpoint is still unstated/unproved (0%).  The whole HCG
compactness project remains about 59%; these are upstream analytic producers,
not noncollapsing itself.
