# ScalarEigenJet

## 2026-07-16: rank-zero spatial series majorant

`scalarEig_jet_le` specializes the generic compact raw-component jet bound and
the generic covariant eigensection Sobolev estimate to rank `(0,0)`.  Its
conclusion is already in `iteratedFDerivWithin` normal form on the open chart
target, ready for the scalar spectral-series M-test.

No new geometric or convergence assumptions are introduced.  In particular,
the proof does not select a time-dependent smooth representative, does not use
`HasLocallyConstantChartAt`, and never asserts equality of whole Hom objects.

Focused verification passed after narrow refreshes of the two newly exported
upstream producers.  The next frontier is the local product-mode summable
majorant, followed by the chart-local scalar `tsum` regularity theorem.

Honest project accounting at this point: `scalar_path_recon` is not yet stated
or proved (theorem 0%); its dedicated machinery is about 85%.  The conjugate
heat realization endpoint and Perelman noncollapsing endpoint remain theorem
level 0%; this file advances only their upstream scalar regularity machinery.
