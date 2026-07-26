# MetricWkpData

## Endpoint supplied by this file

`metricDiff_wkp3_bdd` is the intended data-entry theorem for the uniform
short-time-existence lane.  For a family `gSeq` satisfying the existing
exact-order bounds

`MetricCovDerivOrderBoundOn univ q (gSeq k) gBase B`, for every `q <= 3`,

it produces one real number `C >= 0`, independent of `k`, such that every
fixed-background metric difference belongs to `MemWkpTensor 3 p` and has
`wkpTensorNorm` at most `ENNReal.ofReal C`.

The endpoint now consumes `MetricWkpTerms.metricDiff_wkp_terms` directly for
the per-chart scalar membership and bounds.  This keeps the finite-atlas
tensor packaging in this file while avoiding a second invocation of the
compact-jet-to-`W^{3,p}` argument.

The theorem does not consume Lambda-ellipticity.  This is intentional:
ellipticity controls the principal parabolic operator, whereas this theorem
only controls the size of the initial-data family.  Thus the conjunction of
the C3 bounds and Lambda-ellipticity implies the result, with the stronger fact
that the C3 bounds alone suffice.

## Geometric conversion

`metricDiff_comp_jet` is retained as a compatibility API for
`MetricHolderData.metricDiff_c2half`.  The direct producer beneath
`metricDiff_wkp3_bdd` is now `MetricWkpTerms.metricDiff_fam_jet`, packaged by
`metricDiff_wkp_terms`.

1. The base metric and the varying family are combined as an `Option` family,
   exactly as in `LowRegCoefficients.lean`, so the chart Gram difference has
   uniform constants on both arms.
2. `chartGram_pou_le` converts the intrinsic exact-order bounds into uniform
   order-0-through-order-3 Frechet bounds for the chart Gram entries on every
   active POU support.
3. `gramDiff_eqOn` identifies the raw metric-difference component with the
   Gram-entry difference on the chart-target interior.
4. `norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE` transfers
   the raw component from `E` coordinates to the canonical Euclidean chart
   coordinates.
5. The POU Leibniz formula gives a uniform third-order bound for the actual
   chart component.  Outside the POU kernel it is locally zero.

The common compact set for a fixed chart is exactly
`chartPouKernel alpha`.  Its compactness, containment in the chart target, and
the support inclusion

`tsupport (tensorChartComponent ...) subset chartPouKernel alpha`

are existing public theorems.  No compact support or uniform constant is
inferred from smoothness alone.

## Analytic conversion

For each fixed chart, `metricDiff_wkp_terms` supplies simultaneous scalar
`MemWkp 3 p` membership and a uniform scalar norm bound.  The final tensor
norm remains a finite sum over the existing `chartAtlasPOU_finset` and the two
finite component-index types.

## Verification state

Both the compatibility component producer and the tensor packaging theorem
are source-written.  The direct `metricDiff_wkp_terms` consumption edit has
not yet been Lean-checked because a named shared build is active.  The file is
below 3000 lines and contains no `sorry`, `admit`, axiom, opaque declaration,
public or foundational instance, notation, or heartbeat setting.  Its only
local instance is the canonical completeness of the finite-dimensional model
space `E`, already supplied by the existing analysis API.

The most likely elaboration-only frontiers for the first focused check are:

- coercing `m : Fin 4` through `chartGram_pou_le` and the finite Gram-constant
  sum;
- rewriting the `EqOn` Gram difference through
  `iteratedFDerivWithin_congr` after unfolding `metricDifferenceCcTensor`;
- inference of the finite-sum witnesses in the final `wkpTensorNorm` collapse.

These are not known mathematical gaps.  If one fails, the smallest repair is
an explicit type annotation or local equality; no extra regularity or
ellipticity hypothesis should be introduced.

Honest status: mathematical machinery 90%; Lean verification 0%; exact
`ricci_flow_unif_existence` endpoint remains 0% until this producer and the
subsequent uniform maximal-regularity solver are checked and assembled.
