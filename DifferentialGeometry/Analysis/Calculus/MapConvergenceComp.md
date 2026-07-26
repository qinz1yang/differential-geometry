# MapConvergenceComp

## 2026-07-15 canonical placement

The generic moving-composition theorem and fixed constant/product/finite-Pi/CLM
closures now live in the analysis calculus layer. The new
`MapCInfConvOnCompacts.ringInv` composes convergence with smooth Banach-algebra
inversion on the open unit locus; it introduces no metric-specific input.

Focused verification passed, and the old HCG import path remains a checked
compatibility module. A proposed fully generic bilinear closure was discarded
after it caused unnecessary elaboration cost; the spray proof instead composes
the existing APIs at concrete finite-dimensional types.

## 2026-07-16 finite varying-domain extraction

`exists_cInf_finite` is the canonical finite-family diagonal at the analysis
layer. Each member may have its own domain and may refine any already selected
strict subsequence. The proof recursively extracts one member and preserves all
earlier limits through `MapCInfConvOnCompacts.comp_tendsto_atTop`; it introduces
no HCG-specific data or extra compactness assumption.

Focused verification passed. This generic extraction API is complete. It is
supporting machinery only: the concrete `NormalMetricConv` producer and
`StepB1RawInput` remain separate downstream theorems.

The extractor also preserves an arbitrary predicate on each selected limit,
so geometric consumers retain smoothness and metric equivalence together with
convergence. Its index assumption is the minimal `Finite` instance; the proof
installs a local `Fintype`. Focused verification and the targeted refresh
passed.

## 2026-07-16 three-index tail

`MapCInfConvOnCompacts.three_tail` turns convergence along every triple of
reindexings tending to infinity into one common tail in all three indices, for
each compact core, finite derivative order, and positive tolerance.  Its proof
is the direct bad-triple diagonal argument, so it adds no smoothness or
geometry assumption.  Focused verification passed.

This closes the generic quantifier-order brick needed by the moving-reference
center route.  It does not itself construct the HCG center family or the
`StepB1RawInput` producer; those theorem endpoints remain 0%.

## 2026-07-16 pullback-form closure

`MapCInfConvOnCompacts.pullbackForm` is the canonical analysis-layer adapter
for a varying bilinear-form field and a varying continuous-linear-map field.
It first uses the existing product closure on `(B_k,D_k)` and then composes
with the fixed smooth polynomial `pullbackForm`; no duplicate metric-specific
API was introduced.

The statement retains the exact `ProperSpace` hypothesis on the intermediate
product demanded by the generic moving-composition theorem.  In the intended
finite-dimensional chart application this is inferred from the existing
instances.  Focused verification passed.  This closes the polynomial
contraction brick only; the chart-to-intrinsic metric bridge and the
`StepB1RawInput` producer remain separate, unstated endpoint theorems (0%).

## 2026-07-16 rectangular pair tails

`mapCInf_pair_tail` is the generic bad-sequence extraction from compact
`C∞` convergence along every pair of cofinal reindexings to one common
two-index rectangular tail.  It keeps only the normed-space assumptions needed
by `mapDerivNorm` and avoids repeating this diagonal argument in C4 consumers.

Focused verification passed.  This is quantifier-order infrastructure only;
the chart-to-intrinsic bridge and `StepB1RawInput` remain separate endpoints.
