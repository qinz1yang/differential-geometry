# PointedConvergence

Source used: MSM135 Chapter 3 Definition 3.1 and the following paragraph on exhaustions by open sets, together with the chapter's pointed Cheeger-Gromov-Hamilton convergence setup.

Introduced definitions: `metricCovDerivStep`, `metricCovDeriv`, `metricDiffCovDerivAt`, `metricDerivNorm`, `metricDerivNormSupOn`, `MetricCPConvOn`, `MetricCInfConvOn`, `MetricCInfConvOnCompacts`, `MetricCInfConvData`, `ExhaustsByOpen`, `PointedCGHMaps`, `SourceDomain`, `sourceCompactSet`, `SourceDomainMetricData`, `SourceMetricCPConvOn`, `SourceMetricCPConvOnWindow`, `SourceMetricConvergenceData`, `SourceSpacetimeConvergenceData`, `FunctionPullbackTendsto`, `ScalarPullbackTendsto`, `RicNormPullback`, `PointedCGConverges`, and `SmoothCGHConverges`.

## 2026-07-24: squared Ricci-norm convergence retention

Added `RicNormPullback`, the canonical specialization of
`FunctionPullbackTendsto` to the intrinsic squared Ricci norm
`PDE.RicciFlow.ricciNorm`.  `SmoothCGHConverges` now retains this output in
`ricciNorm_converges`; both `ofSpacetime` and `ofRestrictPullback` take the
explicit concrete-produced convergence proof and preserve it.

This is data-layer plumbing, not a new endpoint assumption or a proof of
curvature convergence.  The concrete ConvOut construction must still derive
the field from smooth metric convergence.  Theorem 3.10 remains unstated here
and 0% unconditionally; this retention subtask is 100% checked, while the
project map's P4 consumer-machinery and whole-HCG estimates are unchanged.

Verification: focused verification and the exact exported-module refresh
passed.

The `C^p` definition is formalized using the displayed `sup_{0 <= alpha <= p} sup_{x in K}` condition. `metricDerivNorm` is now concrete: it uses the Levi-Civita connection of the reference metric `g` and the metric-induced tensor norm. The tensor `nabla^a(g_k - g_infty)` is represented as `nabla^a g_k - nabla^a g_infty`, which is the Lean-friendly form of the same expression by linearity of covariant differentiation.

`MetricCPConvOn` now takes compactness of `K` as an explicit hypothesis. The raw `metricDerivNormSupOn` remains available only as the low-level supremum used under that compactness hypothesis.

`ExhaustsByOpen` now records openness, monotonicity `U k ⊆ U (k+1)`, and eventual containment of every compact subset. `PointedCGHMaps` stores actual smooth `PartialDiffeomorph` data rather than an arbitrary predicate, and the projection helpers `source`, `target`, and `map` make clear that the semantic convergence lives on the open sources.

For MSM135 Definition 3.2, the file now has an HCG-local open-domain metric layer. `SourceDomainMetricData` keeps the source-subtype topology/manifold instances, restricted limit metrics, pulled-back sequence metrics, reference metrics, compact-preimage input, and the `mfderiv` inner-product formulas. `SourceMetricConvergenceData` and `SourceSpacetimeConvergenceData` are data-bearing convergence records, not arbitrary `Prop` placeholders.

`FunctionPullbackTendsto.le_of_bound0` is the reusable order-closure bridge for Section 12 pinching transfer: pointwise pullback convergence plus eventual upper bounds tending to zero gives arbitrary positive upper bounds on the limit value. `ScalarPullbackTendsto` is a concrete field of `SmoothCGHConverges`.

Frontier: the remaining honest backend is construction of the open-source subtype manifold metrics and their pullback/restriction formulas from general RicciFlower manifold infrastructure, plus the trace-free Ricci/pinching-ratio pullback convergence producer needed by Hamilton Section 12. These frontiers are located in the HCG source-domain and function-pullback layers, not hidden behind placeholder convergence predicates.

2026-05-27 review update: the fixed-manifold `C^p` convergence API and `SourceDomainMetricData` no longer expose a public `IsManifold I (∞ + 1)`/`smoothPlus` assumption. The derivative definitions and source-domain supremum derive `∞ + 1` locally from the stored `IsManifold I ∞` instance when a lower RicciFlower producer needs that exact instance.

Verification: passed for this file and for the Ricci-flow convergence wrapper.

2026-05-29 Lemma 3.11 update: added the first-order local-frame bridge for
the background covariant derivative of a metric tensor.  The new theorems
`metricCovDeriv_one_eval_smooth_slots`,
`metricCovDeriv_one_eval_localFrame`, and
`metricCovDeriv_one_component_localFrame` express the first displayed formula
in the second part of MSM135 Lemma 3.11 in terms of the concrete
`metricCovDeriv` API.  This connects the HCG convergence norm to local-frame
Christoffel/connection-difference estimates without introducing a new
placeholder operator for `nabla - nabla_k`.

Verification: passed for this file after the local-frame bridge.

2026-06-17 P4 packaging note: added
`SourceMetricCPConvOnWindow.of_derivNormSupOn` and
`SourceSpacetimeConvergenceData.of_derivNormSupOn`.  These are only the routine
assembly from already-separated ingredients: eventual compact containment in the
comparison-map sources (`PointedCGHMaps.source_subset`) plus raw uniform-on-window
bounds for `(D k).derivNormSupOn`.  They deliberately do not construct
`SourceDomainMetricData`, source-subtype metrics, or pullback/restriction
formulas; those remain the open source-domain backend.

Verification: passed for this file, with the new theorem axiom-clean under the
expected project axioms.

2026-06-17 source-domain compactness correction: narrowed
`SourceDomainMetricData.compact_preimage` to require the missing hypothesis
`K ⊆ Φ.source k`.  The previous all-compact statement would assert compactness
of `K ∩ source` for an arbitrary open source, which is false in general.  Added
`sourceCompactSet_isCompact`, proving the corrected statement by identifying the
source-domain set with `K` through the subtype image once `K` is contained in
the source.

Verification: passed for this file.

2026-06-17 source-domain canonical constructor: added
`SourceDomainMetricData.ofCanonical`.  It fills the canonical source-domain
topology, charted-space, T2, smooth-manifold, and compact-preimage fields using
the helpers above.  It still requires sigma-compactness, the restricted/pulled
metric families, and the two `mfderiv` inner-product formulas as inputs, so the
actual source metric backend remains visible instead of being hidden behind a
new assumption.

Verification: passed for this file.

2026-06-17 source-domain open-subtype note: `SourceDomain` is now the bundled
open source `sourceOpen Φ k`.  This aligns the source domain definition with
`PointedCGHMaps.source_open`, and the source compactness lemma continues to
check.  A temporary probe showed that the topology part is routine, but a
reusable charted/T2/smooth base-instance package should be added deliberately
with explicit `TopologicalSpace.Opens` bridges; plain `infer_instance` through
the current abbreviation did not close the charted/T2 goals.  I did not add that
public package in this pass, because the main remaining backend is still the
restricted/pullback smooth metric construction and its `mfderiv` formulas.

Verification: passed for this file; the new source-domain theorems are
axiom-clean under the expected project axioms.

2026-06-17 source-domain base package: added the canonical open-subtype
helpers `sourceDomTop`, `sourceDomCharted`, `sourceDomT2`, and
`sourceDomSmooth`.  The charted and smooth helpers use Mathlib's
`TopologicalSpace.Opens` chart/manifold route explicitly; this resolves the
previous plain-`infer_instance` obstruction without changing the metric
frontier.  Added `sourceDomSigmaOf` as a conditional sigma-compact bridge from
an explicit `IsSigmaCompact (Φ.source k)` set fact.  I did not claim automatic
sigma-compactness of arbitrary open sources, and I did not construct the
restricted/pullback smooth metrics.

Verification: passed for this file.

2026-06-17 target-domain and partial-diffeomorphism backend: added the
canonical target open-domain package `targetOpen`, `TargetDomain`,
`targetDomTop`, `targetDomCharted`, `targetDomT2`, `targetDomSmooth`, and
`targetDomSigmaOf`, plus `targetCompactSet_isCompact`.  Added
`sourceTargetDiff`, turning each stored `PartialDiffeomorph` into an honest
diffeomorphism between the bundled source and target open domains, with
projection lemmas for the forward and inverse maps.  The only nontrivial local
API needed was `contMDiff_openCod`: a map into an open subtype is `C∞` when its
ambient coercion is `C∞`; this was proved by `contMDiff_iff_target` and the
open-subtype chart identity.

That remaining backend is now closed by the metric-layer `OpenSubtype` and
`Pullback` updates.  Added `SourceDomainMetricData.ofRestrictPullback`, which
constructs the limit metric by restricting `L.S.family.metric t` to the source
open domain, constructs the sequence metric by restricting
`(X.term (subseq k)).S.family.metric t` to the target open domain and pulling it
back along `sourceTargetDiff`, and proves both stored inner-product formulas.
The theorem-facing inputs left are the honest sigma-compactness facts for the
source and target open sets plus the reference metric family used in
`metricDerivNormSupOn`.

Verification: passed for this file.

Added `SourceMetricConvergenceData.of_derivNormSupOn` as the spatial analogue
of the existing spacetime constructor: it folds source exhaustion into raw
per-time `derivNormSupOn` convergence of the supplied source-domain metric
data.  The remaining P4 analytic bridge is therefore the actual production of
those raw source-domain seminorm bounds for the restricted/pulled-back metrics.

## 2026-07-17 canonical comparison-map reindexing

Moved the shared structural reindexing layer here: `ExhaustsByOpen.comp_subseq`
and `PointedCGHMaps.compSubseq`.  Their qualified names and statements are
unchanged, so existing downstream dot-call consumers require no migration.
This lower placement lets the open-time P4 diagonal reindex its fixed
comparison maps without importing the endgame assembly.  Focused verification
of this file is green.

Added the definitional projection lemmas `compSubseq_source`,
`compSubseq_target`, and `compSubseq_map`.  They are the only comparison-map
readouts needed by the fixed-family open-window producer; the exact module
refresh is green.

Verification: passed for this file.

Added `SourceSpacetimeConvergenceData.toSpatial` and
`SmoothCGHConverges.ofSpacetime`.  Spacetime source-domain metric convergence
now supplies the per-time spatial metric convergence by applying the window
statement to `[t,t]`, so a later `SmoothCGHConverges` proof only needs maps,
scalar pullback convergence, and the spacetime metric-convergence record.

Verification: passed for this file.

Added `SourceMetricConvergenceData.ofRestrictPullback` and
`SourceSpacetimeConvergenceData.ofRestrictPullback`.  These constructors
instantiate the convergence records with the canonical
`SourceDomainMetricData.ofRestrictPullback` metrics.  The remaining input is
exactly the analytic seminorm convergence of those constructed source-domain
metrics, pointwise in time for the spatial record or uniformly on compact time
windows for the spacetime record.

Verification: passed for this file.

Added `SmoothCGHConverges.ofRestrictPullback`, composing the canonical
restrict/pullback source-domain metrics with scalar pullback convergence into
the final smooth CGH convergence record.  This does not discharge the analytic
P4 bridge: the theorem still explicitly requires uniform window convergence of
the seminorms of the constructed source-domain metrics.

Verification: passed for this file.
