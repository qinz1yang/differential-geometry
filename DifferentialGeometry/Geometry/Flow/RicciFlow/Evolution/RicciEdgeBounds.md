# RicciEdgeBounds

## Verified producer (2026-07-18)

`ricciEdgeMetric` is proved without `sorry` and passes a warning-free focused
check.  It consumes exactly the joint chart-Gram `C0` regularity already present
in `ricci_flow_forward_unique`.  For every compact initial slab
`Icc a c` with `c < b`, it produces one `Lambda >= 1` such that, simultaneously
for every `t`, point, and tangent vector on that slab,

```text
Lambda^-1 * g(a)(v,v) <= g(t)(v,v) <= Lambda * g(a)(v,v).
```

The proof uses the canonical chart-Gram-to-bundled-tensor continuity bridge.
It bounds the evolving metric on the compact `g(a)`-unit tangent slab and the
initial metric on the compact evolving-unit time slab; combining the two bounds
gives the two-sided constant.  No Ricci bound, PDE integration, uniqueness, or
new endpoint hypothesis is used.

Accounting: this zeroth-order producer is 100%.  The exact theorem
`ricci_flow_forward_unique` remains 0%.  Its initial-edge metric-equivalence
subbrick is now 100%; its fixed-background order-one bound and weighted
order-two bound remain 0%.

## Exact remaining edge producer

The next analytic theorem should consume the same chart-Gram smoothness and
continuity fields plus the existing Ricci PDE field, and prove a short window
`a < c < b` and a constant `A` with

```text
metricCovDerivNorm 1 (g t) (g a) x <= A
sqrt (t - a) * metricCovDerivNorm 2 (g t) (g a) x <= A
```

for every `t in Ioc a c` and `x`.  A suitable public name is
`ricciEdgeDeriv`.  This is the precise order-one/order-two part still missing
from the proposed aggregate `ricci_edge_bounds` package.

## Routes audited for the derivative part

1. **Interior chart compactness.**  Joint `C-infinity` on `Ioo a b` gives
   bounds on each `Icc (a + delta) c`, but direct compactness cannot make them
   uniform as `delta` tends to zero.  `C0` convergence of the coefficients at
   `a` does not control their spatial derivatives.  Classification: invalid
   topological inference; a boundary parabolic estimate is required.
2. **Time shift plus the existing Shi machinery.**  The available
   `movingShiBoundN`/`movingShiBoundSol` first require a uniform curvature bound
   on the whole solution slab and are dimension-three producers.  The exact
   forward-uniqueness hypotheses are dimension-generic and carry no such
   curvature bound.  The repository also has no uniform-in-shift bridge from
   those moving curvature bounds to the displayed fixed-background metric
   derivative estimates.  Classification: missing analytic producer/API, not
   a routine adapter.
3. **Gauge-fixed boundary regularity.**  Ricci-DeTurck or harmonic-map heat-flow
   Schauder estimates would faithfully yield the edge bounds, but the repository
   has no harmonic-map heat-flow existence package, gauge PDE identity, or
   boundary regularity theorem for an arbitrary geometric Ricci flow.
   Classification: substantial parabolic/gauge infrastructure.

No route produced a counterexample to the existing forward-uniqueness
statement.  The obstruction is formalized analytic groundwork, not evidence
that the endpoint statement is false.

## Source implementation (2026-07-19)

Three additional honest PDE bridges are now implemented in the Lean source.
They introduce no derivative-bound hypothesis and are dimension-generic.

- `ricciEdgeChartPDE` converts the exact geometric metric PDE on `Ico a b`
  into the existing `jetRicciFlow (jet2 chartGram)` equation on `Ioo a b`.
  It composes `chartGramEntryPDE_of_metricPDE` with
  `chartGramEvolution_of_pde`; static spatial `C∞` follows from each
  `SmoothRiemannianMetric` slice.  This is intentionally labelled *weakly*
  parabolic: the ungauged Ricci symbol retains the diffeomorphism kernel.
- `ricciEdgeIntegral` proves on every strict interior interval
  `[s,t] ⊂ (a,b)` that
  `g(t)(v,w)-g(s)(v,w) = ∫_s^t -2 Ric(g(r))(v,w) dr`.  The existing
  `ricciCont_interior_of_chartGram` gives integrability from the endpoint's
  joint-interior `C∞` field, while the raw PDE gives the ordinary derivative.
- `ricciEdgeImproper` sends `s → a+` in that identity.  It concludes that the
  interior Ricci integrals converge to `g(t)(v,w)-g(a)(v,w)`.  The conclusion
  is deliberately an improper limit, not a claim that Ricci is Lebesgue
  integrable on `[a,t]`; the endpoint assumptions do not yet supply such a
  majorant.

These source proofs have been statically reviewed and contain no
`sorry`/`admit`/axiom/opaque declaration.  A focused Lean check was not run in
this lane because the workspace had the single coordinated named build still
active; verification therefore remains pending.

**2026-07-25 VERIFIED (B-lane planner).** First authoritative
`lake build +…RicciEdgeBounds`: two mechanical direction errors repaired
(`:221` needed `.symm` on `metricRicciAt_apply_eq_ricciTensor`; `:266` needed
`heq.symm` in `Tendsto.congr'`), then GREEN (9416 jobs).  `#print axioms` via
direct lean: all four public theorems (`ricciEdgeMetric`, `ricciEdgeChartPDE`,
`ricciEdgeIntegral`, `ricciEdgeImproper`) depend on exactly
`[propext, Classical.choice, Quot.sound]`.  This file is now settled verified
API for the forward-uniqueness lane.

## Updated obstruction audit

The new bridges sharpen rather than remove the analytic obstruction.  Three
mathematically different continuations were checked.

1. **Use the ungauged chart equation directly.**  `ricciEdgeChartPDE` makes
   this route exact, but `jetRicciFlow` is only weakly parabolic.  Its principal
   symbol has the diffeomorphism kernel recorded in `StrictParabolicity.lean`.
   Hence no boundary Schauder or maximal-regularity estimate for first/second
   fixed-background derivatives follows from this equation alone.
2. **Integrate the metric PDE from the edge.**  `ricciEdgeIntegral` and
   `ricciEdgeImproper` complete everything available from scalar time FTC.
   They control the metric coefficients pointwise in time, but differentiating
   the identity in space would require an integrable edge majorant for
   `∇Ric`/`∇²Ric`, which is exactly stronger spatial regularity than is known.
   Thus this route is circular for `ricciEdgeDeriv`.
3. **Pass to Ricci--DeTurck/harmonic-map gauge.**  The repository proves the
   Ricci--DeTurck strict principal symbol and now has abstract time-dependent
   tame fixed-point and reverse-Duhamel infrastructure.  It also has the
   identity-map/diffeomorphism tension algebra under construction.  What is
   still absent is a short-window harmonic-map heat-flow solution for an
   arbitrary endpoint flow, together with a boundary maximal-regularity
   theorem whose constants consume only `C0` metric comparability at `a` and
   interior smoothness.  Existing DeTurck short-time results construct flows
   from prescribed smooth initial data; they do not gauge an independently
   supplied regularizing Ricci flow all the way to its initial edge.

Classification: substantial missing parabolic/gauge producer, not a false
endpoint statement and not a coercion or local coordinate-algebra issue.  The
smallest next analytic lemma is a component-local harmonic-map heat-flow
boundary estimate: on one common short window, a solution starting from the
identity must satisfy a uniform first spatial derivative bound and a
`sqrt(t-a)`-weighted second derivative bound using only the metric-equivalence
constant from `ricciEdgeMetric`.  Its gauge identity can then transfer those
bounds to the fixed-background connection-difference quantities consumed by
the GSM uniqueness energy argument.

Accounting remains strict: `ricciEdgeChartPDE`, `ricciEdgeIntegral`, and
`ricciEdgeImproper` are source-complete but unverified; `ricciEdgeDeriv` is not
stated/proved (0%); its dedicated edge machinery is about 25%.  The exact
`ricci_flow_forward_unique` theorem remains 0%, so `extends_of_rmBounded` and
the Hamilton positive-Ricci endpoint still retain the Phase B analytic
dependency.

## 2026-07-19 comparison with regularizing-flow uniqueness

There is a mathematically faithful third route which confirms that the public
endpoint is true in its stated `C0`-at-the-edge class.  Burkhardt-Guim,
arXiv:1907.13116, Theorem 5.4 proves uniqueness of regularizing Ricci flows from
a `C0` metric, up to one stationary diffeomorphism `alpha`, together with the
compatibility `chi1 o alpha = chi2`.  Each flow in
`ricci_flow_forward_unique` is a regularizing flow with the constant gauge
family `chi_t = id` and limiting map `chi = id`; hence that compatibility
forces `alpha = id`.

The proof is not a reusable citation-sized adapter to the current code.  Its
analytic core restarts at times `t_i -> 0`, puts both smooth time slices into a
common Ricci--DeTurck gauge, and uses a uniform estimate of the form

```text
sup_t ||RD_1(t) - RD_2(t)||_C0 <= C ||RD_1(t_i) - RD_2(t_i)||_C0,
```

where both the common lifetime and `C` depend only on a small `C0`
neighborhood of a fixed smooth background, not on high derivatives of the
time slices.  It then passes almost-isometries to a limiting isometry, makes
that isometry stationary by positive-time smooth Ricci-flow uniqueness, and
identifies the limiting edge maps.

The repository has the positive-time Ricci--DeTurck uniqueness/continuation
and much of the pullback algebra, but it does not have the two rough inputs
used in that proof:

1. a compact-manifold Ricci--DeTurck solver with a common horizon for all
   sufficiently small `C0` perturbations of a smooth background; and
2. the displayed `C0` stability estimate for two such solutions.

The current uniform short-time theorem under construction is not a substitute:
its family hypotheses control fixed-background derivatives through order
three, whereas the slices `g(t_i)` supplied by the endpoint have no uniform
derivative bounds as `t_i -> 0`.  The Euclidean Gaussian `L^p` kernel and first
two derivative estimates in `Analysis/Parabolic/Euclidean/HeatKernelLp.lean`
are an initial parametrix brick, but there is not yet a Koch--Lamm/Simon solution
space, compact-manifold localization, nonlinear fixed point, or `C0` stability
theorem.  The limiting-isometry step would also need a distance/isometry
compactness and smoothness bridge not currently exposed as a public API.

Cost comparison: the regularizing-flow route avoids the general-map harmonic
Bochner and `C1` diffeomorphism-persistence layers, and is therefore the shorter
faithful Phase-B design once rough `C0` Ricci--DeTurck stability exists.  With
the present repository, however, it is still a substantial new parabolic
foundation rather than a consequence of Phase N.  This is a third genuinely
different obstruction, not evidence that the endpoint statement is false.
