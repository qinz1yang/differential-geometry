# Canonical-neighborhood source estimates

This phase starts from handoff commit `4d7a0cbc071b3b10f5540a339772a9401a0814b3`, whose parent is
the previous proof commit `3b12c1abf575960b58f7adca8f73c54c7ea5049b`. Work remains on
`codex/pc-work-2026-09-17`.

## Proven source estimates

Commit `12a12b7800bec88f9beff085043e7f510a175f47` proves the following results.

- `DifferentialGeometry.PDE.RicciFlow.shi_curvDerivNorm_terminal_of_terminal_ball`, in
  `DifferentialGeometry/Geometry/Flow/RicciFlow/Estimates/Shi/Derivatives/TerminalBall.lean`:
  a curvature bound on a compact fixed terminal ball over a closed backward time interval gives
  every fixed curvature derivative bound at its center at the actual terminal endpoint. The proof
  derives metric comparison from an absolute Ricci estimate, proves containment of a buffered
  earlier-time ball, and applies the existing endpoint Shi theorem on that ball. No source Ricci
  sign or positive-time extension is assumed. Dimensions zero and one are covered by the zero
  curvature derivative theorems.
- `exists_curvDerivNorm_le_on_scalar_sublevel`, in
  `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/NormalizedTerminalDerivatives.lean`:
  for sufficiently small epsilon, normalized sources have a uniform terminal curvature derivative
  bound of each fixed order on every scalar sublevel set. The epsilon threshold depends on kappa;
  the resulting bound may depend on the sequence, scalar threshold, and derivative order.
- `exists_curvDerivNorm_bound_on_terminal_ball`, in the same file: a positive radius depending on
  kappa works for all sufficiently small epsilon and all normalized sequences. On this terminal
  base ball, every fixed derivative order has a bound uniform over all source indices.
- `exists_terminalDerivativeBounds_of_boundedAtDistance`, in the same file, derives the complete
  derivative conclusion from scalar boundedness at distance using the proved sublevel estimate.

The last three declarations are in
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn`.

The source estimates use the actual proved `canonical_neighborhood_local_propagation` theorem.
On the tail, pinching gives a scalar lower bound of minus one. The final sublevel proof applies
the stronger scalar-scale estimate below with `Q = max A 1`. Each exceptional source is
controlled separately using its own global curvature bound and positive backward depth; a
finite maximum handles all exceptional indices. No bound shared by all derivative orders is
asserted.

The metric-independent covariant-step bridge and the dimension-at-most-one derivative results
were moved from compactness files to their curvature topic homes:
`Geometry/Curvature/CurvatureOperator/Derivatives/Covariant.lean` and
`Geometry/Curvature/DimensionOne/Derivatives.lean`. Their existing public names remain available.
All four new modules are registered in the flat root.

## Proven spatial point picking

Commit `1d52378c9` adds `NormalizedSequence.exists_terminal_scalar_point_selection` in
`Perelman/CanonicalNeighborhood/NormalizedPointSelection.lean`. From failure of
`BoundedAtDistance X`, it constructs a strictly increasing subsequence, centers with scalar
curvatures tending to infinity, and positive radii such that curvature times radius squared
tends to infinity. Scalar curvature on each selected closed ball is at most twice the center
value, and the entire selected ball lies in one fixed buffered terminal base ball. Both the
centers and the balls are in the actual source manifolds.

The proof first uses each source's own global curvature bound to ensure that curvature escape
can be selected beyond every finite prefix. It maximizes scalar curvature times the square of
the remaining distance to the buffered boundary, then selects one quarter of this remaining
distance as radius. The resulting factor is at most `16/9`, hence at most two. This is the
weighted argument of MSM163 chapter 18, `notes_and_commentary:lbl199`, with a different fixed
radius fraction. It requires no curvature-sign assumption or model information.

The shared weighted maximum proof is now `Metric.exists_weighted_point_selection` in
`Geometry/Metric/PointPicking.lean`, with a Riemannian version in
`Geometry/Metric/RiemannianPointPicking.lean`. The metric result needs only a pseudometric space,
compactness of the particular closed ball, and continuity on that ball. The Riemannian version
has no artificial positive-dimension or global-completeness assumption. The existing ASCR
point-selection proof reuses this common result. Its two public statements are unchanged.

The three new point-selection declarations and the two ASCR consumers passed all thirteen
applicable declaration linters and the standard-axiom-only audit. Fresh leaf builds passed.

## Proven scalar-scale parabolic estimates

Commit `df6ffa0c68ca428cf442ae5503e810a25b6cec3c` proves two results in
`Perelman/CanonicalNeighborhood/NormalizedCurvatureWindows.lean`:

- `exists_parabolic_curvature_bound_at_terminal_scalar_scale` produces positive constants
  `epsStar`, `c`, and `C` depending on kappa. For each admissible normalized sequence with
  epsilon at most this threshold, eventually in the source index, simultaneously for every
  `Q >= 1` and every terminal point with `R(0,p) <= Q`, the actual fixed terminal ball of radius
  `c / sqrt Q` has `|Rm| <= C Q` throughout `[-c/Q, 0]`. The theorem also provides inclusion
  of that closed time interval in the actual source carrier.
- `exists_curvDerivNorm_bound_at_terminal_scalar_scale` produces an epsilon threshold and a
  nonnegative coefficient function `B : Nat -> Real`. Eventually in the source index, for every
  `Q >= 1`, terminal point with `R(0,p) <= Q`, and order `m`, it gives
  `|nabla^m Rm|(0,p) <= B(m) Q (sqrt Q)^m`. The tail is shared across orders; the bound itself
  depends on the order. The proof checks the source regular interval and applies the genuine
  terminal-ball Shi theorem, with the time and radius factors simplified explicitly.

The pinching step is uniform even when `Q` grows with the source index. With
`L = 1 + |R(0,p)| <= 3 Q`, use `exists_forall_rescalePinchingFunction_le` at combined scale
`X.scale i * Q` and argument `4 L / Q <= 12`. This bounds the relative error by `Q` using one
source tail, without an exact nonnegative curvature or Ricci assumption.

The same commit proves `exists_parabolic_point_selection_of_not_boundedAtDistance` in
`Perelman/CanonicalNeighborhood/NormalizedParabolicPointSelection.lean`. Failure of scalar
boundedness produces the actual contained balls above with `Q_i r_i^2 -> infinity`, together
with a fixed positive rescaled backward duration `tau` and a fixed curvature constant `C`.
On each selected terminal ball, `|Rm| <= C Q_i` throughout `[-tau/Q_i, 0]`, eventually in `i`.
This controls balls of diverging radius after curvature rescaling for a fixed backward slab.
It does not construct an ancient solution or rule out the original curvature escape.

All three declarations are in the `FiniteHorn` namespace stated above. The two new modules
are registered in the flat root. The existing sublevel derivative proof now uses the scalar-scale
derivative theorem; its public statements are unchanged.

## Curvature escape limits

The continuation through proof commit `a97df9972a9b6edec91aec778a753e4d12359b70` constructs
actual metric and backward-flow limits from failure of `BoundedAtDistance`. These are genuine
producers from the normalized source hypotheses, not assumptions of a limit or a cone.

- `e04d3b15691c9a3e80182fb921986184675bbe42` proves the constant metric-scaling laws for
  `curvCovDeriv`, `curvDerivNormSq`, and `curvDerivNorm` in
  `Geometry/Curvature/CurvatureOperator/Derivatives/Scaling.lean`. For scaling factor `c > 0`,
  the derivative norm of order `m` scales by `1 / (c * sqrt(c)^m)`. The statements use finite
  dimensional normed model spaces; no inner product, boundaryless, or positive-dimension
  hypothesis is imposed.
- `21cb0927f3ff935d28af981647d41b5f100c4f7f` constructs a complete terminal metric limit in
  `Perelman/CanonicalNeighborhood/NormalizedMetricLimit.lean`. Its actual source metrics are
  the selected terminal metrics scaled by their center scalar curvatures. Every fixed ball
  eventually lies in the selected source ball. The scalar-scale derivative bounds and actual
  local injectivity theorem give smooth pointed compactness. The limit has base scalar one,
  global scalar at most two, nonnegative sectional curvature, and kappa noncollapse at all scales.
- `5bb0fa727e0e7d1dd7d0a7376ae3e9994116e665` proves that this metric limit is noncompact.
  A uniform bound on a fixed original terminal base ball forces high-curvature centers outside
  that ball. Thus the original basepoints escape to infinity in the rescaled source metrics.
  A compact pointed limit would eventually globalize its convergence maps onto the connected
  sources, contradicting escape. The reusable result is
  `PointedRiemannianConvergenceMaps.noncompact_of_escaping_points` in
  `Geometry/Compactness/CheegerGromov/Pointed/Convergence/Compact.lean`.
- `a97df9972a9b6edec91aec778a753e4d12359b70` constructs a normalized rescaled flow sequence,
  an oriented terminal limit of that sequence, and an actual closed backward extension.
  `NormalizedSequence.terminalCurvatureRescale` in `NormalizedRescaling.lean` preserves
  the finite source intervals, source-dependent curvature bounds, completeness, noncollapse,
  pinching, and oriented higher-curvature model witnesses. Both depth and pinching scale are
  multiplied by the center scalar curvature. A tail ensures every selected center scalar is
  at least one, as needed for the higher-curvature threshold.

The final two producers are
`exists_noncompact_terminalLimit_of_not_boundedAtDistance` in `NormalizedTerminalLimit.lean`
and `exists_noncompact_backwardExtension_of_not_boundedAtDistance` in
`NormalizedBackwardLimit.lean`, both in the `FiniteHorn` namespace. Their conclusions retain
actual selected source points, radii, containment in one fixed source base ball, center curvature
`Q_i` and products `Q_i r_i^2` tending to infinity, and the exact normalized rescaled sequence to
which the limit belongs. The terminal limit is noncompact and has scalar curvature at most two. The
backward extension includes smooth convergence of the selected source flows, completeness,
nonnegative sectional curvature, and compact-time global curvature bounds on a genuine closed
interval `[-delta, 0]`, with `delta > 0`.

`TerminalLimit.ofMetricCompactLimit` exposes the existing terminal-limit construction as an actual
object, preserving its space and maps definitionally. The previous existential theorem remains
with its original statement. The six existing normalized reindexing declarations moved verbatim
from `EscapeReindexingReduction.lean` to `NormalizedReindexing.lean`; this makes them available
below the unresolved bounded-distance theorem. Four generic compact-limit globalization
results moved from `KappaSolutions/CompactLimitGlobalization.lean` to the pointed-convergence
`Compact.lean` module, preserving their names and statements. All new leaves are registered in
the flat root.

The backward-extension producer uses the already-proved
`exists_backward_extension_of_model_curvature_bound` and the proved ancient-kappa model bound.
It does not invoke `bounded_curvature_at_distance`, `terminal_limit_global_bound`, or
`ancient_extension` in its proof closure. Its current import graph nevertheless reaches
`FiniteHornStructure.lean` through the existing backward-slab infrastructure. A future consumer
inside that file will need to separate the existing lower curvature-control declarations from
its headline to avoid a module import cycle; the lower metric and terminal-limit producers do
not import that file.

## Mathematical references

The read-only library is `/Users/bennettchow/Documents/Codex/RicciFlowBooksLatex`.

- MSM135, `tex/chapters/chapter3.tex`, `notes_and_commentary:lbl334`: compactness of complete
  pointed metrics under curvature derivative and injectivity bounds. The formal construction uses
  the existing local-ball version, after deriving its actual source estimates. Label `lbl335`
  assumes an open time interval containing zero; it is not used to infer a positive-time source
  extension. Label `lbl338`, with equations `lbl339` and `lbl340`, records the initial metric
  comparison and derivative hypotheses for controlling evolving metrics.
- MSM144, `tex/chapters/chapter14.tex`, `notes_and_commentary:lbl550`: local higher derivative
  estimates on a compact initial ball, including positive times up to the terminal time. The new
  terminal-ball theorem supplies the earlier ball and its curvature bound before using the
  formal endpoint version.
- MSM163, `tex/chapters/chapter18.tex`, `notes_and_commentary:lbl199`: weighted spatial point
  picking from curvature escape on a bounded ball; only compactness of the buffered closed ball
  is needed.
- MSM163, `tex/chapters/chapter20.tex`, `notes_and_commentary:lbl477`: the bounded-distance lemma
  there assumes nonnegative curvature operator and the Harnack time-monotonicity property. These
  are not hypotheses of a normalized source and must not be inferred from almost-pinching.
- MSM163, `tex/chapters/chapter22.tex`, `notes_and_commentary:lbl621`, `lbl623`, `lbl624`: the
  finite-interval setting and point-picking arguments use individual source curvature bounds;
  those bounds do not become uniform over a sequence.

## Remaining target

`bounded_curvature_at_distance` in `FiniteHornStructure.lean` is still unproved, with its original
source text unchanged. Its remaining mathematical obstacle is scalar control at arbitrary bounded
terminal distance. The derivative producer above is ready once that scalar estimate is obtained.
The point-picking, metric-limit, and backward-slab producers now supply actual geometric
limits for the escape case. They do not supply the geometric exclusion of that case. A local ball
estimate cannot by itself exclude finite-distance curvature escape.

The high-curvature blowup theorem and the full Poincare development are not complete. The previous
handoff's cautions concerning cone exclusion versus cone construction, terminal limit construction,
and compatible ancient extension still apply. In particular, one backward slab is not an ancient
solution, and the existing theorem named `finite_horn_produces_cone` excludes a cone.

## Verification of the derivative checkpoint

The initial handoff's `verify.sh` passed before source changes. Fresh leaf builds for the new
source estimates passed, including their rebuilt compactness dependents. Seven public declarations
(three moved, four new) passed all thirteen applicable declaration linters; each has only
`propext`, `Classical.choice`, and `Quot.sound` in its transitive axiom closure. The previous phase's
nine-declaration audit also passed again after the derivative checkpoint.

The derivative checkpoint's full root build passed 20,147 jobs with exactly 21 retained `sorry`
warnings. Its dependency audit found the same three reachable proof holes as the original
handoff: `bounded_curvature_at_distance`, `terminal_limit_global_bound`, and `ancient_extension`.

After the scalar-scale checkpoint, the combined audit checked fifteen public declarations with
thirteen applicable linters. All passed, and every transitive axiom closure was a subset of
`{propext, Classical.choice, Quot.sound}`. This covers ten new declarations, three moved
declarations, and the two existing ASCR consumers. The elaborated statement queries are included
in the same temporary driver and log, `/private/tmp/wt17-source-estimates-audit.lean` and `.log`.

The final full build at `df6ffa0c68ca428cf442ae5503e810a25b6cec3c` passed **20,152 jobs** with
exactly **21 retained `sorry` warnings and no other diagnostics**. Its log is
`/private/tmp/wt17-source-estimates-root.log`. No Lean source was edited during any build.
The target's complete source file compares identically to the original handoff commit.

The original handoff's `verify.sh` also passed again after the final source changes: seven fresh
source elaborations, nine declarations checked by thirteen linters, standard axiom closures,
original statement compatibility, and exactly twenty-one retained holes in eleven files. Its
dependency traversal again found only the same three reachable blowup holes. Evidence is in
`/private/tmp/wt17-kappa-verification.R7CQO3`; the command log is
`/private/tmp/wt17-source-estimates-compatibility.log`.

Reproduce the source builds with:

```sh
lake build DifferentialGeometry.Geometry.Metric.PointPicking \
  DifferentialGeometry.Geometry.Metric.RiemannianPointPicking \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedPointSelection \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedParabolicPointSelection \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedTerminalDerivatives
lake build DifferentialGeometry
bash docs/handoffs/kappa-solutions-2026-09-20/verify.sh
git diff --check
```

For fresh source elaboration and declaration probes, use the repository's exact options:

```sh
lake env lean -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -DautoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dlinter.style.header=false \
  -Dlinter.style.longLine=false /path/to/probe.lean
```

The combined probe imports `NormalizedTerminalDerivatives`, `NormalizedParabolicPointSelection`,
and `KappaSolutions.AscrPointSelection`. Use the earlier handoff's `getChecks`/`lintCore` driver
on all ten new public declarations listed above, the three moved declarations
`curvStep_eq_covStep`, `curvCovDeriv_eq_zero_of_finrank_le_one`, and
`curvDerivNorm_eq_zero_of_finrank_le_one` in `DifferentialGeometry.CheegerGromovCompactness`, and
`exists_ascrPointSelection` and `exists_scalarAscrPointSelection` in the kappa-solution namespace.
Query both `#check @...` and `#print axioms ...` for each declaration.

## Verification of the limit checkpoint

The source snapshot `a97df9972a9b6edec91aec778a753e4d12359b70` passed the full root build:
**20,158 jobs**, exactly **21 retained `sorry` warnings**, and no other diagnostics. Twelve
changed source modules were also freshly elaborated with the exact repository options and
zero diagnostics. No Lean source was edited during these builds.

The combined declaration audit checked **22 declarations with all 13 applicable linters**.
All passed. Each exact elaborated statement was queried, and every transitive axiom closure
is contained in `{propext, Classical.choice, Quot.sound}`. The inventory is:

- In `DifferentialGeometry.CheegerGromovCompactness`: `curvCovDeriv_scaleMetric`,
  `curvDerivNormSq_scaleMetric`, `curvDerivNorm_scaleMetric`, and
  `PointedRiemannianConvergenceMaps.noncompact_of_escaping_points`.
- In `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions`:
  `partialDiffeomorph_target_eq_univ_of_compact_source`, `globalDiffeomorphOfUniv`,
  `compactLimit_eventually_source_eq_univ`, and `compactLimit_eventually_globalizes`.
- In the `FiniteHorn.NormalizedSequence` namespace: `terminalCurvatureRescaledSequence`,
  `terminalCurvatureRescale`, `reindex`, `reindex_term`, `reindex_interval`, `reindex_depth`,
  `reindex_scale`, and `reindex_id`.
- In `FiniteHorn`: `exists_terminalCurvatureRescaledSequence_metric_limit_of_not_boundedAtDistance`,
  `exists_terminalCurvatureRescaledSequence_noncompact_metric_limit_of_not_boundedAtDistance`,
  `TerminalLimit.ofMetricCompactLimit`, `terminal_limit_of_metric_compact_limit`,
  `exists_noncompact_terminalLimit_of_not_boundedAtDistance`, and
  `exists_noncompact_backwardExtension_of_not_boundedAtDistance`.

The audit imports `NormalizedBackwardLimit`; use the earlier handoff's `getChecks`/`lintCore`
pattern on this inventory and query `#check @...` and `#print axioms ...` for every entry.
Local evidence is `/private/tmp/wt17-normalized-limits-audit.lean` and `.log`; the twelve empty
fresh-elaboration logs are in `/private/tmp/wt17-normalized-limits-fresh/`.

The original handoff's `verify.sh` passed again, including its seven fresh source elaborations,
nine-declaration linter/axiom audit, and original-statement compatibility probes. It confirms
**21 actual `sorry`s in 11 files** and exactly the same three reachable holes in
`arbitrary_high_curvature_blowup`: `bounded_curvature_at_distance`,
`terminal_limit_global_bound`, and `ancient_extension`. Evidence is in
`/private/tmp/wt17-kappa-verification.BxXsAv`; the command log is
`/private/tmp/wt17-normalized-limits-verification.log`. The complete `FiniteHornStructure.lean`
source still compares identically to the original handoff commit. `git diff --check` passed.

Reproduce the limit builds with:

```sh
lake build DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedBackwardLimit \
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EscapeReindexingReduction
lake build DifferentialGeometry
bash docs/handoffs/kappa-solutions-2026-09-20/verify.sh
```

The new proof layers pass their mathematical, API, compiler, linter, and axiom checks. The
requested `bounded_curvature_at_distance` theorem is **Not accepted** as a completed proof:
its original `sorry` remains, and the geometric exclusion of finite-distance curvature escape
has not been constructed.

Local evidence is in `/private/tmp/wt17-normalized-derivatives-audit.lean`, its `.log`, and
`/private/tmp/wt17-continuation-kappa-audit.log`. These temporary files are not portable handoff
artifacts. The earlier handoff contains the reproducible audit-driver pattern and original
statement compatibility probes. Its fixed job/debt counts describe its own snapshot.


## Finite-radius source comparisons

The local reference directory `/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers`
contains `MorganTianPoincare.pdf`, `MorganTianGeom.pdf`, `KleinerLottPerelman.pdf`, and
`BBBMP-10112010.pdf`, as well as Perelman's original papers. The user requested that these
references be remembered for future work; the directory is now recorded in the global
`/Users/bennettchow/.codex/AGENTS.md`. All reference sources remain unchanged.

The main guides for the missing geometric construction are Kleiner--Lott, section 52,
Step 2 (equation 52.13 and Lemma 52.14; printed pages 2702--2704), and Morgan--Tian,
*Ricci Flow and the Poincaré Conjecture*, Chapter 10 (Theorem 10.2, Proposition 10.7,
and Proposition 10.12; printed pages 245--264). The former matches the almost-pinched
normalized-sequence formulation; the latter expands the incomplete-tube and cone construction.
Neither permits replacing these source flows by ancient kappa-solutions.

`CurvatureEscape.lean` now contains the existing radius-selection definitions and proofs,
moved without changes to their statements or proof bodies out of files depending on
`FiniteHornStructure.lean`. This makes them available below the unfinished headline.

`NormalizedLocalCompactness.lean` proves
`exists_terminal_pairwise_metric_approximation_of_not_boundedAtDistance`. For sufficiently
small epsilon, failure of boundedness produces a strict source subsequence with an actual
`FiniteControlledRadius` and smooth pairwise metric-comparison maps on every smaller closed
terminal ball. The selected escape points and the comparison maps refer to the same source
subsequence. Injectivity bounds are derived from source noncollapse and actual containment
in a buffered ball; derivative bounds use the already proved terminal scalar-sublevel estimates.
The generic diagonal argument now handles arbitrary countable radius families, and a new
finite-radius compactness theorem is in the Cheeger--Gromov topic home.

This gives comparison maps, not yet the incomplete limit manifold or the finite horn.
The headline `bounded_curvature_at_distance` still has its original statement and proof hole.
The next geometric step is to realize the comparisons as a smooth incomplete limit, retaining
capture of each inner ball and the escaping geodesic endpoint, then construct the horn and cone.

The finite-radius layer passed fresh elaboration of all eight changed Lean leaves and the
full `lake build DifferentialGeometry` (20,160 jobs). Its 21 audited declarations passed
13 applicable declaration linters and have only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom closures. The 21 moved declaration blocks were
checked verbatim against their preceding locations. The existing headline statement and
proof body are unchanged. Verification logs are in `/private/tmp/wt17-finite-radius-fresh/`,
`/private/tmp/wt17-finite-radius-audit.log`, and
`/private/tmp/wt17-finite-radius-root-build.log`.

## Source geodesic tails

`NormalizedEscapeGeodesic.lean` proves `exists_high_curvature_geodesic_tail`, following
Kleiner--Lott section 52, Step 2, immediately after equation (52.13). Uniformly for
sufficiently small epsilon and eventually in every normalized sequence, each terminal
point with scalar curvature greater than 12 is joined to the normalized basepoint by an
actual smooth unit-speed minimizing geodesic. The construction selects the last point
with scalar curvature 2, proves scalar curvature is greater than 2 on the remaining
segment, and gives that segment a uniform positive lower length bound.

Its reusable ingredients are `ContinuousOn.exists_eq_and_forall_gt` in
`Topology/Order/IntermediateValue.lean` and
`exists_unitSpeed_minimizing_geodesic_of_complete` in `Geometry/Geodesic/Ray.lean`.
All three declarations passed 13 applicable declaration linters, exact-signature review,
and standard-only transitive axiom checks. All three leaves elaborated freshly without
diagnostics; the full project build passed 20,162 jobs. Evidence is in
`/private/tmp/wt17-geodesic-tail-audit.log` and
`/private/tmp/wt17-geodesic-tail-root-build.log`. The headline still requires the
smooth incomplete limit and the subsequent horn/cone construction.

## Directed comparisons below the escape radius

`exists_directed_approximate_isometry_subsequence_within_radius` now constructs
successor comparison maps whose arbitrary finite compositions remain controlled on
closed balls with radii tending to a prescribed positive finite radius. The zero-order
error tends to zero fast enough that each such ball maps strictly inside the next
ball. Covariant derivative errors are controlled separately at each fixed order;
no common all-order bound is asserted. The original unbounded-radius directed
subsequence theorem retains its statement and is a corollary of the shared proof.

The two changed leaves elaborated freshly without diagnostics. Three public
declarations passed all 13 applicable declaration linters and standard-only
transitive axiom checks. The full project build passed 20,162 jobs with the 21
retained proof-hole warnings. Evidence is in
`/private/tmp/wt17-directed-finite-audit.log`,
`/private/tmp/wt17-directed-finite-fresh-error.log`,
`/private/tmp/wt17-directed-finite-fresh-existence.log`, and
`/private/tmp/wt17-directed-finite-root-build.log`.

These maps supply the geometric input for compatible metric limits on the inner
balls. The incomplete limit, geodesic endpoint, and horn/cone producer remain the
active work; the headline's existing proof hole is unchanged.

## Local pointed limits below the escape radius

The continuation after `a8c20eeaebc21b1875867ac0c58c317ef08f8a92` proves
`exists_pointed_convergence_within_radius` in
`Geometry/Compactness/CheegerGromov/Pointed/Compactness/Local.lean`. Pairwise smooth metric
approximations on every ball of radius below a positive finite radius now produce an actual
smooth pointed limit. Its convergence maps have targets equal to specified source balls with
radii tending to the limiting radius. The returned convergence data is explicitly canonical,
and relative metric bounds hold on each entire comparison domain, with errors tending to zero.

The compatible-chain metric-limit proofs now accept arbitrary positive ball radii and actual
chain-image containment. Their existing power-of-two statements are preserved as corollaries.
The zero-order approximation conversions separate the metric distortion tolerance from the
higher derivative tolerance. `ProperMetricOn.alignedMetricSpace` moved unchanged to the proper
metric module.

`PointedRiemannianConvergenceMaps.isCompact_closed_ball_of_target_coverage`, in the new
`Pointed/Convergence/LocalProperness.lean` leaf, transports compactness from source balls to
strictly smaller limit balls. Its general kernel is
`PartialDiffeomorph.isCompact_riemannianClosedBallOf_of_metric_upper` in
`Geometry/Metric/Comparison/IntrinsicBallImage.lean`. The proof applies the existing intrinsic
ball-image theorem to the inverse map, using an explicit radius margin and the whole-domain
metric bound. It does not assume completeness of the limit.

The application is `exists_terminal_pointed_convergence_of_not_boundedAtDistance` in
`Perelman/CanonicalNeighborhood/NormalizedLocalCompactness.lean`. For sufficiently small
epsilon, failure of boundedness now produces a finite controlled radius, escaping source points,
and a smooth pointed limit of the actual terminal source metrics along the same subsequence.
Every inner closed base ball is compact. The limit has base scalar curvature one and nonnegative
sectional curvature, obtained by passing the source pinching to the limit. The source metrics
are not assumed to have nonnegative curvature.

This realizes the smooth-manifold and inner-ball compactness portion of Kleiner--Lott Section 52,
Step 2, following equation (52.13), printed pages 2702--2703 of
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
Morgan--Tian, `MorganTianPoincare.pdf`, Chapter 10, Proposition 10.7, is the companion reference
for the later incomplete tube. The limiting geodesic with its missing endpoint and the neck/cone
producers remain to be proved. The bounded-distance headline is unchanged and remains open.

After the final Lean edit, the full root build passed 20,164 jobs with the same 21 retained
`sorry` warnings. Twenty declarations passed all thirteen applicable declaration linters; all
have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closures.
The old generalized signatures also compile as corollaries. Both new leaves are registered in
the flat root. Temporary evidence is in `/private/tmp/wt17-local-limit-final-root-build.log`,
`/private/tmp/wt17-local-limit-final-audit.log`, and
`/private/tmp/wt17-compatible-balls-compatibility.log`.

## Curve subsequences in the finite-radius limit

The continuation after `8a745b1ca14c3653bfb1ba067800597d789e9dc3` proves
`PointedRiemannianConvergenceMaps.exists_curve_subseq_limit` in the new
`Geometry/Compactness/CheegerGromov/Pointed/Convergence/Curves.lean` leaf. It constructs a
subsequence of the actual pulled-back source curves and a continuous 1-Lipschitz limit on
`[0, rho)`, with the prescribed basepoint and uniform convergence on every compact parameter
set. The inputs are source curves that are C1 on their closed segments, a unit-speed upper
bound, lengths tending to `rho`, target-ball coverage, relative lower metric bounds tending
to one, and compactness of the inner limit balls.

The proof truncates each source curve strictly inside its actual target ball. The truncation
lengths tend to `rho`. Inverse-map derivative identities transfer the source speed bound to
the limit metric. For each parameter below `rho`, these estimates place the pulled-back
points in a compact inner ball. Arzela--Ascoli then produces the curve; passing all constants
greater than one to the limit gives the exact 1-Lipschitz bound. Completeness of the limit and
extensions of the source curves beyond their supplied smooth intervals are not assumed.

`Analysis/Calculus/Compactness/ArzelaAscoli.lean` now has the uniform-space compact-closure
version, a metrizable-target subsequence version allowing pointwise eventual compactness,
and `ArzelaAscoli.exists_lipschitz_subseq_limit_on_Ico` for exhausting source intervals.
The existing scalar and vector specializations retain their signatures as corollaries.
`Manifold.riemannianEDist_le_of_curve_speed_bound`, in `Geometry/Metric/Path/Speed.lean`,
requires smoothness on the closed interval and a speed bound only in its interior. The
existing Hopf--Rinow and flat-model metric speed estimates retain their signatures and use
this general result.

This supplies the compactness step for curves following Kleiner--Lott Section 52, Step 2,
after equation (52.13), printed pages 2702--2703 of
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
Distance preservation, the missing endpoint, and the neck/cone producers remain active proof
work. The curve theorem does not yet assert that the limit is minimizing. The bounded-distance
headline is unchanged, and the source inventory still contains 21 proof holes.

The changed leaves compiled without diagnostics. Nine new or changed declarations passed
all thirteen applicable declaration linters, with only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom closures. Both new leaves are registered in the flat
root. Temporary evidence is in `/private/tmp/wt17-speed-leaves-build.log`,
`/private/tmp/wt17-arzela-curves-build.log`, `/private/tmp/wt17-pointed-curves-build.log`, and
`/private/tmp/wt17-curve-compactness-audit.log`.

After the final Lean edit, the full root build passed 20,166 jobs with the same 21 retained
`sorry` warnings and no other diagnostics. The root evidence is
`/private/tmp/wt17-curve-compactness-root-build.log`.


## Distance preservation and source endpoints

The continuation after `e293f9c47` proves
`PointedRiemannianConvergenceMaps.limsup_edist_le` in the new
`Geometry/Compactness/CheegerGromov/Pointed/Convergence/Distance.lean` leaf. Upper metric
bounds tending to one on each compact set imply upper semicontinuity of source distances
between images of converging limit points. The proof maps nearly shortest paths in compact
sets and controls the errors at moving endpoints in compact neighborhoods. The limit need
not be complete or connected.

`PointedRiemannianConvergenceMaps.exists_isometric_curve_subseq_limit` strengthens the
previous curve producer when the source curves are minimizing with their unit-speed
parametrizations. Its output retains uniform convergence of the actual inverse images on
compact parameter sets and gives `Isometry` for the limiting half-open segment. The proof
establishes eventual actual target membership before using either inverse identity.

`PointedRiemannianConvergenceMaps.tendsto_edist_curve_endpoint_zero` proves the endpoint
comparison needed for the missing-endpoint contradiction. If a pulled-back curve has an
endpoint in the smooth limit, then its source endpoints approach the images of that point
in source intrinsic distance. The source endpoints need not belong to the maps' targets.
Only C1 regularity on the supplied closed intervals, a fixed finite speed bound in their
interiors, convergence at interior parameters, and local upper metric bounds are used.

The general metric-valued interval speed estimate now lives in
`Geometry/Metric/CurveSpeed.lean`, with the existing global flat-model theorem as a
corollary. The curve producers reuse it. Its raw norm-valued foundation remains
`Manifold.riemannianEDist_le_of_curve_speed_bound` in `Geometry/Metric/Path/Speed.lean`.

This develops the minimizing-segment and endpoint argument following Kleiner--Lott,
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`,
Section 52, Step 2, after (52.13), printed pages 2702--2703. The application to the actual
normalized escaping sequence, its missing endpoint, and the neck/cone producers remain
active proof work. The bounded-distance headline is unchanged; there are still 21 source
proof holes.

The changed leaves compiled without diagnostics. Six new or changed declarations passed
all thirteen declaration linters and have only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom closures. Temporary evidence is in
`/private/tmp/wt17-pointed-distance-build.log`,
`/private/tmp/wt17-metric-curve-speed-build.log`,
`/private/tmp/wt17-curves-endpoint-build.log`, and
`/private/tmp/wt17-curve-distances-audit.log`.

After the final Lean edit, the full root build passed 20,167 jobs with the same 21 retained
`sorry` warnings and no other diagnostics. The root evidence is
`/private/tmp/wt17-curve-distances-root-build.log`.


## The actual escaping segment and its missing endpoint

The continuation after `85be0c06e6305b8dda7c1de45d300674ff7c82ca` proves
`exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance` in the new
`CanonicalNeighborhood/NormalizedEscapeLimit.lean` leaf. Starting from a normalized
sequence and failure of `BoundedAtDistance`, it now produces the actual finite-radius
terminal pointed limit together with an isometric curve on `[0, F.radius)`. This curve
starts at the limit basepoint and has no limit in the smooth manifold at `F.radius`.

The conclusion retains the earlier canonical metric convergence, exact source-ball
targets, relative metric bounds, compact inner limit balls, base scalar one, and
nonnegative limit sectional curvature. It also retains a strict further subsequence,
the actual source geodesics ending at `F.points`, and uniform convergence of their actual
inverse images on compact parameter sets. Each retained source geodesic is smooth,
unit speed, and minimizing. Its final high-curvature tail begins at scalar two, stays
above two after that point, and has length greater than a fixed positive constant
chosen from kappa. These tail statements currently concern the source curves; their
limit scalar and neck properties are still to be proved.

The construction engine `exists_isometric_curve_with_missing_endpoint` works from the
produced escaping points, converging source radii, canonical pointed metric convergence,
whole-domain lower metric estimates, and compact inner limit balls. Compact upper metric
estimates are derived from canonical metric convergence rather than requested again.
The proof selects an initial tail of the escaping sequence, obtains the source geodesics
from `exists_high_curvature_geodesic_tail`, and applies the general isometric curve
compactness theorem. A hypothetical smooth endpoint would force the source endpoints
to approach its comparison-map images in source distance.

`not_tendsto_edist_zero_of_scalar_tendsto_atTop` rules that out. Scalar convergence at the
fixed smooth point bounds the scalars of its images. The new
`eventually_scalar_le_of_edist_tendsto_zero` in `ModelCurvaturePropagation.lean` transfers
a bounded scalar estimate between coalescing source points. It follows from the proved
local propagation theorem and works at varying times in the controlled last half of each
source interval. Applying it would bound the escaping scalars, contradicting their
divergence. No nonnegative source Ricci assumption, common future extension, or ancient
source solution is used.

This proves the missing-segment-endpoint step following Kleiner--Lott Section 52, Step 2,
after (52.13), printed pages 2702--2703 of
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
The completion endpoint, limiting high-curvature tail, neck tube, and cone producers
remain active work. `FiniteHorn.bounded_curvature_at_distance` is unchanged and remains
open. The source inventory still has 21 proof holes.

The changed source leaves and their direct dependencies compiled without diagnostics.
Four new public declarations passed all thirteen declaration linters, and each transitive
axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`. The new leaf
is registered in the flat root. Temporary evidence is in
`/private/tmp/wt17-scalar-coalescence-build.log`,
`/private/tmp/wt17-missing-endpoint-build.log`, and
`/private/tmp/wt17-missing-endpoint-audit.log`.

After the final Lean edit, the full root build passed 20,168 jobs with the same 21 retained
`sorry` warnings and no other diagnostics. The root evidence is
`/private/tmp/wt17-missing-endpoint-root-build.log`.


## The completion endpoint of the escaping segment

The continuation after `259beb3ad90a5c25cbf3a280e4b629932e821a45` strengthens
`exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance`:
the produced limit is path connected, and the escaping segment converges to a point
of its canonical intrinsic metric completion outside the smooth manifold. The distance
from that point to the segment at parameter `t` is exactly `F.radius - t`. All earlier
source geodesic, scalar-tail, convergence, and limit curvature data are retained.
The named bounded-distance target is still unchanged and open.

Three general foundations support this construction. Positive-radius intrinsic open
balls are path connected without completeness or finite-dimensionality assumptions.
Pointed convergence maps with path-connected targets at infinitely many indices have
a path-connected limit. Finally, an isometric half-open real interval in any
pseudometric space has a completion endpoint with the exact remaining-length distance
formula. These results live respectively in `Geometry/Metric/Distance/Ball.lean`,
`Geometry/Compactness/CheegerGromov/Pointed/Convergence/Connected.lean`, and
`Geometry/Metric/Segment.lean`. The new connectedness leaf is registered in the flat root.

The normalized application obtains connectedness from its actual source-ball targets.
This makes its intrinsic extended distances finite, so the existing metric-completion
API applies. The already-proved absence of a smooth endpoint shows that the constructed
completion point lies outside the embedded manifold. This realizes the completion
step in Kleiner--Lott Section 52, Step 2, printed page 2703 (PDF page 117), rather than
assuming a missing point or an arbitrary ambient metric.

The three foundation leaves passed their build (4,143 jobs), and the normalized
application and affected dependencies passed their build (13,982 jobs), without
diagnostics. All four added or strengthened declarations passed thirteen declaration
linters and have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive
axiom closures. Evidence is in `/private/tmp/wt17-completion-foundations-build.log`,
`/private/tmp/wt17-normalized-completion-build.log`, and
`/private/tmp/wt17-completion-audit.log`.

## Scalar divergence at the completion endpoint

The continuation after `b60a19263596b0317d3d281a7ecd4f219d94c6a1` strengthens
`exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance`
with scalar curvature tending to positive infinity along the escaping segment at its
completion endpoint. The earlier limit, source geodesic, convergence, and exact
completion-distance data are retained. The construction engine first proves divergence
of absolute scalar curvature. The application uses the proved nonnegative sectional
curvature of the limit to recover the signed conclusion.

The proof uses scalar convergence at actual moving source points and a quantitative
source separation estimate from local propagation. If the limit scalar at a point near
the missing endpoint stayed bounded, its approximating source points would remain a
fixed positive distance from the escaping endpoints. The remaining geodesic lengths
tend to zero there, a contradiction. Actual membership in the convergence maps' targets
is proved before using inverse maps. This develops the scalar-divergence step in
Kleiner--Lott, Section 52, proof of Lemma 52.14, printed page 2703 (PDF page 117), in
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.

The general scalar-convergence API now lives in
`Geometry/Compactness/CheegerGromov/Pointed/Convergence/Scalar.lean`. Uniform convergence
on compact sets follows from canonical relative metric convergence at order two;
moving-point and actual inverse-image forms follow from it. The new primary statements
use a finite-dimensional normed model and derive its completeness locally. Existing
pointwise and compact scalar-control statements are compatibility corollaries.

The static metric-curvature difference and scalar-convergence developments moved to
`Geometry/Curvature/MetricDifference.lean` and `Geometry/Metric/Convergence/Scalar.lean`,
with their established declaration names, scopes, and proofs preserved. Static curvature
restriction identities moved from the flow restriction file into the existing
`Geometry/Curvature/RicciRestriction.lean`. The duplicate Ricci restriction proof was
removed in favor of the existing, more general canonical theorem, re-exported for
compatibility. A positional consumer was updated and an unused completeness assumption
was removed from dependent restriction lemmas.

The bounded-distance headline remains unchanged and open. The source inventory remains
21 proof holes. Neck and cone producers remain active mathematical work.

The normalized application build passed 13,986 jobs without diagnostics. The final
root build passed all 20,170 jobs with exactly the 21 retained `sorry` warnings and
no other diagnostics. Twenty-two added, moved, generalized, or affected declarations
passed all thirteen declaration linters; every inspected transitive axiom closure
contains only a subset of `propext`, `Classical.choice`, and `Quot.sound`. Exact
signatures and evidence are recorded in
`/private/tmp/wt17-normalized-scalar-escape-repair-build.log`,
`/private/tmp/wt17-scalar-endpoint-final-root-build.log`, and
`/private/tmp/wt17-scalar-convergence-final-audit.log`.

## Quantitative curvature separation at the missing endpoint

The continuation after `9b375c5f3` produces uniform curvature bounds on actual
source balls from `WindowedModelWitness`. For each fixed normalized radius, a
positive epsilon threshold works for every source and every model parameter.
The curvature bound holds on the ball defined at any time in the model window,
throughout that full window. Compactness and ball containment come from the
proved buffered comparison and first-exit argument. The source itself is never
treated as an ancient solution.

The new module `CanonicalNeighborhood/WindowedUniformCurvature.lean` keeps this
universal-model input above the existing `WindowedSourceCurvature.lean` transport
interface and is registered in the flat root. Its physical-radius scalar
corollary gives a uniform bound on balls of radius `r / sqrt(Q)` around a model
point of scalar curvature `Q`. Applied to the higher-curvature witnesses in a
normalized sequence, it separates bounded-scalar convergent points from points
whose scalar curvature diverges. The comparison holds throughout the specified
source time interval and requires no source Ricci-sign assumption.

Both escaping-curve construction theorems now accept a prescribed nonnegative
constant `A`. For a sufficiently small epsilon depending on this constant, their
actual output satisfies `A^2 <= R * d^2` wherever `R > 2`, where `d` is the
remaining segment length, or equivalently the distance to the constructed
completion point. The strict scalar threshold is the one required to obtain
higher-curvature source witnesses after convergence. Scalar divergence ensures
that this condition holds near the endpoint. All previous source, convergence,
completion, and curvature data remain in the conclusions. Both preceding
statements compile as corollaries by choosing `A = 0` and forgetting the added
estimate.

This proves the quantitative separation input in Kleiner--Lott, Section 52,
Lemma 52.14(1), printed page 2703 (PDF page 117), in
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
The threshold is allowed to shrink with `A`; the statement does not assert an
arbitrarily large lower bound for one fixed epsilon. The neck construction in
Lemma 52.14(2), the horn/cone producers, and the named bounded-distance headline
remain open. The source debt inventory remains 21.

The final changed-leaf and affected-consumer build passed 13,992 jobs without
diagnostics. The final root build passed 20,171 jobs with exactly the 21 retained
`sorry` warnings and no other diagnostics. All five added or strengthened public
declarations passed thirteen declaration linters and have standard-axiom-only
transitive closures. The two exact preceding construction statements also compiled
as corollaries. Evidence is in
`/private/tmp/wt17-quantitative-escape-interface-build.log`,
`/private/tmp/wt17-quantitative-escape-final-root-build.log`, and
`/private/tmp/wt17-quantitative-escape-audit.log`.


## Intrinsic lines, cylinder classification, and source necks

The continuation after `490e0e62a` proves that an oriented three-dimensional
ancient kappa-solution containing an intrinsic minimizing line at any time at
or before zero is a round shrinking cylinder, with one diffeomorphism realizing
the product metric at all times. Without orientability, the remaining alternatives
are the cylinder and the antipodal sphere product. The reflected cylinder quotient
is excluded by its actual covering metric.

The exclusion has reusable foundations in `Topology/Covering/Line.lean` and
`Geometry/Metric/Cylinder/Line.lean`. A continuous lift of a hypothetical line has
absolute height bounded below; the covering distance estimate and reflection force
that height to preserve distances up to a bounded error, which contradicts the
intermediate value theorem. Compactness of the cross-section supplies the bounded
error in the Riemannian application. These results require no curvature hypothesis.

`KappaSolutions/AncientCylinderLine.lean` combines this exclusion with the proved
null-plane and fixed-cylinder classification. `KappaSolutions/PointedLineNeck.lean`
then constructs eventual source neck witnesses from canonical pointed metric
convergence to an ancient limit containing a line. It derives the limit's scalar
normalization from convergence and excludes the antipodal sphere product using
orientations on the approximating manifolds. The conclusion identifies every neck
embedding with the actual convergence map. This is the compactness and splitting
step underlying Kleiner--Lott, Section 49, Proposition 49.1 (printed page 2692,
PDF page 106 of `BooksPapers/KleinerLottPerelman.pdf`). Quantitative long-segment
neck production and its use near the missing endpoint remain the next work.

All four new leaves are registered in the flat root. The cylinder and pointed-neck
leaf builds passed without diagnostics. Six public declarations passed thirteen
declaration linters, and all six have only `propext`, `Classical.choice`, and
`Quot.sound` in their transitive axiom closures. The final root build passed
20,175 jobs with the same 21 retained sorry warnings and no other diagnostics.
Evidence is in `/private/tmp/wt17-ancient-cylinder-line-build.log`,
`/private/tmp/wt17-pointed-line-neck-build.log`,
`/private/tmp/wt17-cylinder-line-audit.log`, and
`/private/tmp/wt17-cylinder-line-root-build.log`.
The bounded-distance headline remains unchanged and open.


## Long minimizing segments produce strong necks

The continuation after `923e29242` proves a quantitative strong-neck producer for
normalized oriented ancient kappa-solutions. For each neck tolerance, sufficiently
long almost-isometric segments through the basepoint force a genuine strong neck.
The exact minimizing-segment statement is a corollary. The proof constructs a line
in a compactness limit, classifies that limit as the normalized shrinking cylinder,
and transfers its finite-order spacetime comparison back to the approximating
solutions. It does not treat finite-interval source flows as ancient solutions.

The underlying line-limit theorem allows distances between segment points to have
multiplicative errors tending to zero. The inverse-metric and inverse-distance
foundations, and the generic pointed line-limit construction, now live under
`Geometry/Metric/Comparison` and
`Geometry/Compactness/CheegerGromov/Pointed/Convergence`. Existing namespaces and
public declarations are preserved; model-space hypotheses are generalized from
inner product spaces to finite-dimensional normed spaces. Static ball capture was
also separated from its flow-specific witness application.

This is the compactness and splitting argument of Kleiner--Lott, Section 49,
Proposition 49.1 and Corollary 49.2, used in Section 52, Lemma 52.14(2), in
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
The application to actual windowed source models is the next step; the
bounded-distance headline remains open, with 21 retained source sorrys.

All twenty added, moved, or affected declarations passed thirteen declaration
linters and have standard-axiom-only transitive closures. Changed leaves and
consumers built without diagnostics. The final root build passed 20,177 jobs with
exactly the 21 retained sorry warnings and no other diagnostics. Evidence is in
`/private/tmp/wt17-long-segment-necks-build.log`,
`/private/tmp/wt17-almost-line-neck-interface-build.log`,
`/private/tmp/wt17-long-segment-necks-audit.log`, and
`/private/tmp/wt17-long-segment-necks-root-build.log`.

## Strong necks in the actual normalized sources

The continuation after `4347c4c14` proves the finite-interval source application.
`WindowedSegmentNecks.lean` transfers a minimizing segment into the ancient model
using quantitative inverse-distance control on a buffered compact metric ball,
produces a model strong neck, and transfers the neck back to the source.
`NormalizedSegmentNecks.lean` supplies the source orientation and time-window
regularity directly from `NormalizedSequence.higher_good` and the actual interval
carrier. It proves that a high-curvature point on a minimizing segment is a strong
neck center when both remaining segment lengths are large in its curvature scale.
This includes the genuine terminal endpoint and requires no positive-time extension
or nonnegative source Ricci curvature.

The same module passes scalar and segment-length limits into the neck theorem.
Together with scalar divergence and the previously proved quantitative remaining
length bound, it yields eventual source necks near the missing endpoint. The next
assembly connects this statement to all the actual witnesses returned by the
escaping-limit producer. The geometric limit's necks and the horn/cone producers
remain unfinished; the bounded-distance headline remains open.

These are the source-model and long-segment steps of Kleiner--Lott, Section 52,
Lemma 52.14(2), using Section 49, Proposition 49.1, in the local
`BooksPapers/KleinerLottPerelman.pdf`. Morgan--Tian, Chapter 10, Propositions 10.7
and 10.12, remains the companion reference for the subsequent finite-end geometry.

Both new leaves are registered. All five new public declarations passed thirteen
declaration linters and have only the permitted standard axioms in their transitive
closures. The final leaf build passed 14,087 jobs; its only warnings were inherited
retained sorrys. The root build passed 20,179 jobs with exactly the same 21 retained
sorry warnings and no other diagnostics. Evidence is in
`/private/tmp/wt17-source-segment-necks-build.log`,
`/private/tmp/wt17-source-segment-necks-audit.log`, and
`/private/tmp/wt17-source-segment-necks-root-build.log`.

## Escaping-limit assembly with genuine source necks

The continuation after `d559da9a6` adds
`exists_terminal_pointed_limit_with_missing_endpoint_and_necks` in
`NormalizedEscapeNecks.lean`. From failure of bounded curvature at distance, this
producer returns the actual pointed limit, source convergence maps and geodesics,
missing completion point, nonnegative limit sectional curvature, scalar divergence,
and the prescribed quantitative curvature-distance separation. It additionally
returns eventual strong necks centered at the actual source geodesic points as the
limit parameter approaches the missing endpoint. Moving-point scalar convergence
is proved through the actual inverse convergence maps, with source membership
established from the minimizing segment and the precise target balls.

The preceding escaping-limit statement is unchanged. The new conclusion constructs
source necks; it does not yet claim necks in the incomplete limit or a realized
finite horn. The bounded-distance theorem and the 21 retained sorrys remain open.
This is the source part of Kleiner--Lott, Section 52, Lemma 52.14(2), in the local
`BooksPapers/KleinerLottPerelman.pdf`.

The new declaration passed thirteen declaration linters and its transitive axiom
closure contains only `propext`, `Classical.choice`, and `Quot.sound`. The leaf build
passed 14,212 jobs. The root build passed 20,180 jobs, with exactly the same 21
retained sorry warnings and no other diagnostics. Evidence is in
`/private/tmp/wt17-escape-necks-build.log`,
`/private/tmp/wt17-escape-necks-audit.log`, and
`/private/tmp/wt17-escape-necks-root-build.log`.

## Inverse metric control and spatial neck transport

The continuation after `27ff63d12` proves compact, fixed-order convergence of
metric differences measured in the approximating metric's connection and norm.
`Pointed/Convergence/InverseMetric.lean` gives this inverse comparison from canonical
pointed convergence, without completeness or boundarylessness assumptions.
`StaticComparison.lean` constructs an actual static `MetricComparisonOn` on a compact
set from the local pulled-back metric and its derivative bounds, by smooth tensor
extension. Its pullback is tied to the supplied map by the derivative equation.

`StrongNeck.toSpatialNeck` freezes the genuine terminal slice. The new local spatial
neck transport theorem uses the actual partial diffeomorphism, proves its map
equation, and requires only the compact cylinder buffer needed for tensor extension.
`SpatialNeck` moved unchanged into `FiniteHornGeometry.lean`. Replacing the accidental
`ComparisonComposition` import of `AncientExtension` removes the path from the source
neck producers back to the bounded-distance headline. `WindowedModelLimit` now
imports its terminal window lemma directly.

These are comparison steps toward Kleiner--Lott Section 52, Lemma 52.14(2), in
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/KleinerLottPerelman.pdf`.
The actual inverse-map comparison, limit necks, and horn/cone producers remain
unfinished. The bounded-distance headline and the same 21 retained sorrys remain open.

All four new public declarations passed thirteen declaration linters and have only
`propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closures.
The affected-consumer build passed 14,213 jobs. The additional static-comparison and
direct-import repair build passed 13,847 jobs. The final root build passed 20,182
jobs, with exactly 21 retained sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-inverse-metric-spatial-neck-build.log`,
`/private/tmp/wt17-static-comparison-build.log`,
`/private/tmp/wt17-inverse-metric-spatial-neck-audit.log`, and
`/private/tmp/wt17-inverse-metric-spatial-neck-root-build.log`.

## Actual inverse comparisons and independent scale factors

The continuation after `1418f1d06` adds `PointedInverseComparison.lean`. Canonical
pointed metric convergence now produces static comparisons along the actual inverse
convergence maps, on the actual images of compact limit sets. The proof supplies
domain containment, pulls back the restricted limit metric through the inverse
diffeomorphism, and verifies its derivative equation in the ambient manifolds.
No completeness assumption is used.

`ComparisonStaticScaling.lean` independently rescales the source and target metrics
in a static comparison. Its explicit error bound accounts for the difference of
scale factors and for each finite derivative order. The pointed inverse comparison
therefore remains valid when the two positive scale factors converge to a common
positive limit. This supports the distinct source and limit scalar normalizations
needed for the neck step of Kleiner--Lott Section 52, Lemma 52.14(2).

The three new public declarations passed thirteen declaration linters. Their axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`. The scaling
leaf build passed 11,773 jobs; the final inverse comparison leaf build passed
11,777 jobs. The root passed 20,184 jobs with the same 21 retained sorry warnings
and no other diagnostics. Evidence: `/private/tmp/wt17-static-rescaling-build.log`,
`/private/tmp/wt17-pointed-inverse-comparison-build.log`,
`/private/tmp/wt17-pointed-inverse-comparison-audit.log`, and
`/private/tmp/wt17-pointed-inverse-comparison-root-build.log`.

The bounded-distance headline remains open. Actual limit neck construction still
requires source neck image containment and alignment of the moving neck centers.
The next geometric route under investigation allows a neck center to lie near,
rather than exactly on, the long minimizing segment. The finite horn and cone
producers remain unfinished.


## Neck centers near long minimizing segments

The continuation after `34f6e73d0` allows a neck center to be a bounded distance
from the center of a long segment, measured in the scalar-normalized metric.
`Pointed/Convergence/Line.lean` now constructs an intrinsic line when the segment
centers remain bounded from the pointed basepoints. The line need not pass through
the basepoint; cylinder classification needs only an intrinsic line somewhere in
the limit. The exact-center line conclusions retain their original signatures.

The resulting kappa-solution theorem propagates through `WindowedSegmentNecks`
and `NormalizedSegmentNecks`. The windowed proof explicitly enlarges its capture
ball by the center displacement. In a normalized finite-interval sequence, centers
converging to the source geodesic points inherit strong necks when the scalar and
two normalized segment lengths satisfy the original bounds. The exact-center neck
theorems retain their original statements as corollaries. The existing map-distance
continuity lemma was promoted to a public method without changing its proof.

This implements the nearby-center step toward Kleiner--Lott Section 52, Lemma
52.14(2), and the fixed-limit-point necks used in Morgan--Tian Chapter 10,
Claim 10.8. The local PDFs are `KleinerLottPerelman.pdf` and
`MorganTianPoincare.pdf` under
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers`.

Twenty public declarations passed all thirteen applicable declaration linters and
have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom closures.
The affected `NormalizedEscapeNecks` build passed 14,032 jobs. The full root passed
20,184 jobs with exactly the same 21 retained sorry warnings and no other
diagnostics. Evidence: `/private/tmp/wt17-normalized-near-segments-build.log`,
`/private/tmp/wt17-near-segment-necks-audit.log`, and
`/private/tmp/wt17-near-segment-necks-root-build.log`.

The bounded-distance headline remains open. The next assembly places source necks
at actual images of fixed limit points and captures their buffered images in a
compact limit ball, before transporting them to spatial necks. The finite horn and
cone producers remain unfinished.


## Spatial necks on the incomplete curvature-escape limit

The continuation after `9456d6131` proves actual spatial necks along the limiting
geodesic approaching the missing endpoint. `PointedSegmentNecks.lean` combines
inverse convergence, scalar convergence, and the nearby-segment theorem to place
source strong necks exactly at the images of fixed limit points. No common future
time interval or ancient-source hypothesis is introduced.

`PointedSpatialNecks.lean` transfers these necks through the actual inverse maps.
A quantitative radius condition captures the entire buffered neck image inside the
image of a compact limit ball. The proof uses metric lower bounds to establish
containment and the independently rescaled inverse comparisons to transfer the
finite-order terminal spatial jets. It requires neither a complete limit nor
connected source manifolds.

`NormalizedLimitNecks.lean` supplies those inputs from the existing curvature-escape
producer. Its theorem
`exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks` preserves the
actual pointed convergence, geodesics, nonnegative limit curvature, missing completion
endpoint, and arbitrarily prescribed scalar-distance separation, and additionally
produces spatial necks along the limit geodesic sufficiently near that endpoint.
Compact balls around those points are obtained inside the already controlled
basepoint balls. This closes the spatial-neck step in Kleiner--Lott Section 52,
Lemma 52.14(2); the tube/end and cone constructions are still unfinished.

All four new public theorems passed thirteen declaration linters and have only
`propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closures.
The final leaf build passed 14,040 jobs. The full root passed 20,187 jobs with exactly
21 retained sorry warnings and no other diagnostics. The import graph has no path
from `NormalizedLimitNecks` back to `FiniteHornStructure` (6,035 modules traversed).
Evidence: `/private/tmp/wt17-normalized-limit-necks-build.log`,
`/private/tmp/wt17-normalized-limit-necks-audit.log`, and
`/private/tmp/wt17-normalized-limit-necks-root-build.log`.

The bounded-distance headline remains open. The next task is the geometric assembly
of the neck neighborhoods into a finite end, retaining the actual source convergence
needed to construct and exclude the cone. Morgan--Tian Appendix A, Proposition A.11
and Lemmas A.13--A.18, describe the neck overlap and chain steps. The extracted text
of Proposition A.19 and Lemma A.20 has inconsistent separation wording: A.18 requires
separating spheres, whereas A.19 says nonseparating. The formal argument must establish
the correct separation property rather than copy that wording.

## Compact spatial neck slabs and actual metric balls

The continuation after `0d7f8cffe` generalizes the neck-region geometry to static
spatial necks and arbitrary interior slabs. `SpatialNeck.isCompact_image_slab`,
`isOpen_image_openSlab`, and `frontier_image_slab` prove compactness, openness, and
the exact two-sphere frontier. `SpatialNeck.image_slab_subset_closedBall` bounds
the slab in an actual ambient metric ball, and `ball_subset_image_slab` captures
an actual ambient ball inside the slab using the metric lower bound. These
statements require no completeness. The existing strong-neck region theorems
retain their signatures and now follow as corollaries.

The leaf build passed 10,814 jobs. Nine public declarations passed thirteen
applicable declaration linters; all transitive axioms are among `propext`,
`Classical.choice`, and `Quot.sound`. The full root passed 20,187 jobs with exactly
21 retained sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-spatial-neck-balls-build.log`,
`/private/tmp/wt17-spatial-neck-slabs-audit.log`, and
`/private/tmp/wt17-spatial-neck-slabs-root-build.log`.

The bounded-distance headline and the geometric end/cone producers remain open.

## Spatial neck charts, curvature ratios, and actual overlap graphs

The continuation after `09ac601c7` connects spatial necks to the existing generic
cylindrical-chart API. `MetricComparisonOn.metricDerivNorm_of_local_metric`
generalizes the existing open-pullback derivative identity to arbitrary finite-dimensional
normed source models and independent source/target universes. The
old same-model theorem keeps its signature as a corollary.
`CylinderReference.metric_zero_eq_roundCylinder` identifies the static model.
`SpatialNeck.cylindricalChart` uses the actual partial diffeomorphism on its full
controlled window; its `metricCloseOn` estimate and scalar-ratio estimate follow
from the existing covariant-jet and cylindrical curvature APIs.

`SpatialNeck.image_slab_subset_of_center_mem_slab` is an actual overlap producer:
for sufficiently small precision, if the second center is in a slab of the first
neck of radius at most one tenth of its coordinate window, every slab of the
second neck of the same maximum radius lies in the first neck's full chart.
Scalar comparison controls the relative scales; the triangle inequality and the
proved ball-capture theorem establish the containment. No completeness is assumed.
`SpatialNeck.exists_graph_in_nearby_neck` then constructs a smooth graph and a
sphere diffeomorphism for every cross-section in that smaller slab. It consumes
the existing least-Ricci alignment and transverse product-chart graph theorems.
This is the contained-sphere portion of Morgan--Tian, `MorganTianPoincare.pdf`,
Appendix A, Proposition A.11(4), with quantitative containment supplied explicitly.

Nine declarations passed all thirteen applicable declaration linters and have
only the three approved foundational axioms. The final leaf passed 11,176 jobs;
the full root passed 20,189 jobs with exactly 21 retained sorry warnings and no
other diagnostics. The overlap module has no dependency on `FiniteHornStructure`
(2,471 reachable project modules inspected). Evidence:
`/private/tmp/wt17-spatial-neck-overlap-build.log`,
`/private/tmp/wt17-spatial-neck-overlap-audit.log`, and
`/private/tmp/wt17-spatial-neck-overlap-root-build.log`.

The bounded-distance headline is still open. The next construction chooses necks
along the limiting geodesic with steps proportional to their curvature scales,
proves that they approach the missing endpoint, and assembles the end geometry.

## Curvature-scale neck sequences and disjoint central spheres

The continuation after `3d53774e2` constructs a sequence of necks along an actual
isometric curve with the previously proved scalar-distance separation.
`exists_spatialNeck_sequence_along_isometric_curve` produces strictly increasing
parameters tending to the missing endpoint, with increments exactly one fortieth
of the coordinate-window radius divided by the square root of the center scalar
curvature. Each intervening curve segment lies in the corresponding inner neck
slab. Adjacent cross-sections are related by smooth graphs and sphere
diffeomorphisms, and all central spheres are pairwise disjoint.

The iteration argument lives in `Topology/Order/Iteration.lean`: the primary
result works in a conditionally complete linear order with its order topology;
the continuous-step corollary additionally uses an ordered additive group with
continuous addition. `SpatialNeckSeparation.lean` proves disjointness from an
actual lower bound on the distance between centers, using the scalar comparison
at a hypothetical common point and the metric bounds on central spheres. These
results require neither complete ambient manifolds nor ancient source flows.

Four public declarations passed thirteen applicable declaration linters and have
only the three approved axioms. The leaf passed 11,179 jobs and the full root
passed 20,192 jobs with exactly the same 21 retained sorry warnings. Evidence:
`/private/tmp/wt17-spatial-neck-sequence-build.log`,
`/private/tmp/wt17-spatial-neck-sequence-audit.log`, and
`/private/tmp/wt17-spatial-neck-sequence-root-build.log`.

The next application restricts the produced incomplete limit geodesic to a tail
where every point has a spatial neck. The ordered neck sequence must still be
assembled into a finite end and used to construct the cone. The bounded-distance
headline remains open.

## Disjoint neck sequences produced from normalized curvature escape

The continuation after `29f6bc13b` proves
`exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence`
in `NormalizedNeckSequence.lean`. Starting from failure of bounded curvature at
distance, it retains the full source convergence, missing completion endpoint,
nonnegative limit curvature, and prescribed scalar-distance separation, and
constructs a sequence of spatial necks whose centers approach that endpoint.
Successive central spheres are smooth graphs in the preceding neck charts, and
all the central spheres are pairwise disjoint. A tail of the limit geodesic is
chosen from the actual eventual neck and scalar-divergence conclusions; no neck
sequence or cross-section producer is added as a hypothesis.

The new theorem passed thirteen declaration linters and has only `propext`,
`Classical.choice`, and `Quot.sound` in its axiom closure. The leaf passed 14,118
jobs, and the full root passed 20,193 jobs with exactly 21 retained sorry warnings
and no other diagnostics. Evidence:
`/private/tmp/wt17-normalized-neck-sequence-build.log`,
`/private/tmp/wt17-normalized-neck-sequence-audit.log`, and
`/private/tmp/wt17-normalized-neck-sequence-root-build.log`.

Pairwise disjoint spheres are not yet an assembled finite horn and do not by
themselves assert separation of the entire ambient manifold. The annular assembly,
finite-end geometry, and cone producer remain necessary. The bounded-distance
headline remains open.

## Annuli between successive spatial neck cross-sections

The continuation after `cf64b2344` constructs actual compact annuli between
successive central spheres. `SpatialNeck.exists_annulus_in_nearby_neck` produces a
partial diffeomorphism defined on a neighborhood of the full closed unit cylinder,
with explicit endpoint maps, the exact two-sphere frontier, and containment in the
preceding neck's controlled window. Both the isometric-curve neck-sequence theorem
and `exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence`
now retain these annuli in their conclusions.

The general graph-band homeomorphism and diffeomorphism now require distinct
endpoint values rather than an ordering. The closed-strip image is the unordered
band between the two graphs. `exists_graphBand_partialDiffeomorph` proves the
compact-image and frontier statements in arbitrary manifold product charts.
The generic image/interior/frontier results for open partial homeomorphisms were
moved into `Topology/OpenPartialHomeomorph/Images.lean`; the existing cap-transport
signatures remain as corollaries, and the duplicate private neck-frontier argument
was removed.

The geometric input follows Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*,
Appendix A, Proposition A.11(4), in
`/Users/bennettchow/Documents/Codex/Geometrization/BooksPapers/MorganTianPoincare.pdf`.
No ambient separation or annulus-interior disjointness is asserted by this layer.
The global fitting and end-frontier arguments of Lemmas A.13–A.15 still require
proof, as does the cone producer. `bounded_curvature_at_distance` remains open.

Twenty-four declarations passed thirteen declaration linters. Every inspected
axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
The normalized leaf passed 14,120 jobs. The full root passed 20,195 jobs with
exactly 21 retained sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-normalized-annuli-build.log`,
`/private/tmp/wt17-neck-annuli-audit.log`, and
`/private/tmp/wt17-neck-annuli-root-build.log`.

## Local finiteness and the closed annular union

The continuation after `9b1a1f335` proves local finiteness of neck windows from
scalar curvature divergence. `SpatialNeck.locallyFinite_of_scalar_tendsto_atTop`
allows arbitrary index sets with the cofinite filter and varying neck tolerances
bounded by a common value below `1 / 4323`. The scalar-ratio estimate yields a
positive multiple of center curvature as a lower bound throughout each window.
The general topology input,
`UpperSemicontinuous.locallyFinite_of_tendsto_lower_bound`, works for upper
semicontinuous maps into a preorder with no maximal elements.

The normalized escape producer now chooses an explicit family of annulus maps
and retains local finiteness of both their images and the containing neck windows.
Their union is closed, connected, and noncompact in the smooth limit, and its
frontier is contained in the union of the central spheres. The endpoint maps
remain explicit. Connectedness uses the actual common central spheres; local
finiteness rules out compactness of the infinite union. The general
`LocallyFinite.frontier_iUnion_subset` provides the frontier inclusion.

This is the local-finiteness mechanism used in Morgan–Tian, *Ricci Flow and the
Poincaré Conjecture*, Appendix A, Lemma A.15, in the read-only local
`Geometrization/BooksPapers/MorganTianPoincare.pdf`. The current statement does not
yet assert that only the outermost sphere is on the frontier. Quantitative
annulus separation, fitting at adjacent spheres, the finite-end geometry, and
the cone producer remain to be proved. The bounded-distance headline is open.

Four declarations passed thirteen declaration linters, with only `propext`,
`Classical.choice`, and `Quot.sound` in the inspected axiom closures. The normalized
leaf passed 14,123 jobs. The full root passed 20,198 jobs with exactly 21 retained
sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-normalized-neck-locally-finite-build.log`,
`/private/tmp/wt17-neck-local-finiteness-audit.log`, and
`/private/tmp/wt17-neck-local-finiteness-root-build.log`.

## Distance along arbitrary axial segments

The continuation after `9c677ac68` generalizes the collar distance estimate from a
segment ending at height zero to arbitrary endpoints. The new
`collar_axial_segment_edist_le` needs only containment of the actual vertical
segment in the comparison domain. The original `collar_axial_edist_le` keeps its
signature and is now a corollary. Its duplicate private distance-commutativity
lemma was removed in favor of the metric-distance API.

`SpatialNeck.edist_same_fiber_le` applies this estimate with the exact curvature
rescaling. `SpatialNeck.central_sphere_subset_closedBall` exposes the radius
`7 / sqrt R` bound previously private in the sphere-separation proof. That proof
now consumes the public ball-containment statement. These estimates prepare
bounds for graph annuli from both endpoint centers, needed for quantitative
separation and gluing of the annular union.

The geometry is the elementary axial/transverse length comparison in
Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Appendix A, §2 (in particular
the diameter conclusion of Lemma A.4), in the read-only local
`Geometrization/BooksPapers/MorganTianPoincare.pdf`. The finite-end and cone
producers, and the bounded-distance headline, remain open.

Five declarations passed thirteen declaration linters, with only `propext`,
`Classical.choice`, and `Quot.sound` in all inspected axiom closures. The changed
leaf and separation dependent passed 11,178 jobs. The full root passed 20,198
jobs with exactly 21 retained sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-spatial-neck-fiber-distance-build.log`,
`/private/tmp/wt17-axial-distance-audit.log`, and
`/private/tmp/wt17-axial-distance-root-build.log`.

## Two-center bounds for the actual annuli

The continuation after `df87dc141` proves graph-band containment in explicit
closed balls around both neck centers. The first estimate permits different
neck tolerances and arbitrary graph functions; regularity is needed only for
the annulus construction. The annulus producer retains its actual height
interpolation. The new metric version derives positive slab radius and chart
containment from the center-distance bound.

For the neck sequence, a slab radius `eps⁻¹ / 36` gives containment of each
annulus in balls about both adjacent centers of radius
`(3 * eps⁻¹ / 100) / sqrt R`, exactly six-fifths of the center spacing. The
normalized escape producer now retains these bounds for its actual annulus
family. The inputs are the axial and central-sphere length estimates and the
proved scalar comparison on the overlapping neck. This is the quantitative
geometry behind Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Appendix A,
Proposition A.11 and the chain arguments in Lemmas A.13–A.16, in the read-only
`Geometrization/BooksPapers/MorganTianPoincare.pdf`.

All five changed public declarations passed thirteen declaration linters and
have only the approved foundational axioms. The annulus leaf passed 11,178 jobs,
the sequence leaf 11,181 jobs, and the normalized dependent 14,123 jobs. The full
root passed 20,198 jobs with exactly 21 retained sorry warnings and no other
diagnostics. The bounded-distance headline remains open; nonadjacent annulus
separation and adjacent fitting are the next geometric steps. Evidence:
`/private/tmp/wt17-annulus-two-center-leaf-build.log`,
`/private/tmp/wt17-sequence-annulus-balls-leaf-build.log`,
`/private/tmp/wt17-normalized-annulus-balls-build.log`,
`/private/tmp/wt17-annulus-balls-audit.log`, and
`/private/tmp/wt17-annulus-balls-root-build.log`.


## Exact boundary of the annular tail

The continuation after `46dfd2754` proves that nonadjacent annuli of the actual
neck sequence are disjoint, that the interiors of the tail annuli are pairwise
disjoint, and that adjacent tail annuli intersect exactly in their shared central
sphere. The metric separation uses the two-center bounds and comparison of
successive curvature scales. The initial annulus supplies the boundary buffer.

A general collar theorem proves that each shared sphere lies in the interior
of the union of its two adjacent annuli. It uses an actual open product chart,
regular closedness, connectedness of the cross-section, and disjoint interiors.
A separate locally finite closed-chain theorem then identifies the frontier of
the tail union with its first central sphere. The normalized escape producer
now retains all these properties, together with closedness, connectedness, and
noncompactness of the tail union. This supplies actual seams and boundary
identification in the annular-chain argument of Morgan–Tian, *Ricci Flow and the
Poincaré Conjecture*, Appendix A, Proposition A.11 and Lemmas A.13–A.16, in
`Geometrization/BooksPapers/MorganTianPoincare.pdf`. A global tube, the finite-end
and cone producers, and the bounded-distance headline remain open.

All nine changed public declarations passed thirteen declaration linters and
have only approved foundational axioms. The regular-closed leaves passed 940
jobs, the frontier-chain leaf 902 jobs, and the collar-union leaf 1,800 jobs.
The final static and normalized dependent build passed 14,130 jobs without
diagnostics. The full root passed 20,200 jobs with exactly 21 retained sorry
warnings and no other diagnostics. The declaration audit was repeated after
the final source cleanup. Evidence:
`/private/tmp/wt17-regular-closed-frontier-leaf-build.log`,
`/private/tmp/wt17-frontier-chain-leaf-build.log`,
`/private/tmp/wt17-collar-union-leaf-build.log`,
`/private/tmp/wt17-annular-chain-frontier-dependents-build.log`,
`/private/tmp/wt17-annular-chain-frontier-audit.log`, and
`/private/tmp/wt17-annular-chain-frontier-root-build.log`.


## The limiting axis and endpoint containment

The continuation after `44ca9a288` proves that the limiting geodesic, from its
second selected neck center onward, lies in the interior of the annular tail.
The actual seam supplies an interior starting point. The exact frontier and the
central-sphere diameter estimate prevent the isometric geodesic from crossing
the first sphere afterward. Every point of annulus `n` also lies within
`(11 / 5) * (F.radius - t n)` of the same missing completion point. Thus the
whole annuli, not only their centers, shrink toward that endpoint. These are
quantitative ingredients of the finite-end construction in Kleiner–Lott,
*Notes on Perelman's papers*, §52, Step 2 and Lemma 52.14, in the read-only
`Geometrization/BooksPapers/KleinerLottPerelman.pdf`.

The existing closed-cover API now glues homeomorphisms over arbitrary locally
finite closed covers, using compatibility in both directions, and exposes the
forward and inverse restrictions to every piece. No separation, compactness,
or countability assumptions were added to this general construction. The
actual cylinder-chain assembly remains the next consumer; the bounded-distance
headline is still open.

Four declarations passed thirteen declaration linters with only approved
foundational axioms. The normalized leaf passed 14,130 jobs, and the closed-cover
leaf passed 897 jobs, without diagnostics. The full root, including affected
dependents, passed 20,200 jobs with exactly 21 retained sorry warnings and no
other diagnostics. Evidence:
`/private/tmp/wt17-normalized-annular-axis-leaf-build.log`,
`/private/tmp/wt17-homeomorph-closed-cover-leaf-build.log`,
`/private/tmp/wt17-annular-endpoint-closed-cover-audit.log`, and
`/private/tmp/wt17-annular-endpoint-closed-cover-root-build.log`.


## Actual cylinder parametrizations of the annular end

The continuation after `a7ce2cb39` constructs a homeomorphism from
`Sphere 2 × Ici 0` onto the actual normalized annular tail, and a compatible
homeomorphism from `Sphere 2 × Ioi 0` onto its interior. The first map agrees on
every unit strip with the produced partial diffeomorphism, after the recursively
determined sphere reparametrizations. The second map is the restriction of the
first through the canonical inclusion of the positive half-line.

The general cylinder-chain theorem works for arbitrary topological
cross-sections and ambient spaces. It glues locally finite closed cylinder
pieces with the actual specified boundary identifications; nonadjacent pieces
are disjoint, and adjacent pieces intersect exactly in their common boundary.
The forward and inverse compatibility proofs both use those geometric
conditions. The separate interior-restriction API works over any partially
ordered topological parameter space, with no order-topology assumption. It
retains forward and inverse compatibility with the original homeomorphism.
These give the topological cylinder in the annular-chain construction of
Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Appendix A, Lemmas
A.13–A.16, in `Geometrization/BooksPapers/MorganTianPoincare.pdf`.

These are topological parametrizations; no smoothness across glued seams is
claimed. The existing `GlobalNeckTube` interface is still unchanged. Inspection
found that its consumers use smoothness of individual barrier spheres, in
addition to the topological tube properties. The finite-horn and cone producers
and the bounded-distance headline remain open.

Five public declarations passed thirteen declaration linters with only approved
foundational axioms. The cylinder-chain leaf passed 1,619 jobs, the interior
restriction leaf 915 jobs, and the normalized dependent 14,133 jobs, with no
diagnostics. The full root passed 20,202 jobs with exactly 21 retained sorry
warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-cylinder-chain-leaf-build.log`,
`/private/tmp/wt17-homeomorph-interior-leaf-build.log`,
`/private/tmp/wt17-normalized-cylinder-leaf-build.log`,
`/private/tmp/wt17-normalized-cylinder-audit.log`, and
`/private/tmp/wt17-normalized-cylinder-root-build.log`.


## Containment of entire later neck windows

The continuation after `e45ac798a` proves that every sufficiently late full
spatial-neck window lies inside the interior of the actual annular end. The
frontier is a compact central sphere. Local finiteness makes later windows
avoid that sphere, while the limiting axis gives an interior point in each
window. Connectedness then puts the entire window inside. This is an actual
containment conclusion for the produced neck maps, with their original scale
windows unchanged.

The underlying topological theorem handles any locally finite family that is
eventually preconnected and eventually meets the interior of a set with compact
frontier. It requires no separation axiom or metric. The new containment is a
further ingredient in Morgan–Tian's annular-end construction, Appendix A,
Lemmas A.13–A.16, and allows the local neck geometry to be restricted to the
constructed open end. The finite-horn and cone producers and the headline
remain open.

Both changed declarations passed thirteen declaration linters and have only
approved foundational axioms. The frontier leaf passed 902 jobs, the normalized
dependent passed 14,133 jobs, and the full root passed 20,202 jobs. Only the 21
retained sorry warnings appeared in the full build; the leaves and audit were
otherwise clean. Evidence:
`/private/tmp/wt17-eventual-interior-leaf-build.log`,
`/private/tmp/wt17-normalized-neck-capture-leaf-build.log`,
`/private/tmp/wt17-neck-window-capture-audit.log`, and
`/private/tmp/wt17-neck-window-capture-root-build.log`.


## The metric on the actual open annular end

The continuation after `00ca7b42b` transports the full spatial-neck charts to
the restriction of the limit metric to the constructed open annular end. The
constructor preserves the scalar normalization, pullback metric, jets, and
finite-order comparison estimates. Its source, forward inclusion, and inverse
compatibility laws are public. The normalized producer returns these actual
restricted necks at every sufficiently late selected center, with those same
compatibility laws.

The limiting axis now has an actual continuous lift into the open end, and its
intrinsic Riemannian distances equal its parameter distances. The general
metric result proves that a Lipschitz curve on any order-connected subset of
the real line keeps its Lipschitz constant after restriction to an open set.
It uses the existing preservation of continuous-curve variation, and derives
continuity from the ambient distance estimate. No smoothness of the limiting
axis or global glued cylinder is assumed. This supplies the intrinsic axis
used in Kleiner–Lott, *Notes on Perelman's papers*, section 52, Step 2 following
Lemma 52.14, in `Geometrization/BooksPapers/KleinerLottPerelman.pdf`. The metric
completion of the whole end and the finite-horn and cone producers are still
unproved; the bounded-distance headline remains open.

Six declarations passed thirteen declaration linters and have only approved
foundational axioms. The spatial-neck restriction leaf passed 10,804 jobs,
the curve restriction leaf 3,616 jobs, and the normalized dependent 14,140
jobs, without diagnostics. The full root passed 20,203 jobs with exactly the
21 retained sorry warnings and no other diagnostics. Evidence:
`/private/tmp/wt17-spatial-neck-restriction-leaf-build.log`,
`/private/tmp/wt17-curve-lipschitz-restriction-leaf-build.log`,
`/private/tmp/wt17-normalized-intrinsic-leaf-build.log`,
`/private/tmp/wt17-open-end-metric-audit.log`, and
`/private/tmp/wt17-open-end-metric-root-build.log`.
