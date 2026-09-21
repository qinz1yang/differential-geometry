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
