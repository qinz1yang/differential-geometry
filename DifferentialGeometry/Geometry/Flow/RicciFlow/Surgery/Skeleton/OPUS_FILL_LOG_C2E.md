# OPUS fill log C2E (E2a + E: closed-start open-set package)

Worker: Opus 5.5, worktree D:\differential-geometry-pc3 @ 9126abc30. Append-only.

## 2026-09-26 Start

Targets (verbatim from DESIGN_C2_ASSEMBLY §5.1, §5.2):
- E2a `exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart`
- E `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain`

Read: AGENTS.md, DESIGN_C2_ASSEMBLY §1(c), §2, §5, H2-H3 digest, G1b ClosedStartPhase, G1c
ClosedStartCurve, H3a Exponential, H3b ExponentialSmooth, H3b' ExponentialFamily, MinDomain,
Window, SpeedBounds, DomainContinuation, CompactLowerBound, UniformBounds slab sups.

Plan:
- E2a (new file Perelman/LGeometry/Geodesic/ClosedStartVelocity.lean): slab bounds on
  Icc a b ⊆ Ico a c from hmetric (nablaKRmSlabSup / ricci slab sup), Gronwall via
  lRegularizedSpeedSq_le_of_gradient_ricci_bounds, cluster point by compactness, chart lower
  bound on a closed-start slab, coordinate Cauchy argument, phase ODE (lRegularizedCurve_phase)
  with lPhaseField continuous up to s = v.
- E (new files under Surgery/Topology/HistoryLGeometry/): local package at each Z0 in
  historyMinDomain; interior case via H3b open domain, closed-start case via G1b phase flow
  seeded at c0 < v; historyLAction continuity via window families + interval-integral
  continuity; U := union of local packages.

## Progress 1 — E2a proved

- New file `Perelman/LGeometry/Geodesic/ClosedStartVelocity.lean` (359 lines). E2a
  `exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart` proved, statement verbatim.
  Route: slab `Icc a ((a+c)/2) ⊆ Ico a c`; `ricciSlabSup`/`nablaKRmSlabSup` + `curvNormSq_eq`,
  `abs_scalarDifferential_le_of_curvature_jet`, `tensor02_quadForm_abs_le_normSq0S` give
  `|g(∇R,V)| ≤ G|V|`, `|Ric(V,V)| ≤ K|V|²`; `lRegularizedSpeedSq_le_of_gradient_ricci_bounds`
  (Gronwall) bounds the speed on `[s₂, v)`; compactness gives a cluster point `y`; a closed-start
  chart lower bound (private copy of `exists_chart_inner_bounds_on_compact` from `hmetric`) bounds
  chart velocities; the chart phase clusters at `z∞`; G1b `exists_lPhaseFlow_of_start` at
  `(v, z∞)`, seed `(s, z s)` inside the flow box, `eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn`,
  `tendsto_lVelocity_lift_of_family`. No bootstrap/exit-time argument needed.
- Compile note: `lake env lean` must get lakefile options: `-DmaxSynthPendingDepth=3` (else a
  typeclass timeout in the copied `inCoordinates` proof) plus `weak.linter.mathlibStandardSet`.
  Clean (0 errors, 0 warnings). Axioms: propext, Classical.choice, Quot.sound.

## Progress 2 — action continuity + interior package (E, part 1)

- New file `Surgery/Topology/HistoryLGeometry/ActionContinuity.lean` (~490 lines, all private so
  far, compiles clean). Contents: `pieceAction` (dif-guarded stage integral), partition/Lebesgue
  number assembly `continuousOn_pieceAction_of_local`, core `pieceAction_local_of_family` (any
  solution flow + C^∞ family + carrier + Lagrangian identification ⇒ continuity and
  integrability), window version, `ActionGoodNear` (local continuity at a parameter),
  `exists_continuousOn_historyLAction` (all parameters in `[0,v]` good ⇒ historyLAction
  continuous near Z₀), base family at `s = 0` (`actionGoodNear_zero`, lRegularizedFamily_extend
  + H3a uniqueness against truncation), interior endpoint (`hasPrefixFamily_end`), interior
  package `exists_package_of_mem_historyLExpOpenDomain` (H3b + H3b′).
- Note: a concurrent `lake build --old` in pc3 (not mine) deleted/rebuilt oleans 09:28–09:35;
  compiles failed with "object file does not exist" until it finished.
- Next: closed-start package (G1b flow seeded at c₀ < c < v from H3b′ at level c; new history
  curve, windows via `LWindow.exists_stage` + invFun lift), then E assembly.

## Progress 3 — E proved; DONE

- `ActionContinuity.lean` merged into the E file (single module; its lemmas stay private).
  Final E file: `Surgery/Topology/HistoryLGeometry/ExponentialClosedStart.lean` (1137 lines).
  Public: `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain` (statement verbatim
  from DESIGN_C2_ASSEMBLY §5.2; namespace `...Surgery.Topology.ObservedHistory`, variables
  `{first last} {T B v} {p}`, binder `{hle}`; `q` is the off-domain value of `f`).
- Closed-start package (`exists_package_of_closedStart`): stage-`first` incoming slab
  (`exists_incomingSlab_stageMetric`, `smoothUpTo.jointContMDiffOn` = `hmetric` on `Ico`); the
  history curve's stage-`first` tail is a slab geodesic on `(s₁, v)`; E2a gives the phase limit;
  G1b flow box at `(v, z∞)`; seed parameter `c₀` with `(c₀, st c₀)` in the box; `c = (c₀+v)/2`;
  `Z₀ ∈ historyLExpOpenDomain` at level `c` (truncation + restricted window); H3b′ family at `c₀`
  gives smooth seeds `σ(Z)`; `β̃(Z,·)` = phase-flow curve; ODE uniqueness on `J₁`, then
  `lRegularizedSolution_eqOn` up to `c`, endpoint continuity at `c`; new curve `A Z` (level-`c`
  history curve, `β̃` on stage `first` past `c`), windows past `c` by `LWindow.exists_stage` +
  invFun lift (`of_comp_localPullMetric`), initial vector by restricting the base window to
  `min W.b c`; `f(Z) = β̃(Z, v)` smooth; action continuity via the slab family near `[c, v]`,
  H3b′ at level `c` (transferred by truncation uniqueness) on `(0, c)`, base family at `0`.
- Interior case: H3b + H3b′ + `hasPrefixFamily_end`. U := ⋃ over `historyMinDomain` of the
  local packages; `f`, `L` = dif-extensions of `historyLExp`, `historyLAction`.
- Compile (read-only): concatenation of the two new files in scratch (neither has an olean),
  `lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true ...`: 0 errors,
  0 warnings. `#lint`: 0 errors (14 linters, 23 declarations). Axioms of both headlines:
  propext, Classical.choice, Quot.sound.
- Not done (outside "edit nothing else"): registration of the two new modules in
  `DifferentialGeometry.lean`; `lake build` of them.
