# P1 COMPARISON-GEOMETRY PLAN

This is the single phase-specific execution plan for Poincare Phase P1.  The
whole-program authority remains
`../Flow/RicciFlow/POINCARE_PLAN.md`.  The implementation order is strict:
P1a, then P1b, then P1c.  P1d/Toponogov is outside this campaign except for
recording the dependency boundary exposed by P1c consumers.

The target denominator is the set of comparison statements actually consumed
by Morgan--Tian's P2/P3 route, not a complete textbook comparison-geometry
library.  A theorem endpoint counts as complete only when its final statement
is present, proved, focused-check green, and directly axiom-audited.  Existing
machinery is accounted for separately.

## Ownership and verification

- Work only in the current checkout.  Protect all existing dirty files and all
  active or stale claims owned by other work.
- Search `DifferentialGeometry/` first.  `RFreference/` and
  `RicciFlow/Morgan-Tian/` are read-only references for theorem shape and proof
  route; they are never imported into the native tree.
- Claim every Lean file before editing.  Use focused no-global-lock checks;
  refresh an explicitly named module only when a downstream import needs a new
  exported declaration or has a stale-olean failure shape.
- Every edited `Foo.lean` has a synchronized `Foo.md` recording route, reuse,
  blocker if any, and pass/fail without command transcripts.
- The main coordinator alone edits this plan.  P1 work does not edit
  `Perelman/LGeometry/` files.

## P1a -- Bishop--Gromov and required volume comparison

### Acceptance target

Freeze the exact Morgan--Tian P2/P3 consumers and match each to a native,
axiom-clean producer.  Reuse the checked `BishopBall`/normal-ball ratio,
packing, polar/Jacobian, and ball-volume machinery.  Add only a missing stronger
statement, thin adapter, or genuine producer required by those consumers.

### Running status (2026-08-27, exact consumer audit frozen)

- Project-used theorem endpoints: **87.5%** (seven of eight separately counted
  endpoints are checked: global model-ratio comparison, its zero-Ricci power
  form, the absolute Euclidean upper bound, the packing consequence, and the
  small-radius Euclidean epsilon normalization and positive-radius continuity
  used by MT 9.66, plus the strict positive-sectional-curvature Euclidean
  volume inequality used by MT 9.56).
- Dedicated native machinery: **about 98%**.  The polar/Jacobian/normal-ball
  engine, complete/global segment-ball engine, and compact-tail endpoint
  continuation are checked.  The exact framed-density/Haar normalization is
  now also warning-free focused-check and named-refresh green under the intended
  smooth-manifold binder, and the Euclidean model-ball normalization adapter is
  warning-free focused-check and named-refresh green.  The curvature-operator
  and sectional-to-Ricci bridges are also checked and refreshed.
  Radius continuity and radial equality propagation are checked and axiom-clean.
  Local minimizing-geodesic coverage remains the sole genuine
  missing-groundwork frontier.  Strict sectional-volume assembly is
  warning-free focused-check and named-refresh green and is included in the
  common direct axiom audit.
- Direct P2/P3 usage has global curvature hypotheses (compact/global in P2;
  complete with global nonnegative Ricci curvature in P3).  The local
  compact-closure form is needed only to reproduce the Chapter 5 incomplete
  compactness chain in its stated generality; it is tracked separately and is
  not silently charged to the already checked global theorem.
- Current action: P1a is closed at a precisely documented blocker after seven
  checked endpoints.  Release its file claims and start the P1b consumer/native
  audit.  Do not reopen the one remaining local compact-closure endpoint unless
  new geodesic-lift or raw-exp polar infrastructure appears.

### Remaining-frontier route audit

- **Local compact-closure form.**  The nearest native target is a radius-local
  minimizing-exponential coverage theorem for `RadialSurjectivity.radialMinSet`,
  with explicit `v in expDomain`.  The compact-tail continuation lemmas remove
  ambient completeness for an already supplied bounded-speed geodesic, but they
  do not construct the minimizing radial ray.  Moreover, the present `SegDom`,
  `SegInt`, `expJacDensity`, and segment-polar integration layer are built from
  `expMapIntrinsic`/`intrinsicGeodesic`, hence still require `CompleteSpace M`.
  Thus the faithful incomplete-manifold theorem needs both local minimizing-ray
  coverage and a raw-`expMap` local segment-polar bridge; adding compactness to
  the existing complete theorem would not solve this consumer.  The smallest
  honest first statement is `minExp_of_cptBall` in `RadialSurjectivity`: compact
  closed ball plus a point in the corresponding open ball produces a minimizing
  `v in expDomain`.  Its proof first needs a base-geodesic-to-initial-data phase
  lift (the absent `IsGeodesicOn.toWithInitial`) and a finite-horizon maximal
  extension; even this lemma alone does not remove the separate local-polar gap.
- **Equality rigidity.**  Three native routes were checked.  Direct tightness of
  the three inequalities in `segBall_vol_le_explicit` and a strict-defect
  contrapositive both reduce to the equality/strictness case of the traced
  matrix Riccati inequality; the radius-ratio route instead needs a shell
  derivative theorem for the polar ball integral before reaching the same
  radial equality.  The smallest common producer is an equality
  characterization for `Analysis.trace_sq_le_mul`, followed by a geometric
  equality-or-strict lemma for `mean_riccati_le`.  Those bottom two layers are
  checked and axiom-clean as `trace_sq_eq_iff`, `mean_sq_eq_iff`, and
  `mean_riccati_eq_iff`.  The radial propagation, strict Jacobian/model-volume,
  pole-Haar, Euclidean normalization, curvature-coordinate, and
  sectional-to-Ricci bridges are all warning-free focused-check and
  named-refresh green.  The final `segBall_lt_of_sec` endpoint is included in
  the common direct audit and depends only on the standard logical axioms.

## P1b -- Cheeger lemma and CGT injectivity

P1b starts only after P1a closes or reaches a precisely recorded genuine
blocker.  The known P0 chain `intrInj_ge_cgt -> injDecay_of_bg -> flowInj_of_vol`
must be reused and must not be reopened.  The acceptance target is the exact
additional P2/P3 injectivity statement, if any.

### Running status (2026-08-27, exact consumer set frozen)

- Project-used theorem endpoints: **0%** (zero of two separately counted
  endpoints are yet proved in their exact local-on-balls P3 shape).
- Dedicated native machinery: **about 94%**.  The Whitehead/Jensen/propeller
  stack, `intrInj_ge_cgt`, `injDecay_of_bg`, and `flowInj_of_vol` are
  source-complete with no `sorry`/`admit`; the realized P0 chain is historically
  axiom-clean.  The new `intrInj_ge_cgt_on` radial-local strengthening is
  warning-free focused-check and named-refresh green while preserving the old
  global API.  The quantitative `intrInj_ge_vol` assembly is also focused- and
  named-refresh green; it combines local-radial CGT with the existing ball and
  pull-volume upper bounds.  Its current public interface accepts an ambient
  extended-ball curvature bound; `intrFrame_mem_eball` creates the radial input,
  and `framedExp_not_conj` eliminates a redundant public nonconjugacy premise.
  It still exposes completeness and local-diffeomorphism.  The common direct
  audit is green for all 28 P1a/P1b declarations, with only the three standard
  logical axioms.  The sequence-level producers still use global
  curvature/bounded geometry, while P3 supplies bounds separately on each fixed
  bounded ball.
- Exact endpoints: E1 has global nonnegative Ricci curvature, compact closure
  of a relevant larger ball, and full-curvature/volume control only there, and
  concludes a point injectivity lower bound; E2 propagates a uniform base
  injectivity/noncollapse bound to a uniform injectivity bound on each fixed
  bounded ball.  P2 has no direct P1b call.  Most P3 inputs are complete
  kappa-solutions, but the `volcomp` use at `temp2kappa:2668` explicitly allows
  an incomplete ambient and prevents completeness from being imposed globally.
- Current action: implement the smallest incomplete-ambient producer
  `frame_mem_expDom`, deriving raw exponential-domain coverage from compactness
  of a buffered extended ball.  This attacks the shared Route 1 blocker before
  any raw CGT port or E2 assembly.

### Remaining-frontier route audit

1. **Direct compact-tail / partial-exp route (preferred).**  The incomplete
   ambient has the raw `framedInjRadius`, `exp_dom_of_inj`,
   `endpointCont_compact`, `geo_Ioo_extend_cpt`, and the non-complete Zorn
   extension wrapper.  The missing producer is a local Hopf--Rinow theorem from
   compact closure of a larger intrinsic ball to both tangent-ball exp-domain
   coverage and metric-ball coverage by `radialMinSet`.  Exp-domain coverage
   alone does not supply the local Bishop/polar ball-volume upper bound, and the
   existing CGT collision proof would then still need a raw partial-exp port.
2. **Complete metric surgery on an open restriction.**  `restrictOpen`,
   `geodesicOn_open_iff`, curvature naturality, and
   `bumpExtend_complete` exist.  This route fails earlier: the last theorem
   needs a pre-existing complete background metric and does not construct one
   on an arbitrary open subtype.  Even with such a metric, no buffered
   equality theorem transfers small-ball distance, volume, exp, and
   injectivity radius back to the original metric.  Thus this route exposes at
   least two independent API frontiers.
3. **Localize the checked `CGTDecay` propagation proof.**  Its algebraic base
   volume shift and Bishop/CGT estimates are reusable, but its normal-coordinate
   input is globally packaged by `SeqBoundedGeometry` and completeness.  A
   bounded-ball version first needs a producer from padded compact-ball
   curvature jets to uniform local metric control/nonconjugacy/raw framed-exp
   local diffeomorphism; volume propagation then still needs Route 1's local
   Bishop/minimizing coverage.  It therefore cannot independently bypass the
   compact-tail frontier.

The smallest shared next theorem is the Route 1 local Hopf--Rinow producer,
with conclusion split into exp-domain coverage and `radialMinSet` coverage.
This is missing groundwork rather than a local coercion issue; no endpoint is
counted until it is formally stated and proved.

## P1c -- Laplacian comparison, Busemann functions, and splitting

P1c starts only after P1b closes or reaches a precisely recorded genuine
blocker.  The expected order is the weakest reusable Laplacian-comparison
producer, then Busemann, then the Cheeger--Gromoll splitting endpoint, adjusted
only if the exact P3 consumers give a shorter native route.  Missing distance
smoothness, cut-locus, barrier/weak-Laplacian, ray compactness, or Hessian-trace
infrastructure must be isolated as the smallest native bridge rather than
replaced by a parallel hierarchy.

### Running status (not started)

- Laplacian-comparison endpoint: **0%**.
- Busemann endpoint: **0%**.
- Cheeger--Gromoll splitting endpoint: **0%**.
- Dedicated native machinery: provisionally **5--15%** pending the asset audit.
- P1d boundary: record exact Toponogov assumptions consumed downstream; do not
  implement them in this campaign.

## Program accounting

- Final theorem `poincare_of_inputs`: **0%** (not declared).
- P1a theorem endpoints: **87.5%** (seven of eight); P1b: **0%** (zero of two);
  P1c endpoint counts remain 0% pending its exact consumer/asset audit.  Do not
  collapse these distinct denominators into a misleading single percentage.
- Whole P0--P9 program infrastructure: retain the global authority's current
  **15--25%** estimate; P1 audit or helper work must not inflate it.

## Dependency table

This table is filled from live source evidence during each phase.

| Phase | Morgan--Tian consumer | Exact assumptions/conclusion | Native producer | Classification | Verification/axioms |
|---|---|---|---|---|---|
| P1a | MT 1.34; 5.6; 8.10 | Complete/global metric; Ricci lower bound; compare two radii, then upper/lower volume bounds give packing | `segBall_vol_rel`, `segBall_vol_le`, `segBall_card` | checked producer | focused checks passed; direct axiom print has only standard logical axioms |
| P1a | MT 9.11, 9.59--9.63 | Complete; global `Ric >= 0`; power-law ratio and Euclidean absolute upper bound | `segBall_vol_pow`, `segBall_vol_le_euclidean` | checked producer plus thin zero-curvature adapter | focused/named-refresh checks passed; the common direct axiom audit reports only standard logical axioms |
| P1a | MT 5.9--5.11, 5.15 | Compact closure of the relevant ball and a Ricci bound only there; full-radius local ratio/packing | `localBall_ratio` covers only a small injectivity-radius interval under global completeness; `endpointCont_compact` and `geo_Ioo_extend_cpt` supply the compact-tail continuation brick | missing stronger producer | continuation bricks are focused/named-build green and axiom-clean; `radialMinSet` still lacks local minimizing coverage, and the segment-polar layer still depends on complete-only `expMapIntrinsic` |
| P1a | MT 9.66 | a sufficiently small radius has Euclidean-normalized volume within any prescribed relative error; no audited consumer needs a public abstract limit | `framedDens_zero`, `framedDens_haar`, `exists_ball_ratio`, `exists_euclid_ratio` | checked producer and endpoint | focused checks passed; both normalization theorems and the endpoint are axiom-clean |
| P1a | MT 9.66 | continuity in radius, used to choose a half-model-volume radius | `segBall_vol_cont` via polar integral, sphere-null, and dominated convergence | checked endpoint | focused/named-build verification passed; common axiom audit has only standard logical axioms |
| P1a | MT 9.56 | global strict positive sectional curvature makes every positive-radius intrinsic ball strictly smaller than its Euclidean comparison ball | checked bottom equality chain and radial propagation `transDens_eq_rigid`; checked general strict producers `expJac_lt_of_ricci` and `segBall_vol_lt`; checked smooth-manifold `normalHaar_eq`, `gBall_model_eucl`, `rm04_eq_inner_riem`, and sectional-to-Ricci bridges; exact wrapper `segBall_lt_of_sec` | checked endpoint | all dependencies and `SegmentBallEuclideanStrict` itself are warning-free focused/named-refresh green; common direct audit reports only `propext`, `Classical.choice`, and `Quot.sound` |
| P1b E1 | MT `volinj`; `basicconv`; `2ndmfdconv`; P3 `flowlimit` and the local `basicconv` use | Global `Ric >= 0` is available in every actual P3 use; a relevant larger ball has compact closure and a uniform local `|Rm|` bound; a smaller ball has `Vol >= epsilon*r^n`; conclude `inj(p) >= delta(n,epsilon)*r`. Ambient completeness cannot be required because of `temp2kappa:2668` | checked `intrInj_ge_cgt_on` and ambient-ball quantitative assembly `intrInj_ge_vol`; `flowInj_of_vol` realizes the stronger complete/global-bounded-geometry special case | missing exact local producer | all listed machinery is focused/named green and direct-axiom clean; exact raw exp-domain/local Hopf--Rinow and raw CGT bridges remain |
| P1b E2 | MT `mfdconv` proof, then P3 `flowlimit` | On each fixed bounded ball: compact closure and uniform curvature-derivative bounds; uniform positive base inj/noncollapse; conclude a uniform positive inj lower bound throughout that ball, allowing incomplete ambient manifolds | `injDecay_of_bg` gives an explicit exponential pointwise bound under complete global `SeqBoundedGeometry`; its proof actually reads only order-zero curvature, base injectivity, and the intrinsic complete-manifold normal-control package | conditional producer; exact local-on-balls adapter missing | source-complete global special case and all direct axiom prints are clean; exact E2 requires raw buffered normal/CGT control plus local Bishop coverage |
| P1c | not started | not started | asset audit pending | not yet audited | not yet audited |

## Status log

- 2026-08-27: plan created after confirming that the historical
  `VOLUME_COMPARISON_PLAN.md` is absent.  P1a consumer/native/axiom audits are
  starting; P1b and P1c remain intentionally undispatched.
- 2026-08-27: froze the P1a consumer table from Morgan--Tian Chapters 1, 5, 8,
  and 9.  Added and focused-checked `hypRadVol_zero`, `segBall_vol_pow`,
  `curve_cauchy_speed`, and `curve_lim_of_compact`.  The attempted framed
  density value-one normalization was rejected as false: the chart model basis
  is not generally orthonormal, so its positive determinant factor must be
  carried through the small-ball calculation.  P1b and P1c remain undispatched.
- 2026-08-27: audited three equality-rigidity routes and the local
  compact-closure route.  The local obstruction is not the already-built
  compact-tail limit theorem alone: current segment-polar definitions are tied
  to complete-only intrinsic geodesics.  Equality rigidity has a smaller common
  algebraic entry point at the equality case of `trace_sq_le_mul`; its geometric
  continuation is the equality-or-strict case of `mean_riccati_le`.
- 2026-08-27: focused/named-build/axiom verification passed for
  `framedDens_zero`, `framedDens_haar`, `endpointCont_of_lim`,
  `endpointCont_compact`, and `geo_Ioo_extend_cpt`.  `segBall_vol_cont` and
  `trace_sq_eq_iff` pass focused checks; their remaining export/axiom checks and
  the downstream `exists_euclid_ratio` check are serialized behind the shared
  B2 elaboration window.  Claims remain held during that coordination window.
- 2026-08-27: rechecked the exact MT 9.56/9.66 use.  No P2/P3 consumer requires
  a public abstract small-ball `Tendsto` theorem: 9.56 consumes the already
  checked finite-radius Euclidean upper bound, while 9.66 needs one small-radius
  lower bound (the epsilon endpoint) plus radius continuity and an intermediate
  value argument.  Also localized the incomplete-manifold route to
  `minExp_of_cptBall`, but recorded that it still needs a phase-lift/maximal-ray
  bridge and would not by itself remove `CompleteSpace` from segment-polar
  integration.
- 2026-08-27: official focused verification and direct axiom capture passed for
  `exists_ball_ratio` and `exists_euclid_ratio`; both use only the standard
  logical axioms.  This closes the fifth of eight P1a project-used endpoints.
- 2026-08-27: `segBall_vol_cont` passed focused and named-module verification
  after mechanical local style cleanup.  The common P1a audit then passed for
  all six checked volume endpoints and all three compact-tail bridges, with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Separately,
  `trace_sq_eq_iff`, `mean_sq_eq_iff`, and `mean_riccati_eq_iff` are checked and
  axiom-clean dedicated machinery; the final volume-rigidity endpoint remains
  unstated and therefore 0%.
- 2026-08-27: source-written but deliberately uncredited pending validation:
  radial equality propagation (`transDens_eq_rigid`), its strict-Jacobian
  contrapositive (`expJac_lt_of_ricci`), strict positive-Ricci model-volume
  comparison (`segBall_vol_lt`), and the low sectional-to-Ricci bridges.  Three
  focused passes on `SegmentPolar` exposed only local elaboration/coercion
  repairs.  A fifth focused pass and the explicit named refresh then succeeded
  (3980/3980), so `transDens_eq_rigid`, `segBall_vol_le_int`, and
  `gBall_model_int` are verified exported producers; direct axiom audit is
  still pending.  The exact next normalization brick is the pole-density/model-
  Haar pushforward identity `normalHaar_eq`; endpoint completion remains six of
  eight and dedicated machinery is about 95%.
- 2026-08-27: the first focused pass on `SegmentPolarRigidity` reported no
  error in `expJac_lt_of_ricci`; `segBall_vol_lt` initially had four local
  elaboration issues.  Three were discharged immediately.  The remaining
  open-set-positivity call did not consume either the inferred or explicitly
  installed parent instance in two further passes, so it has now been rewritten
  to call the existing additive-Haar instance's `open_pos` field directly.
  The fourth focused pass then completed warning-free, so both strict producers
  are locally verified.  Neither is yet credited as the final MT endpoint:
  the new module still needs a named refresh when its exports are consumed,
  direct axiom audit, and the separate Euclidean model-ball normalization.
- 2026-08-27: `normalHaar_eq` passed a warning-free focused check and its
  explicitly named `BishopPolarFramed` refresh (3905/3905).  The downstream
  `gBall_model_eucl` normalization has now been source-written without new
  Ricci, metric-realization, or dimension assumptions; it remains 0% as a
  checked theorem until its own focused verification.
- 2026-08-27: the new radial equality proof had raised `SegmentPolar.lean` to
  3034 lines, past the repository limit.  The declaration
  `transDens_eq_rigid` was therefore moved verbatim (statement, docstring,
  attribute wrapper, and proof unchanged) to the dedicated
  `SegmentPolarEquality.lean`; the base file is now 2883 lines.  The old
  location was green; the edited base then passed a warning-free focused check
  and named refresh (3980/3980), and the new equality module passed its own
  warning-free focused check and named refresh (3981/3981).  Direct axiom audit
  remains pending.
- 2026-08-27: the first focused pass on `gBall_model_eucl` reached the intended
  proof and exposed only local elaboration issues: two unqualified sphere
  names, zero-curvature `if True` simplification, ENNReal multiplication versus
  measure scalar action, an under-specified `normalHaar_eq` invocation, and a
  missing explicit `Nontrivial E` witness for the Haar closed/open ball lemma.
  These are being repaired statically; no named refresh was run.  The exact
  MT 9.56 wrapper `segBall_lt_of_sec` is source-written but remains a 0%
  endpoint pending all dependency checks, its own focused verification,
  refresh, and axiom audit.
- 2026-08-27: two subsequent focused passes on `gBall_model_eucl` reduced the
  local failures first to ENNReal scalar-action normalization and a manifold
  smoothness mismatch, then to the latter alone.  Source inspection showed that
  `omega` is the analytic outer top whereas `infinity` is the smooth grade, so
  `IsManifold.of_le` cannot manufacture the former from the latter.  The real
  issue was the overly strong global analytic binder in
  `BishopPolarFramed.lean`; it has been weakened to the smooth grade used by the
  framed normal-coordinate API, and the impossible consumer-side instance has
  been removed.  Both producer and consumer are source-written with unchanged
  public consumer assumptions, but remain unchecked after this correction.
- 2026-08-27: the first focused pass after the grade correction stopped at the
  producer binder because this file's open ENNReal scope parsed an unqualified
  infinity symbol as `ENNReal` rather than `WithTop ENat`.  The downstream
  diagnostics were all cascades from that first type mismatch.  A second pass
  showed that a result type ascription does not override scoped notation
  selection, so the binder now uses the notation-free coercion of the top ENat
  grade into `WithTop ENat`.  No refresh or consumer check was run, and the
  smooth-manifold generalization still awaits re-verification.
- 2026-08-27: the notation-free smooth-manifold `BishopPolarFramed` source then
  passed a warning-free focused check and its explicitly named refresh
  (3905/3905).  The downstream `gBall_model_eucl` proof elaborated completely;
  its only diagnostics are local unused-section-variable warnings for
  `T2Space M` and `SigmaCompactSpace M`.  Per project rules its refresh was not
  run; the theorem is being wrapped in the corresponding `omit` before a final
  focused recheck.
- 2026-08-27: after the declaration-local `omit` cleanup,
  `SegmentBallEuclideanUpper.lean` passed a warning-free focused check and its
  explicitly named refresh (3981/3981).  Thus `gBall_model_eucl` is now a
  checked producer, while the exact MT 9.56 theorem endpoint remains 0% until
  the curvature bridges and `segBall_lt_of_sec` itself are checked and
  axiom-audited.
- 2026-08-27: `CoordRm04Bridge.lean` passed a warning-free focused check and
  its explicitly named refresh (3746/3746).  The next `SectionalRicci` focused
  pass stopped at its file-level manifold binder because bare smooth-infinity
  notation was unavailable without the ContDiff scope; all subsequent errors
  were cascades.  Its binder is being replaced by the same notation-free smooth
  grade used above; no sectional refresh or rigidity check was run.
- 2026-08-27: after the binder correction, the next `SectionalRicci` pass
  reached the proof bodies and stopped only because `exists_perp_pos` was not
  in its import cone.  Its canonical home is the native
  `Comparison.Variation.PerpFrame` module, already used by the volume-comparison
  stack.  The file is gaining that single direct import; no sectional refresh
  or rigidity check was run.
- 2026-08-27: with the direct `PerpFrame` import, `SectionalRicci.lean` passed a
  warning-free focused check and its explicitly named refresh (3933/3933).
  `SegmentPolarRigidity.lean` then reached only two identical Euclidean-volume
  type mismatches: theorem-local `InnerProductSpace` creation had made
  `MeasureSpace.toMeasurableSpace` diverge from the earlier private borel
  instance.  The two Euclidean theorems are now in a narrow section that installs
  the inner-product instance before fresh local borel instances, matching the
  checked normalization module.  Public assumptions are unchanged; no rigidity
  refresh was run.
- 2026-08-27: the first Euclidean-section reordering still inherited the
  file-level private measurable instance, so the same two `volume` diamonds
  remained.  The corrected route now scopes the original borel instances to a
  `General` section containing only the non-Euclidean strict theorems; the
  disjoint `Euclidean` section installs `InnerProductSpace` before its sole
  fresh borel pair.  An explicit `@volume` route was rejected because the
  chosen inner-product measure instance still consumes the ambient measurable
  instance and exposes the same diamond.  The scoped route preserves every
  public assumption and awaits a focused recheck.
- 2026-08-27: the disjoint-scope route still produced the same two measure
  diamonds, so the third distinct route split the Euclidean adapters at their
  natural abstraction boundary.  `SegmentPolarRigidity.lean` now contains only
  `expJac_lt_of_ricci` and `segBall_vol_lt` (236 lines).  The unchanged
  `segBall_vol_lt_eucl` and exact `segBall_lt_of_sec` wrappers occur exactly once
  in the new 82-line `SegmentBallEuclideanStrict.lean`, whose global
  `InnerProductSpace` binder precedes its sole borel instance pair exactly as in
  the checked Euclidean Upper module.  The import graph is acyclic, public
  theorem statements are unchanged, and both modules await focused/named
  verification before the common axiom audit.
- 2026-08-27: the split resolved the instance diamond.
  `SegmentPolarRigidity.lean` passed a warning-free focused check and its
  explicitly named refresh (3982/3982).  `SegmentBallEuclideanStrict.lean`
  then elaborated both Euclidean wrappers successfully; its only diagnostic is
  an unused lambda binder at line 79.  Per the warning-clean acceptance rule no
  named refresh was run.  This is a routine static linter repair, not a theorem
  or API blocker; the strict endpoint remains formally 0% until the repaired
  module is warning-free, refreshed, and included in the direct axiom audit.
- 2026-08-27: after replacing the unused lambda binder by `_`,
  `SegmentBallEuclideanStrict.lean` passed a warning-free focused check and its
  explicitly named refresh (4045/4045).  Both exact Euclidean wrappers are now
  checked; the endpoint remains conservatively outside the completed count only
  until the common direct axiom audit runs.
- 2026-08-27: `P1AxiomCheck.lean` passed its expanded focused audit in 77.0s.
  All 20 printed endpoints and producer/continuation bridges, including
  `segBall_lt_of_sec`, depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.  P1a therefore closes at seven of eight project-used endpoints
  (87.5%).  The sole remaining theorem endpoint is the local compact-closure
  Bishop--Gromov form (0%); its three genuinely different attempted routes and
  exact missing groundwork are recorded above.  P1b may now start without
  reopening this blocker.
- 2026-08-27: all eight P1a file-claim tokens were released after the final
  static diff review.  P1b then started, in phase order, with three mutually
  exclusive read-only xhigh tasks: exact Morgan--Tian consumers, native
  producer/axiom coverage, and minimal adapter scouting.  No P1b Lean file is
  claimed or edited until the consumer and producer maps are merged.
- 2026-08-27: the frozen P1b source audit found two, and only two,
  comparison-geometry endpoints in the P2/P3 dependency closure: pointwise
  local volume-to-injectivity (`volinj`) and base-to-bounded-ball injectivity
  propagation.  P2 has no direct use.  Five P3 `flowlimit` applications and
  one `basicconv` application use curvature bounds separately on each fixed
  bounded ball.  The `temp2kappa:2668` application explicitly permits
  incomplete ambient flows, so the exact endpoints must use compact closure of
  the relevant balls rather than global completeness.  All actual P3 inputs do
  have global nonnegative curvature operator, hence global `Ric >= 0` is an
  honest common denominator-control hypothesis.
- 2026-08-27: `intrInj_ge_cgt_on` was added at the native CGT layer with the
  radial-local Rm bound already consumed by the Whitehead/propeller proof.  The
  old `intrInj_ge_cgt` signature and its two external P0 call sites remain
  unchanged as a compatibility theorem.  The file passed a warning-free
  focused check and explicitly named refresh (4061/4061).  This is dedicated
  machinery, not completion of E1; the next producer is the explicit
  volume-denominator assembly `intrInj_ge_vol`.
- 2026-08-27: the first focused pass for the source-written
  `intrInj_ge_vol` stopped before theorem elaboration because the new module
  declared `RiemannianBundle` before disabling the two competing tangent-space
  normed instances.  This produced a local inner-product/PseudoEMetricSpace
  instance cascade and terminal `whnf` heartbeat failures; no named refresh was
  run.  The static repair is to use the already checked `CGTInjectivity` header
  ordering.  The mathematical volume-denominator route is unchanged, and E1
  remains 0% until the exact compact-closure hypotheses are discharged.
- 2026-08-27: after that header-only repair, `CGTVolumeInjectivity.lean`
  passed a warning-free focused check (27.2s) and its explicitly named refresh
  (4072/4072).  `intrInj_ge_vol` is now checked dedicated machinery; it still
  does not close E1 because its complete ball-volume producer and explicit
  `hloc`/nonconjugacy premises are stronger than the incomplete compact-closure
  Morgan--Tian use.
- 2026-08-27: two smaller native bridges were then isolated.  The first
  Coordinates attempt incorrectly stated ambient membership in `Metric.ball`
  while assuming only `PseudoEMetricSpace`, and referred to an out-of-scope
  unqualified `riemannianEDist`; that focused check failed and no refresh or
  Jacobi check ran.  After restating it as `intrFrame_mem_eball` entirely at the
  `edist` layer, `IntrinsicFramedCoordinates.lean` passed warning-free focused
  verification (46.7s) and named refresh (3818/3818).  The derivative bridge
  `framedExp_not_conj` in `IntrinsicFramedJacobi.lean` then passed warning-free
  focused verification (22.8s) and named refresh (3831/3831).  These remove the
  metric-ball-to-radial and redundant-nonconjugacy adapter gaps; they do not
  provide incomplete-ambient compact-tail minimizing coverage.
- 2026-08-27: `intrInj_ge_vol` was then restated with the weaker ambient
  `Metric.eball` curvature input and with nonconjugacy generated internally
  from `hloc`; its explicit denominator and conclusion were unchanged.  The
  revised module passed warning-free focused verification (24.0s) and named
  refresh (4073/4073).  The expanded common axiom audit then passed in 103.5s:
  all 28 P1a/P1b declarations, including `injDecay_of_bg`,
  `injDecay_realizes`, and `flowInj_of_vol`, depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
