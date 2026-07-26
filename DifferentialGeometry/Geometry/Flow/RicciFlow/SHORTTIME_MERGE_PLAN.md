# SHORT-TIME-EXISTENCE MERGE + FORWARD PLAN (uniqueness, `extends_of_rmBounded`)

## 2026-07-13 completed alignment and latest-progress sync

The M-track described below is now complete on
`codex/short-time-existence-align`.  Merge commit `d842bedee` first aligned the
proved qinz short-time-existence tree with our progress through `e5d37bce6`.
The two later committed updates on our `short-time-existence` branch were then
merged on top:

- `17de115b1` (`B/C consult`);
- `2a2ce366e` (`123`).

That latest sync carried 75 source paths (40 added and 35 modified) and merged
without textual conflicts.  Nine Lean compatibility consumers were then
adapted to the merged non-reducible tensor API, with ten same-name notes
created or refreshed.  The changes use the public `Tensor0SSpace` evaluation
API; no theorem statement, new assumption, or endpoint wrapper was added.

Verification is complete:

- the previously paused `NormalBranchMin.lean` focused check passes, so
  `IsNormalDiag.halfSq_inf` and Gate 3 are verified;
- the latest spectral/Garding, conjugate-heat, and C4 Step-D targets complete
  all 9,364 jobs;
- the explicit Hamilton consumer completes all 9,924 jobs;
- the default full build completes all 10,258 jobs, and the declaration index
  contains 24,615 declarations;
- The merge-time `#print axioms` report showed only
  `[propext, Classical.choice, Quot.sound]`; this must be rerun against freshly
  rebuilt post-merge artifacts because the live source has a pointwise
  local-Weyl `sorry` documented as part of the dependency closure.

Strict current accounting: the Hamilton `IsSolutionOn` adapter bodies are
100% implemented, while the unconditional short-time-existence theorem is 0%
until the fresh axiom audit excludes `sorryAx` or the local-Weyl dependency is
removed. Its dedicated construction machinery is otherwise highly integrated.
This does not complete the downstream HCG endpoints: the
conditional compactness endpoint and textbook B1 theorem remain 0%; the whole
HCG machinery estimate was about 51% in this 2026-07-13 snapshot.  Current
whole-program accounting is maintained in `HCGCompactness/PROJECT_MAP.md`.

The two uncommitted planning edits in the primary worktree were deliberately
not copied into this merge.  They describe an earlier pre-merge state in part
and remain user-owned worktree changes for a separate reconciliation.

2026-07-11.  Written at the decision to merge `qinz1yang/differential-geometry`
branch `short-time-existence` (fetched as remote `qinz`/`upstream`) into ours.
All facts below were verified against the fetched ref, not the GitHub UI.

## §0 What the fork proved (verified from the ref)

**Headline** `ricci_flow_short_time_existence`
(`Geometry/Flow/RicciFlow/ShortTimeExistence.lean`, their HEAD `9c01f29f`):
for a compact boundaryless `M` with smooth metric `g₀`: `∃ T > 0` and a family
`g_fam : ℝ → SmoothRiemannianMetric I M` with
- `g_fam 0 = g₀`;
- chart-Gram entries jointly `C^∞` on `Ico 0 T ×ˢ (chart baseSet)` — i.e.
  **joint smoothness up to and including `t = 0`** (strengthened form, their
  commit `d8782e10`);
- the Ricci-flow equation `∂ₜ g = −2 Ric` as `HasDerivWithinAt … (Ici 0) t` for
  every `t ∈ Ico 0 T` (one-sided at `0` included).

Proof spine: DeTurck gauge (`deTurckRicci_solution_with_jointReg`) → chart
regularity → conjugating-flow de-gauging (Seeley time extension of the DeTurck
vector-field flows, joint smoothness on an open interval ⊇ the closed window).
Axiom audit is baked at the declaration site (their `9d30f5ce`):
`[propext, Classical.choice, Quot.sound]`, and their HEAD claims the full
library builds green with the only remaining sorries being two deliberate de
Rham sorries in `Tensor/Exterior`.  Their engine inventory (all new since the
merge-base): quasilinear parabolic maximal-regularity, Galerkin/Picard +
per-mode Duhamel limits, Nemytskii operators on Sobolev scales, correction-field
envelope towers, a vendored De Giorgi–Nash–Moser development, ODE-flow
`C^k`/variational regularity, Seeley extension.

**What the fork does NOT have:** Ricci-flow-level **uniqueness** (only ODE-flow
uniqueness); any blow-up/extension criterion; our post-base geometry (their
HEAD `9c01f29f` in fact *deleted* their stale unfinished copies of Hopf–Rinow /
exp-smoothness / minimizing-geodesic developments — the proven versions live on
OUR branch).  Their README's new work-in-progress target is Hamilton 1982
(= our `ham3_main`): the two forks have converged on the same program.

## §1 Merge geometry (verified numbers)

- merge-base `987a57b4`; ours `e5d37bce` = **237 commits / 986 files** ahead;
  theirs `9c01f29f` = **1244 commits / 1557 files** ahead.
- **Both-modified files: 106** (the conflict surface).  Mostly: the root
  aggregate `DifferentialGeometry.lean`, `Analysis/Calculus/SmoothExtension/*`
  (both sides extended Seeley/Borel), `Analysis/ODE/Flow/*`, a few
  `ConnectionLaplacian`/`Green` files.
- **Delete(theirs)/modify(ours) conflicts: 15** incl.
  `Comparison/BonnetMyers/Headlines.lean` and the old `ShortTime/*` cluster.
- They touched **28 files under our `Geometry/Comparison`/`HCGCompactness`**
  (all base-era shared files: `GeodesicConvexity`, `EndpointContinuation`,
  `BonnetMyers/*`, `ChartVelocityConvergence`…), where our branch is far ahead.
- Their comment-strip commit makes textual conflicts likely wherever both sides
  touched a file, even when semantically compatible.

## §2 Merge strategy (M-track)

- **M0 (before merging anything):** commit our working tree (weeks of verified
  work are still uncommitted), and record baseline `lake build` green on both
  sides (theirs claims green at `9c01f29f`; ours per `PROJECT_MAP.md` §7).
- **M1 resolution policy — by lane ownership:**
  - THEIRS wins: `Analysis/{Parabolic,Spectral,PDE}`-side, `Analysis/ODE/*`,
    `ShortTimeFlow/*`, `ShortTimeExistence.lean`, the vendored DGNM tree, and
    their deletions *inside their own ShortTime cluster* (the old base-era
    files; our edits there were maintenance, not content — audit each of the
    15 delete/modify cases, expected resolution: accept deletion for their-lane
    files, keep ours for `Comparison/BonnetMyers/Headlines.lean`).
  - OURS wins: `Geometry/Comparison/*` (post-base rewrites: Hopf–Rinow chain,
    exp smoothness, CenterOfMass, HalfSqDistGrad…), `HCGCompactness/*` (whole
    tree), `Geometry/Topology/*` (DirectLimit*), `Geometry/Exponential/*`,
    `Evolution/*`, `Coordinates/LocalDiffeoIFT`.
  - REGENERATE: the root `DifferentialGeometry.lean` aggregate = union of both
    leaf-module lists (theirs was regenerated to ~1600 modules; ours added the
    HCG/C4/Topology modules).
  - Comment-strip noise: accept their stripped text in their lane; do NOT
    mass-restore docstrings there (cost accepted); our lane keeps our
    docstring conventions.
- **M2:** post-merge full `lake build`; re-run the axiom audit on BOTH
  headlines (`ricci_flow_short_time_existence`; our endpoint chain per
  `PROJECT_MAP.md` §7) — the false-green lesson applies doubly after a merge.
- **M3:** update `PROJECT_MAP.md` (§2 add the short-time endpoint as DONE-lane,
  §3 add the U/E lanes below), `CODEX_HANDOFF.md`, and `HAM3_BLACKBOX_PLAN.md`
  (frontier 1 = short-time: DONE by the merge).

## §3 Forward plan A — U-track: Ricci-flow forward uniqueness

Target = discharge **black box (B)** `ricci_flow_forward_unique`
(`Evolution/ExtendViaUniqueness.lean` ~L165): forward uniqueness of smooth
Ricci flows on closed `M` with the joint-regularity hypotheses (GSM77 Ch. 7
§5.2 route).  Keep the STATEMENT exactly as the consumer already cites it.

- **U1 — Ricci–DeTurck uniqueness** (the parabolic half).  First AUDIT their
  fixed-point layer: a Banach/Galerkin contraction usually yields
  uniqueness-in-the-ball for free — check whether
  `deTurckRicci_solution_with_jointReg`'s underlying operator has an
  extractable "any two solutions with the same data agree on a short window"
  clause; if yes, U1 is extraction + a continuation argument (cover `[0,T)` by
  short windows), not new analysis.  Fallback route: energy/Gronwall on the
  difference of two Ricci–DeTurck solutions (linearize; their maximal-regularity
  + Gronwall machinery suffices; no new estimates beyond what existence used).
- **U2 — de-gauging uniqueness** (the ODE half).  Two Ricci flows with equal
  initial data DeTurck-ize (harmonic-map heat flow = their conjugating-flow
  layer) to two Ricci–DeTurck solutions with equal data ⟹ equal by U1; the
  conjugating diffeomorphisms then solve the same time-dependent ODE with the
  same initial value ⟹ equal by their ODE-flow uniqueness; undo the gauge.
  All three ingredients exist in their tree post-merge; the work is the
  manifold-level bookkeeping (same shape as their existing de-gauging proof,
  run in reverse).
- **U3 — assemble** `ricci_flow_forward_unique` and DELETE the black-box status
  (per the discharge rule: replace downstream citations, no wrapper left).
- Sequencing: U1-audit is the first session (cheap, decides the route).  U-track
  is independent of the E-track's E1 and can run in parallel post-merge.

## §4 Forward plan B — E-track: `extends_of_rmBounded`

Goal: the extension theorem (|Rm| bounded on `[0,ω)` ⟹ the flow extends past
`ω`) — our `Evolution/` lane, ham3 frontiers 2–3.  The faithful decomposition
already in `ExtendViaUniqueness.lean`:

- **E1 — discharge black box (N)** `ricci_flow_unif_existence` (the ONE sorry
  in that file, ~L92).  Statement = **uniform** short-time existence: for fixed
  `gBase` there is a chart family `S`; for every `Λ ≥ 1` a uniform
  `τ₀(gBase, Λ, S) > 0` such that every `Λ`-comparable `g₀` with order-`≤3`
  chart-Gram bounds flows for time `≥ τ₀`.  **The fork's headline is per-metric
  (`∃T` for each `g₀`) — NOT directly sufficient.**  But their DeTurck
  fixed-point existence time depends only on ellipticity + data bounds, so the
  uniform version is extractable from their ENGINE: re-run
  `deTurckRicci_solution_with_jointReg`'s construction with the
  `(Λ, S)`-uniform hypotheses threaded through the contraction radius/time
  choice, or strengthen their headline to a `τ₀(Λ)`-quantified variant in
  their lane.  This is the main post-merge engineering item of the E-track;
  audit their proof's time-choice locus first (where `T_DT` is fixed) —
  that single lemma's hypotheses tell us the exact uniform-data form.
- **E2 — the restart wiring** `ricci_flow_interior_restart` (provable from
  (N); the route is already written in its docstring: choose `t_star` with
  `ω < t_star + τ₀`, apply (N) at `g₀ := g_fam t_star`).  Its two tail-bound
  hypotheses (`hell` uniform ellipticity, `hC3` chart-Gram C³ tail bounds) come
  from `|Rm| ≤ C` via Gronwall metric-equivalence + Shi (our Lemma-3.11/BBS
  machinery — Gate-L `C^∞`-up-to-`ω` is the remaining producer on OUR side).
- **E3 — glue** the restarted flow to the original by U-track uniqueness on the
  overlap `[t_star, ω)` (the seam-dissolving step the file is named for), then
  assemble `extends_of_rmBounded`.
- **E4 — consumers:** `MaximalTime` (one call-site), the hglue Gate-R (their
  DeTurck closed-endpoint work supersedes it — audit and retire), ham3
  frontiers 2–3, and the `MetricFamilySmoothOn ⊤→∞` cascade (currently HELD —
  re-audit after the merge since their lane reworked the smoothness plumbing).
  NOTE: 3.9/3.10's `hShi` remains a CITED hypothesis — `extends_of_rmBounded`
  does not reopen it.

## 2026-07-14 post-merge live audit

The merge changed the short-time headline but did not close either quantitative
continuation input.

- The live short-time tree has one theorem-body `sorry`, in
  `WeylEigenvalueCountingBound.lean`. Its statement combines a generic
  pointwise counting bound with a sharp point-evaluation summability threshold.
  Existing proved Mercer/Weyl machinery is non-sharp. The actual
  `InteriorAllscaleTimeContinuity` consumer only needs `(0,2)`
  eigenvalue-tail summability and has been rewired to the proved
  `tensorEigen_summable_negpow` producer; focused verification and the fresh
  headline axiom probe are pending the active Spectral artifact rebuild.

- The fixed-point layer does contain `quasilinear_strong_unique`, but it only
  compares two forcing-space fixed points for the same background Sobolev
  problem. `deTurckRicci_solution_with_jointReg` exports a geometric solution
  and joint chart-Gram regularity, while dropping the forcing-space witness;
  there is no reverse theorem identifying an arbitrary smooth geometric
  Ricci--DeTurck solution with such a fixed point.
- The tree contains the DeTurck-to-Ricci conjugating flow used for short-time
  existence. It does not contain the harmonic-map heat-flow construction needed
  to send an arbitrary Ricci flow back to Ricci--DeTurck gauge. Consequently the
  current U1/U2 route is a real analytic frontier, not local bookkeeping.
- The explicit existence time in
  `quasilinear_maxreg_solution_of_nemytskii` depends on the mixed constants
  `C1`, `C2`, and the high-Sobolev norm `‖Nfun 0‖`, at Sobolev order
  `a = 4 * finrank E + 10`. For `g_bg = g0`, `Nfun 0` contains
  `-2 Ric(g0)` and is not zero. Exact fixed-background metric derivative bounds
  only through order three do not uniformly control this high-Sobolev norm.
  Thus the merged high-Sobolev engine cannot by itself prove the present
  C3-uniform statement by merely exposing its time choice.

Smallest honest E1 producer: a quantitative low-regularity Ricci--DeTurck
short-time theorem, based at fixed `gBase`, whose positive time depends only on
`Lambda`-ellipticity and the order-at-most-three metric bounds and whose output
recovers the current joint regularity fields. The alternative is to strengthen
the restart inputs to enough all-order bounds and build uniform metric-varying
Sobolev comparison estimates; that changes the route and is not a thin adapter.

### 2026-07-14 low-regularity input progress

The sorry-free quantitative coefficient chain is now verified:

- `nemytskii_sol_const` exposes the existing maximal-regularity fixed-point
  lifetime using explicit mixed constants `C1`, `C2` and an explicit budget
  `D >= norm (Nfun 0)`.  The old existential-choice theorem is unchanged as a
  compatibility entrypoint.
- `chartGram_of_orders` converts an arbitrary family's exact-order
  `MetricCovDerivOrderBoundOn` hypotheses through order `r` into a uniform
  order-`r` `iteratedFDeriv` bound for every chart Gram component on a compact
  chart piece.  Its `r = 3` specialization supplies the C3 coefficient bridge
  required by E1.  `chartGram_pou_le` takes a finite nonnegative aggregate over
  `chartAtlasPOU_finset`, giving one bound for every active chart support.
- `chartInvGram_unif_lb` converts pointwise `Lambda`-equivalence to `gBase`
  into one positive inverse-Gram Rayleigh lower bound for the whole metric
  family on each fixed compact chart piece.  `chartInvGram_pou_lb` takes the
  positive finite minimum over the same active chart set.  This supplies the
  quantitative uniform-parabolicity half of the low-regularity coefficient
  package.
- `chartGram_pou_bnd` and `chartGram_pou_d1/d2/d3` turn the intrinsic family
  bounds into absolute coordinate Gram bounds through order three on every
  active chart support.  The two-sided `chartInvGram_pou_eqv` envelope and the
  inverse-Gram/Christoffel perturbation producers supply the corresponding
  principal and lower-order coefficients.
- `chartRicci_pou_lip` and `chartLie_pou_lip` combine in
  `chartRHS_pou_lip`, giving one constant that controls the Ricci--DeTurck RHS
  value difference by the metric `2`-jet difference for the whole family.
- `chartRHS_pou_bnd` gives one positive absolute RHS component bound for the
  whole family.  This supplies the chart-level input to a forcing-size budget;
  a Lipschitz modulus alone did not supply it.  A uniform realization of that
  component bound in the spectral `H1` norm used for `norm (Nfun 0)`, including
  the cross-metric norm comparison, is still missing downstream.
- `LowRegCoeff`, `IsLowRegCoeff`, and `exists_low_reg_coeff` package all of
  those facts directly from the E1 hypotheses.  Focused and targeted
  verification pass; the headline package and RHS theorem are axiom-clean.

These do not close E1.  The current spectral nonlinearity still requires high
Sobolev order and the joint-smooth realization chooses a further positive
subinterval without a uniform lower bound.  The smallest remaining frontier
inside the dimension-three specialization is the mixed tame estimate
realizing the
Ricci--DeTurck nonlinearity as `H^3 -> H^1` at maximal-regularity order `a = 1`,
with constants controlled by `LowRegCoeff`.  Its top path arm is now verified:
`LowRegPathSplit.phi_dev_h2`, `top_path_dev_h2`, and `top_path_ball_h1` give the
small principal-coefficient estimate from a three-dimensional spectral `H2`
ball.  `rem_h0_lip` also remains verified.  The exact mixed theorem is still
  unstated and therefore 0%.  The approximately 70% machinery estimate was a
  2026-07-15 snapshot and is superseded by the 2026-07-18 route ruling below.
This specialization cannot by itself prove the dimension-generic public
endpoint; that still needs a quantitative Schauder/`W2p` route or another
dimension-adaptive low-order solver.

### 2026-07-16 route-A execution

The design frontier is settled in favor of extraction into small public
modules. `RHSThreeArmCancel.rhsSlope_eq_arms` proves the exact complete
Ricci+DeTurck three-arm cancellation before norms, and
`RHSPathIntegral.rhsArm_sub_eq_paths` integrates it into concrete C0, C1, and
top path coefficients. Both the exact cancellation and integrated identity are
sorry-free and need no high-`a` assumption. The generic gradient-slot Ricci
commutator was also extracted as `GradSlotCurvature.gradSlot_sub_eq_curv`.

At the 2026-07-16 checkpoint, `LowRegPathSplit` consumed
`rhsTopPathIntegral` and the public top-path joint-smoothness theorem, so its
source import chain no longer reached the oversized high-order remainder file.
Final downstream verification was then waiting on an unrelated in-flight
failure in `Geometry/Operator/Operators.lean`.  That verification blocker is
historical: the 2026-07-18 repair and named target refresh below supersede it.
The proposed uniform pointwise `LowRegCoeff` frontier is likewise superseded by
the residual cometric-variation ruling and integral-product route below.

This was the route proposed on 2026-07-16.  The 2026-07-18 execution record
below identifies the residual cometric-variation obstruction in its zero-order
C0 term and replaces the pointwise argument by the integral-product route.

The exact mixed theorem remains unstated and therefore theorem-level 0%.  The
approximately 78% machinery estimate was the 2026-07-16 snapshot and is
superseded by the 2026-07-18 route ruling below. A coarse appeal to `rhs_h1_lip`
remains inadmissible because it leaves a nonsmall coefficient on the `H3`
difference.

This route is conditional on `finrank E = 3`; completing it would settle a
useful specialization, not the unchanged generic endpoint.

Within that specialization, after the mixed estimate come the actual
low-regularity solver and a
regularization statement valid on the same uniform interval.  E1 and
`ricci_flow_unif_existence` remain theorem-level 0%.  The roughly 42% E1
machinery figure was a 2026-07-16 historical estimate, not a current endpoint
percentage.  The solver must quantify the admissible metric family once and
produce one `tau > 0` such that every member has both an
`IsQuasilinearMetricParabolicSolution` and `JointChartGramSmooth` on that same
`tau`; a later metric-dependent shrink does not prove the uniform statement.

After the missing initial-edge estimate, the smallest honest uniqueness
producer is
harmonic-map heat-flow existence for a smooth Ricci flow relative to a fixed
background, together with the gauge identity and a reverse strong-solution
realization theorem feeding
`quasilinear_strong_unique`. This is likewise substantial new analysis.

### 2026-07-18 analytic-producer execution and route ruling

The exact public endpoints remain theorem-level 0%:
`ricci_flow_unif_existence` and `ricci_flow_forward_unique` still have their
original statements and proof holes.  No replacement hypothesis, axiom, or
opaque producer was introduced.  The statements are still expected to be
mathematically true; the rulings below concern the available formal routes.

For uniform existence, three genuinely different routes were audited to their
first unavoidable obstruction and ruled out with the current formal API.

1. The checked high-Sobolev maximal-regularity route gives a lifetime depending
   on mixed constants and `norm (Nfun 0)` at order
   `4 * finrank E + 10`.  The endpoint's uniform ellipticity and covariant
   metric bounds only through order three do not control those quantities, so
   this route cannot choose the required family-wide `tau`.
2. The intended dimension-three `H3 -> H1` route has a sound small top arm and
   a fully checked conditional assembly theorem `rem_h1_of_bounds` (named
   target build and warning-free focused check pass), but its current
   lower-arm interface is too strong.  It asks for a pointwise bound on
   `rhsLow0PathIntegral`.  The raw Ricci second-derivative terms partially
   cancel with the DeTurck terms, but the complete normal form retains the
   generically nonzero arm
   `D(g^-1)[U] * nabla^2 g = -(g^-1 U g^-1) * nabla^2 g`.
   With a fixed compactly supported chart bump and
   `bump_n(x) = n^(-3/2) phi(n * (x - x0)) K`, take
   `T'_n = bump_n` and `T_n = P0 + bump_n` for fixed small `P0`.  Both endpoints
   stay `H2`-small and `H3`-bounded, their fixed difference is `P0`, and the
   coefficient is unbounded in `C0`.  Thus the requested pointwise bound is false
   on the candidate ball.  The faithful replacement is an intrinsic tensor
   `H1 -> L6` theorem, an `appCc` product estimate
   `H1 x H2 -> H1`, and a lower-path consumer using `H1` control for the
   zero-order coefficient and `H2` control for the first-order coefficient.
   Its differentiated product uses `H2 -> L-infinity`, `H1 -> L6`, and
   finite-volume `L6 -> L3` for the separate factors.  The scalar Sobolev and
   component estimates exist, but public finite-component
   reconstruction is currently only available in `L2`.  Even after that layer,
   this route is dimension-three only, while the endpoint is generic in
   `finrank E`; it also still needs family-uniform mixed constants, comparison
   between the `gBase` and `g0` spectral norms, a uniform spectral-`H1`
   realization of the existing chart-level RHS bound as `norm (Nfun 0)`, and
   smoothing on the same selected horizon.
3. A dimension-generic Schauder or `W2p` proof would faithfully use the stated
   `C3` family data, but the repository has no corresponding quasilinear
   parabolic existence and regularization engine.  This is foundational
   analytic infrastructure, not an adapter around the current Hilbert solver.

The smallest useful existence producer is therefore the dimension-three
tensor `H1 -> L6` bridge (then `appCc_h1_h2_h1`), but it is only the next
machinery lemma, not a proof of the unchanged generic endpoint.  A complete
endpoint route must additionally supply either a dimension-generic low-order
solver or a Schauder/`W2p` engine, plus uniform-family norm comparison and
horizon-preserving smoothing.

For smooth forward uniqueness, three different routes were likewise audited
to their first unavoidable obstruction and ruled out with the current formal
API before the geometric endpoint.

1. The harmonic-map DeTurck ladder is missing short-time harmonic-map heat-flow
   existence for an arbitrary Ricci flow, diffeomorphism regularity, and the
   gauge PDE identity.  The existing ODE-flow uniqueness can be reused only
   after this common gauge has been constructed.
2. A direct Kotschwar-style metric/connection/curvature energy proof has some
   algebraic connection and curvature difference identities available, but no
   coupled evolution inequalities, closed energy estimate, or boundary-time
   regularization theorem for the endpoint's merely `C0`-at-initial-time class.
   In particular the available hypotheses have not been bridged to uniform
   fixed-background first-derivative and parabolically weighted second-derivative
   bounds near the initial time.
3. The checked maximal-regularity uniqueness theorem compares two fixed points
   of one truncated forcing map.  There is no reverse theorem taking an
   arbitrary geometric Ricci--DeTurck solution to that Duhamel representation;
   a fixed-coordinate attack on Ricci flow itself retains the diffeomorphism
   kernel and therefore does not avoid the gauge construction.

The smallest next uniqueness lemma is an initial-edge estimate
`ricci_edge_bounds`: on a common short window it should derive metric
equivalence, an order-one fixed-background covariant bound, and a
`sqrt (t-a)`-weighted order-two bound from the exact endpoint hypotheses.  The
next consumer-shaped producers are a short-window harmonic map heat flow and
gauge identity (for example `hmHeatShort` followed by `ricciGaugeShort`),
together with either local Ricci--DeTurck energy uniqueness or the missing
PDE-to-Duhamel realization.  A separate faithful alternative is
an identity-gauge uniqueness theorem for regularizing Ricci flows from a smooth
`C0` initial metric; that rough-flow infrastructure is also absent.  Local
uniqueness must then be continued across the whole common interval and the
gauge undone.

Consequently `extends_of_rmBounded` still depends directly on both unproved
analytic endpoints.  Its consumer/gluing construction remains checked, but
neither it nor the downstream maximal-time blow-up package is axiom-clean of
these two `sorryAx` dependencies.  The HCG compactness lanes remain independent
and can progress, while the unconditional Hamilton positive-Ricci endpoint
remains theorem-level 0%.

## §5 Risks / open questions

1. The merged high-Sobolev engine cannot be uniformized from C3 data by merely
   exposing its time choice: its zero-forcing norm and mixed constants live at
   order `4 * finrank E + 10`.  The generic E1 endpoint therefore needs a
   dimension-generic low-order or Schauder/`W2p` solver; the current
   dimension-three lane is only a specialization.  Do not revive the old
   "re-run the same contraction"
   fallback without strengthening the restart hypotheses.
2. Merge scale: 106 both-modified + 15 delete/modify + comment-strip noise;
   budget a dedicated merge session with the M1 policy table in hand, and
   expect the root-aggregate regeneration to be the last step before M2.
3. Their tree retains two de Rham sorries (`Tensor/Exterior`) — confirm they
   are off both headline closures post-merge.
4. Program-level: both forks now target Hamilton 1982; after M3, ham3
   frontier 1 is DONE (their short-time), frontiers 2–3 are the E-track, and
   the HCG lanes (PROJECT_MAP) continue unchanged as `ham3_cgh_limit`'s
   producer.
