# Noncollapsing

## 2026-07-09 canonical geometry refactor

`FlowMetricBall S t` is now the canonical ball object.  The time is a
`RealTimeInterval.FlowTime`, and the structure stores only a center and positive
radius.  Its carrier `setAt`, distinguished-time `set`, Riemannian `volume`,
backward-parabolic `IsRmControlled`, and model-dimensional
`IsKappaNoncollapsed` predicates are all derived from the actual solution
metric and canonical `rm04` tensor.

`Nested` is genuine same-time set inclusion, so `volume_mono` follows from
measure monotonicity.  The carrier has the same intrinsic-distance shape as the
existing `smallNormalBall`; a future `Metric.ball` adapter belongs in the
comparison/HCG layer rather than this low Perelman layer.

The zero-callsite `ScaleControlledBall` hierarchy and generic
`hypothesis -> conclusion` proposition aliases were deleted after final audit;
they could otherwise serve as a fake-geometric bypass despite a legacy label.
Hamilton Section 12 has migrated: `ham3RescaledBall` is a genuine
`FlowMetricBall` for the actual `paraSolution`, and `Ham3Noncollapse` uses its
`IsRmControlled` and `IsKappaNoncollapsed` predicates.

Verification passed.  The Hamilton rescaled-source realization and its
`ham3_rm_control` theorem are checked.  The genuine remaining theorem is
Perelman's no-local-collapsing producer (`ham3_noncollapse` remains 0%); further
volume/ball scaling lemmas belong below that producer rather than in a fake
numeric-volume wrapper.

## 2026-07-09 W-route start

`Entropy/ConjugateHeat.lean` now checks the local and interval forms of total
mass conservation for smooth solutions of `∂ₜu = -Δu + Ru`.  This is the first
new analytic producer on the Perelman route.  The moving-metric conjugate-heat
existence theorem remains 0%.

The checked supporting chain now also contains the interval-local
`IsHeatPotOn` / `IsConjHeatOn` interfaces and time reversal,
`heat_pot_nonneg`, the time-operator lift, the abstract
`nonaut_strong_exists` fixed-point theorem, and the local moving-volume
first-variation theorem `first_var_local`.  The scalar Laplacian bridge now has
a successful targeted build.  The genuine short-time non-autonomous inputs are
also complete: `lapDiffA20_short` supplies the support-independent moving
Laplacian difference `A2`, while `conjA1_short` supplies the scalar-curvature
potential `A1`.  `conj_strong_exists` completes their specialized spectral
strong-solution assembly.  The strong-to-classical regularity bridge remains
open.

The geometric scale-transfer lane is now complete.  The canonical volume law
is in `Analysis/Integration/Measure/Scaling.lean`; `Metric/DistanceScaling.lean`
proves distance and ball-carrier scaling and is used directly by `setAt`;
`ScaleTransfer.lean` proves two-way transfer of ball carriers, volume,
`IsRmControlled`, `IsKappaNoncollapsed`, the below-scale predicate, and
`NoLocalCollapsing`.  Hamilton's checked `ham3_noncollapse_of` now reduces the
fixed rescaled-ball conclusion to a genuine original-flow
`NoLocalCollapsing` producer.

Consequently the scale-transfer sublane is 100%, but the analytic
no-local-collapsing theorem and `ham3_noncollapse` remain theorem-level 0%.
Dedicated analytic machinery is about 32%; whole HCG machinery remains about
45% with endpoint theorems at 0%.

## 2026-07-13 scalar weak equation

The Pro-consulted selector-free route has now completed its first three
interfaces: the applied A2 graph closure, the exact A1 scalar graph test, and
`Entropy.conj_weak_ae`, which threads both into the actual maximal-regularity
solution almost everywhere in time.  This is real geometric weak-equation
machinery; it is not the classical moving conjugate-heat theorem and does not
prove noncollapsing.

The precise next analytic frontier is a genuine second-order non-autonomous
interior bootstrap for this scalar weak equation.  The existing first-order
`solField_into_all_tensorHs_interior` theorem cannot absorb A2's two-derivative
loss.  After that bootstrap, joint spacetime smooth reconstruction and the
pointwise derivative bridge remain before `IsHeatPotOn` can be produced.

The smallest first producer is `scalar_crit_tame` in the low Gårding layer: at
every Sobolev order it must split the moving scalar operator into a uniformly
small two-derivative principal arm and an order-dependent one-derivative
remainder.  Existing DeTurck critical-tame/Galerkin theorems are `(0,2)`-tensor
specializations and cannot be called directly.  This is a substantial analytic
producer, not a local elaboration or typeclass gap, and no assumption-shaped
wrapper was added around it.

Honest accounting: `heatpot_of_maxreg` is still unstated/unproved (0%) with
about 30% dedicated reusable machinery; the classical moving conjugate-heat
theorem remains 0% with about 75% dedicated machinery; Perelman
no-local-collapsing and `ham3_noncollapse` remain 0% with about 34% dedicated
analytic machinery.  Whole HCG machinery remains about 45%, with its endpoint
theorems at 0%.

## 2026-07-13 second-order bootstrap stop

The invariant scalar coefficient decomposition has advanced: the moving
cometric trace and traced connection-difference are now genuine fixed-tag
`SmoothCcTensor` fields with fully applied scalar read-off theorems.  Generic
`appCc` jet control, rank-generic spectral-to-jet and jet-to-spectral bounds,
and rank-generic Galerkin energy infrastructure are also checked producers.
This is machinery progress only; `scalar_crit_tame`, `heatpot_of_maxreg`, and
the no-local-collapsing endpoint remain 0% as theorems.

The bootstrap audit has now reached five genuinely distinct failed routes:

1. the existing interior theorem loses only one derivative;
2. the pre-refactor DeTurck critical tame was tied to `(0,2)` and a special
   resolvent-iterate family;
3. fixed-background Gårding alone did not isolate the small moving principal
   coefficient;
4. the base `H2 -> H0` bound and weak equation do not commute a moving operator
   through Galerkin projection at high order;
5. the new coefficient-jet route closes each fixed order with a top constant
   `A(k)`, but the live Galerkin consumer requires one coefficient below `2`
   for all orders simultaneously.

The fifth problem is the current analytic stop frontier.  The next consultation
should choose a direct energy/commutator normal form in which only order-zero
ellipticity enters the top term, or another bootstrap that proves all orders on
one fixed shorter interval.  A fixed-order tame theorem alone must not be wired
to the existing all-order consumer.

There is also a shared-worktree verification conflict: the new public
`metricCcTensor_apply` source checks, but its object-file refresh is blocked by
an independently claimed upstream curvature file with a parse error.  That
lane was not modified or force-released here.

Honest accounting: Perelman no-local-collapsing and `ham3_noncollapse` remain
0%; their dedicated analytic machinery is about 40%.  The classical moving
conjugate-heat theorem remains 0% with about 77% dedicated machinery;
`heatpot_of_maxreg` remains 0% with about 35% directly reusable machinery; whole
HCG machinery remains about 53%, with its endpoints at 0%.

## 2026-07-13 direct dissipation consult

The completed Pro consultation is recorded at
<https://chatgpt.com/g/g-p-6a05f8e7fb0881918ae46beec6dcd123-lean-pro-consult-handoff/c/6a55679f-4250-83e8-9f44-f3b67243e7ff>.
It explicitly searched the GitHub page for
`liao9yuan/differential-geometry`, branch `short-time-existence`.  The public
non-autonomous engine was available there, while the post-merge DeTurck,
pairing, and commutator files were not; the latter were verified only against
the live post-merge worktree.

The consultation corrected its initial commutator claim.  The raw operator
`[1 - Delta, A^{ij} nabla_i nabla_j]` has a third-order
`(nabla A) * nabla^3 u` term.  The direct route closes only after converting
the scalar principal arm to divergence form and treating the commutator as a
balanced bilinear expression of total odd order.  This rules out starting with
a one-step pointwise commutator theorem.

The chosen chain is now exact:

1. prove the coefficient-to-flux identity and `scalar_flux_split`;
2. prove `cc_principal_pair` with the order-zero metric smallness as the only
   top coefficient;
3. prove the support-independent balanced estimate `cc_comm_pair`;
4. assemble `cc_energy_diss`, using the generic coefficient-one Dirichlet gap
   only at the final step;
5. feed that dissipation into the second-order bootstrap, then joint smooth
   reconstruction and the classical heat-potential interface.

The lower-layer `appCc_assoc` producer and the generic `covDiv_appCc` rule are
focused-verified.  Reusing `appCc_assoc` is essential to the cheap proof normal
form: repeating whole-Hom composition extensionality in the divergence
consumer caused a deterministic kernel timeout.  The current frontier is the
fully scalar metric/cometric trace identity `trace_slot_flat`, valid for an
arbitrary covariant rank-two tensor.  No consumer assumption,
`HasLocallyConstantChartAt`, wrapper black box, Hessian-symmetry hypothesis, or
spectral-support-dependent constant was added.

Honest accounting: Perelman no-local-collapsing and `ham3_noncollapse` remain
0% as endpoint theorems, with about 40% dedicated analytic machinery.  The
classical moving conjugate-heat theorem remains 0% with about 77% dedicated
machinery; `heatpot_of_maxreg` remains 0% with about 35% directly reusable
machinery.  Whole HCG machinery remains about 53%, with endpoint theorems at
0%.

## 2026-07-14 invariant A2 and Galerkin frontier

The invariant route is mathematically closed.  The moving scalar Laplacian
difference is expressed by the contraction of the inverse-metric difference
with the terminal Hessian, plus the contraction of the connection difference
with the terminal gradient.  Scalar Green/Bochner estimates control the
terminal Hessian and gradient by the spectral `H²` norm with constants
independent of finite spectral support.  This is the correct producer route for
the required support-independent A2 modulus; it does not require a globally
selected frame or `HasLocallyConstantChartAt`.

The live Lean route now realizes that invariant operator on the finite scalar
core: `lapDiffCore_eq_cc` and `scalarGalPert_fin` are focused-verified, and the
A1 finite pairing `cc_a1_unif` is verified.  The finite scalar Galerkin ODE
producer `scalar_gal_exists` is also focused-verified.  Its performance-stable
normal form packages the common time as `ConjGalTime`, keeps the proof predicate
in `IsConjGalTime`, and proves operator estimates only after applying them to a
finite-dimensional vector.  Whole-Hom equalities and broad `simp` are not used.

The generic compactness layer is now checked as well: rank-generic spectral
exhaustion, coefficient-to-`Hs` convergence `tendsto_of_coeff`, weighted Fatou
`fatou_sq_mass`, time Lipschitz control `right_lipschitz`, and the countable
coordinate Ascoli extraction `galerkin_subseq`.  These are machinery only; they
do not yet prove a Galerkin limit satisfies the moving conjugate-heat equation.

The exact live frontier is therefore:

1. finish the independent focused verification of `scalar_crit_tame` after its
   stale upstream curvature/ScalarNonautUniform object chain is refreshed;
2. verify `scalar_gal_bound`, which combines finite ODE existence, the genuine
   A2/A1 coefficient identity, the critical tame inequality, and the generic
   per-scale energy theorem;
3. prove `scalar_gal_subseq` from the checked countable Ascoli/Fatou layer;
4. prove a separate limit-identification theorem passing the finite ODE
   integral identity to the limit, then perform the second-order bootstrap to
   the classical moving conjugate-heat solution;
5. only after that enter Perelman's entropy/noncollapsing endpoint argument.

No new convergence predicate, chart-selector input, supplied A2 black box, or
consumer assumption is authorized or needed.  The endpoint theorem remains
separate from all of this machinery.

Honest accounting: `scalar_gal_exists`, `scalarGalPert_fin`, and their invariant
finite-core realization are **100% verified**.  `scalar_crit_tame`,
`scalar_gal_bound`, and `scalar_gal_subseq` remain theorem-level **0% until
their own focused checks**; the dedicated compactness machinery for
`scalar_gal_subseq` is about **80%**.  `heatpot_of_maxreg` remains theorem-level
**0%** with about **35%** dedicated machinery; the classical moving
conjugate-heat endpoint remains **0%** with about **78%** dedicated machinery.
Perelman no-local-collapsing and `ham3_noncollapse` remain endpoint-level
**0%**, with about **44%** dedicated analytic machinery.  Whole HCG machinery
remains about **54%**, with endpoint theorems at **0%**.

## 2026-07-14 balanced dissipation closure

The balanced-commutator frontier recorded above is closed.  The generic
passenger-slot theorem `slot_iterL_pair` is proved and verified, and the scalar
specializations `cc_comm_pair` and `cc_energy_diss` pass a complete focused
check.  The resulting principal estimate has coefficient
`delta / (1 - delta)` on the top covariant jet plus a support-independent
adjacent-window remainder.  No raw third-order commutator, wrapper assumption,
or `HasLocallyConstantChartAt` input is used.

The remaining Galerkin closure has two producer tasks.  First, generalize the
existing rank-two coefficient-one spectral/Bochner estimate to
`cc_dirichlet_gap` at arbitrary covariant rank.  Second, identify the scalar
finite spectral weighted pairing with the smooth `cc_energy_diss` pairing.
The finite-core representation and spectral-to-jet bounds are already generic.
The required strict smallness is also available without a consumer assumption:
`metric_cp_tendsto` permits an internal fixed choice such as `delta = 1/4`;
only the small metric-seminorm to `gFibreOpBound` adapter remains to be applied.

Honest accounting: `cc_comm_pair` and `cc_energy_diss` are complete (100%),
but `scalar_crit_tame`, `heatpot_of_maxreg`, the classical moving
conjugate-heat theorem, Perelman no-local-collapsing, and `ham3_noncollapse`
remain theorem-level 0%.  Scalar critical-tame dedicated machinery is about
72%; the upper endpoint machinery remains about 35%, 77%, and 40%
respectively.  Whole HCG machinery remains about 53%, with endpoints at 0%.

## 2026-07-14 principal pairing frontier

The previously recorded `trace_slot_flat` and flux-factorization frontier is
closed.  `scalar_flux_split` and `cc_principal_pair` are now proved and
focused-verified.  The principal energy coefficient is exactly the order-zero
metric perturbation `delta / (1 - delta)`, with no spectral-support-dependent
constant and no new consumer assumption.

The exact next producer is `cc_comm_pair`.  A live API audit confirms that the
public theorem in `ConnLapCommutatorCoefficientTame` controls the raw
third-order commutator and is specialized to the rank-two DeTurck resolvent
family, so it is not the selected route.  The correct balanced bilinear chain
already exists privately in `DeTurckPrincipalArmEnergyPairing`; it must be
extracted or generalized to rank-zero scalar data, then specialized through
the scalar flux adapter.  This is a missing reusable API/extraction frontier,
not a new geometric assumption.

Honest accounting: Perelman no-local-collapsing and `ham3_noncollapse` remain
0% as endpoint theorems, with about 40% dedicated analytic machinery.  The
classical moving conjugate-heat theorem remains 0% with about 77% dedicated
machinery; `heatpot_of_maxreg` remains 0% with about 35% directly reusable
machinery.  Whole HCG machinery remains about 53%, with endpoint theorems at
0%.

## 2026-07-14 energy and compactness checkpoint

The scalar critical-energy phase is now closed through the finite-dimensional
uniform estimate.  `scalar_crit_tame` and `scalar_gal_bound` both pass focused
verification without `sorry`; the latter uses the low-layer finite partial
spectral-mass theorem `cc_partial_le_norm` and a private scalar-sum normal form
to avoid a whole-declaration heartbeat wall.  Its public assumptions and
geometric content are unchanged.

The compactness layer in `ConjGalerkinLimit.lean` now passes focused
verification without warnings or `sorry`.
`scalar_gal_subseq` constructs the genuine extracted finite solutions and
inherits every weighted mass bound.  `galLimHs` packages the limiting
coefficients in each spectral Sobolev order, and `galLim_tendsto` proves
fixed-time `H^m` convergence by applying `tendsto_of_coeff` one order above.
All three declarations and their dedicated compactness machinery are now 100%
verified.  The heartbeat repair split only private scalar/Fatou/initial-value
and support-aware Lipschitz producers; the public assumptions are unchanged.

The precise frontier is the separate `scalar_gal_limit`
producer: pass the finite right-derivative ODE to an interval-integral identity
and identify the spectral strong solution.  Only then should the route enter
the spacetime-smooth realization/second-order bootstrap and Perelman's entropy
argument.  No chart-selector hypothesis, supplied A2 black box, new convergence
predicate, or consumer assumption has been introduced.

Honest nested accounting: `scalar_gal_bound` is **100% verified**;
`scalar_gal_subseq` is **100% verified** with **100%** dedicated machinery;
`galLim_tendsto` is **100% verified** with **100%** dedicated machinery;
`scalar_gal_limit` is **0%** with about **40%** dedicated machinery.  The
classical moving conjugate-heat endpoint remains theorem-level **0%** with
about **82%** dedicated machinery.  Perelman no-local-collapsing and
`ham3_noncollapse` remain endpoint-level **0%**, with about **46%** dedicated
analytic machinery.  Whole HCG machinery remains about **54%**, with endpoint
theorems at **0%**.

## 2026-07-15 strong-limit source checkpoint

The intrinsic Galerkin strong-limit source is now assembled through all three
levels: modewise right-FTC plus dominated convergence, the `H⁰` Bochner FTC,
and a genuine `timeH1.mk` / `MaxRegSolutionSpace` package that explicitly links
its represented path to the `H² → H⁰` spectral limit.  The producer continuity
retained in `IsConjGalSubseq` is filled by existing A2/A1 theorems; no consumer
assumption, new convergence predicate, or chart selector was added.

Verification has not yet reached these proof bodies because the shared targeted
build is refreshing a long chain of missing upstream curvature and spectral
objects.  Therefore `scalar_gal_limit` remains theorem-level **0%**.  Its source
implementation is about **90% assembled**, while only the previously checked
roughly **40%** should be counted as verified dedicated machinery until the new
file passes.  The classical moving conjugate-heat / `IsHeatPotOn` theorem,
Perelman no-local-collapsing, and `ham3_noncollapse` all remain theorem-level
**0%**.  The canonical whole-HCG machinery estimate is about **57%**, with HCG
endpoint theorems still **0%**.
