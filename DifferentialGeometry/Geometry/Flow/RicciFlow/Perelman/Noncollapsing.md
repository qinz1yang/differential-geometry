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

## 2026-07-15 strong-limit closure

The intrinsic spectral Galerkin phase is now verified through
`scalar_gal_bound`, `scalar_gal_subseq`, `galLim_tendsto`, and
`scalar_gal_limit`; each theorem is **100% verified**.  In particular,
`scalar_gal_limit` is theorem-level **100%**, and its dedicated strong-limit
machinery is **100%**.  It produces a genuine `MaxRegSolutionSpace` object with
the exact initial trace, time derivative, and represented `H² → H⁰` path.

This does not yet produce a classical heat potential.  `heatpot_of_maxreg` is
theorem-level **0%**, and the classical moving conjugate-heat / `IsHeatPotOn`
theorem is also **0%**.  The next exact frontier is the joint-spacetime
realization of the all-order spectral strong path, not another strong-limit
packaging theorem.

Perelman no-local-collapsing and `ham3_noncollapse` remain endpoint-level
**0%**.  Their dedicated analytic machinery remains about **46%**; the whole
HCG machinery estimate remains about **57%**, with all HCG endpoint theorems at
**0%**.

## 2026-07-15 all-scale velocity and first-jet closure

The scalar Galerkin path now has an order-independent positive backward-time
slab on which its equation velocity lifts continuously to every natural
Sobolev order (`galLimVel_lift`).  The follow-up `galLimExt_deriv` proves that
this lift is the genuine strong `H^m` derivative of the all-order Galerkin path
at every interior time.  Both theorems pass focused verification without
warnings or `sorry`.

The order-zero compatibility theorem `lapDiffHs_eq_A20` is also verified in a
fully applied normal form.  Input and output Sobolev casts occur only after the
operator is applied; the rejected whole-operator equality deterministically
forced normalization through reducible continuous-linear-map types and timed
out.  No consumer assumption, chart selector, or replacement convergence
predicate was added.

This closes the continuous all-spatial-order velocity and first time-jet phase,
not classical heat-potential existence.  The next exact frontier is second and
higher interior time jets, which requires time derivatives of the A2 and scalar
potential coefficient families as Sobolev-scale operators, followed by scalar
joint-spacetime reconstruction and pointwise PDE identification.
`heatpot_of_maxreg`, `IsHeatPotOn`, Perelman no-local-collapsing, and
`ham3_noncollapse` remain theorem-level **0%**.  Dedicated classical
conjugate-heat machinery is about **85%**; whole HCG machinery remains about
**57%**, with its endpoint theorems at **0%**.

## 2026-07-15 higher-time-jet consult frontier

The completed Pro consultation, checked against the GitHub
[`short-time-existence` branch](https://github.com/liao9yuan/differential-geometry/tree/short-time-existence),
rules that the next producer is not another limit wrapper and not the large
DeTurck forcing stack.  It is a generic, fully applied pathwise regularity
bridge through Sobolev completion: joint mixed coefficient smoothness plus a
finite `C^k` Sobolev path must yield finite `C^k` regularity of the applied
completed action.  No whole-Hom or whole-CLM equality is needed.

The live tree has only smooth-core `app_hs_*` estimates, not a generic
completed `appHs`.  Consequently the exact implementation frontier begins in
`ParametricAppHs.lean`: construct the canonical completion and its core
application theorem, then prove the smooth-core/pathwise regularity transfer.
Only afterward should the scalar potential and moving Laplacian specializations
be assembled and used in the simultaneous all-spatial-order ODE induction for
`galLimExt_smooth`.

Once `galLimExt_smooth` is available, compact-interior spectral jet majorants
are no longer a separate parabolic bootstrap: take the time derivative in a
higher Sobolev order, bound its norm on the compact time interval, and spend a
Weyl-summable negative weight to obtain one modewise majorant.  Rank-zero joint
reconstruction and pointwise equation/initial-value realization remain
separate producers before any honest `heatpot_of_gallim` theorem.

Accounting remains separated: `galLimExt_smooth` is **0%** as a theorem and its
dedicated higher-time-jet machinery is about **35%**; the generic completed
action time-regularity brick is **0%**.  `galLim_jet_mass`, scalar joint
reconstruction, `heatpot_of_gallim`, Perelman noncollapse, and
`ham3_noncollapse` remain theorem-level **0%**.  The previous approximately
**85%** classical-machinery estimate refers to the whole conjugate-heat route;
it must not be read as completion of this newly isolated higher-time-jet
sublane.

## 2026-07-16 applied-action pause checkpoint

The consult-selected producer route has materially advanced. The generic
completed coefficient action `appHs`, its smooth-core compatibility and
uniform coefficient-independent bound, one jointly smooth coefficient
derivative valid for every Sobolev order, and the fixed-input `C∞` path theorem
are implemented and verified. `iterCovGradHs` now completes fixed-background
iterated covariant differentiation from `H^(k+j)` to `H^k`, also verified.

At the scalar specialization, `lapDiffHs_decomp` is focused-green and gives the
real loss-two decomposition through the principal trace coefficient and the
connection-trace coefficient. `lapDiffHs_path_cd` is implemented by composing
the two generic applied paths with backward affine time, and now also passes
focused verification without warnings or `sorry`. The initial unknown-public-
declaration diagnostic disappeared after the narrow `ScalarFluxJetBound`
refresh, confirming that it was stale-import fallout rather than a theorem or
API obstruction.

The next genuine theorem frontier is to normalize the strong derivative from
`galLimExt_deriv` to the explicit all-scale velocity and prove the dynamic-input
completed-action product rule used by the simultaneous Banach ODE induction.
No new consult is currently indicated.

Honest accounting: the original and all-scale `A2` estimates, generic applied
time regularity, the scalar decomposition, and the scalar fixed-input path
theorem are **100%**. `galLimExt_smooth` remains theorem-level **0%**, with its
dedicated machinery about **63%**. `galLim_jet_mass`, scalar reconstruction,
`heatpot_of_gallim`, Perelman noncollapse, and `ham3_noncollapse` remain
theorem-level **0%**. Whole HCG machinery remains approximately **57%**, with
all endpoint theorems at **0%**.

## 2026-07-16 all-time-jet checkpoint

The dynamic completed-action route is now closed. `ParametricAppHsTime`
proves the fully applied product rule and all finite/infinite time regularity;
`ScalarPotentialTime` and `ScalarNonautTime` specialize it to the potential
and loss-two Laplacian-difference arms. The canonical strong ODE in
`ConjGalerkinStrong` then proves `galLimExt_smooth` simultaneously at every
natural Sobolev order on one common smaller positive interval.

`ConjGalerkinClassical.galLim_jet_mass` now closes the first item on that list:
on every compact interior time interval, all coefficient time jets have a
single summable spectral majorant at every natural Sobolev order.  Its proof
uses the rank-generic compact mass producer and the closed-manifold counting
tail.  The latter still inherits the existing
`WeylEigenvalueCountingBound.lean` `sorry`, so this dependency chain is not yet
globally sorry-free.

The live order is now:

1. rank-zero joint spacetime reconstruction;
2. pointwise PDE and initial-value realization;
3. `heatpot_of_gallim`, followed by the genuine entropy/noncollapse argument.

No `HasLocallyConstantChartAt`, consumer-side black box, whole-Hom equality,
or whole-CLM equality was added. `galLimExt_smooth` and
`galLim_jet_mass` are now theorem-level **100%**, with their dedicated
machinery **100%**. Reconstruction, `heatpot_of_gallim`, Perelman noncollapse,
and `ham3_noncollapse` remain theorem-level **0%**. Classical conjugate-heat
dedicated machinery is about **90%** and whole HCG machinery is conservatively
about **59%**; all HCG endpoint theorems remain **0%**.

## 2026-07-16 classical heat-potential closure

The Galerkin route now reaches the genuine classical interface.
`galLim_slice_cc` realizes every time slice by one smooth rank-zero tensor at
all natural Sobolev orders.  `galLim_pde` reconstructs the scalar series and
proves its pointwise moving heat-potential equation.  Finally,
`heatpot_of_gallim` packages joint smoothness, closed-slab continuity, smooth
slices, the initial trace, and the pointwise equation into an actual
`IsHeatPotOn` on a nontrivial closed reversed-time interval.  These three
theorems and their dedicated classical reconstruction machinery are **100%**.

The proof stays in fully applied scalar normal form: it does not use a global
frame, whole-Hom equality, whole-CLM equality, `HasLocallyConstantChartAt`, or a
new consumer-side black box.  The full dependency chain still inherits the
existing `sorry` in `ShortTime/WeylEigenvalueCountingBound.lean`; the new
theorem bodies themselves contain no local `sorry`.

The next analytic frontier is no longer classical existence.  The constructed
heat potential still has arbitrary smooth initial data, so the route must now
produce the normalized/nonnegative conjugate-heat data actually consumed by
the entropy argument, then prove W-monotonicity and the cutoff contradiction.
Perelman no-local-collapsing and `ham3_noncollapse` remain theorem-level
**0%**.  Their broader entropy/noncollapse machinery is about **52%**; whole
HCG machinery is conservatively about **60%**, with every HCG endpoint theorem
still **0%**.

The immediate assembly above this checkpoint is also closed:
`heatpot_exists` removes the conditional Galerkin-subsequence input for every
smooth initial tensor, and `conj_heat_exists` supplies the corresponding
`IsConjHeatOn` solution with its exact terminal trace.  Both are theorem-level
**100%**.  The live frontier is now positivity plus interval-local mass
conservation/normalization; the existing mass theorem cannot yet consume the
new solution directly because it asks for global `FunctionRegularAt` and
`MetricFamilyRegularAt` data.

The first positivity step is now closed as well.  `conjCoeff_bound` exports a
uniform pointwise bound for the reversed scalar-curvature coefficient on a
short closed interval, and `gallim_nonneg` intersects that interval with
`heatpot_exists`, restricts the solution, and applies the existing weak maximum
principle.  Thus nonnegative smooth initial data yield a nonnegative classical
heat potential without a new coefficient-bound assumption.  Both theorems are
**100%**.  Strict positivity and interval-local unit mass remain open; the
first shared mass blocker is a joint-local moving-volume first-variation API.

## 2026-07-16 positive unit-mass and potential checkpoint

The remaining classical input is now closed.  `gallim_pos` upgrades the
nonnegative solution to strict positivity, `heatpot_mass_deriv` proves the
interval-local moving-volume derivative directly from `first_var_joint`, and
`heatpot_mass_eq` turns that derivative into endpoint-inclusive mass
constancy.  `gallim_unit_pos` packages the result: unless `M` is empty, one
obtains a genuine strictly positive reversed heat potential of moving
Riemannian mass one on a nontrivial closed interval.  These producers and
their dedicated positivity/mass machinery are **100%**; no global
`MetricFamilyRegularAt` or `FunctionRegularAt` assumption was added to their
consumers.

`Entropy/Potential.lean` now defines `perelmanPotential` and proves both exact
inverse bridges: `density_potential` recovers the positive density, while
`weighted_potential` identifies the Perelman weighted measure with
`u dmu`.  This scalar bridge is **100%** and has no flow or regularity
assumptions.  It is machinery for the entropy route, not a W-monotonicity or
noncollapsing theorem.

The live W route is therefore:

1. prove the pointwise potential evolution equation, using native logarithmic
   gradient/Laplacian rules;
2. prove the invariant moving-metric derivative of the gradient-square term;
3. assemble the weighted geometric square completion, W monotonicity, and the
   cutoff contradiction.

W monotonicity, Perelman no-local-collapsing, and `ham3_noncollapse` remain
theorem-level **0%**.  Their dedicated entropy/noncollapse machinery is now
about **59%**; whole HCG machinery remains conservatively about **60%**, with
all HCG endpoint theorems still **0%**.  This chain still inherits the existing
`ShortTime/WeylEigenvalueCountingBound.lean` `sorry`; none of the new
positivity, mass, or potential-bridge theorem bodies adds a local `sorry`.

## 2026-07-16 raw W first-variation checkpoint

The first two items of the preceding live route are closed.  The checked
producers are `potential_pde`, `potential_df_time`, `potential_joint`,
`normGradSq_time`, `gradSq_joint`, `revGram_smooth`, `revTrace_eq`,
`revScalar_time`, and `revGradSq_time`.  `w_rev_hasDerivAt` now assembles these
actual inputs into the interval-local first variation of Perelman's `W`
functional along the reversed Ricci flow with the genuine `conjCoeff`
heat-potential input.  It adds no supplied regularity package, global frame,
whole tensor/Hom equality, or `HasLocallyConstantChartAt`.

This closes only the raw first-variation theorem.  The geometric square
completion and weighted divergence cancellation remain open.  The next exact
producer is `ricDriftDiv`, followed by `weighted_hess_split`;
`hessSec_inner_cov` and `ricHess_eq_inner` are checked low-level inputs.

Honest accounting: `w_rev_hasDerivAt` and its dedicated raw-variation machinery
are **100%**.  Weighted square completion, W monotonicity, Perelman
no-local-collapsing, and `ham3_noncollapse` remain theorem-level **0%**.
Broader entropy/noncollapse machinery is approximately **67%**; whole HCG
machinery remains approximately **60%**, with all HCG endpoints at **0%**.

## 2026-07-16 weighted square checkpoint

The invariant square route is now closed through the actual reversed flow.
Checked producers include `metricNablaSymm`, `ricDriftDiv`, `ricDriftAct`,
`weighted_grad_zero`, `weighted_hess_split`, `weighted_bochner`, and
`weighted_w_square`.  `w_rev_square` rewrites the checked raw first variation
as the negative weighted square of `Ric + Hess f - g / (2s)`, and
`w_rev_deriv_nonpos` proves the corresponding local first-variation sign.
The assembly remains scalar after tensor contraction and adds no dimension,
chart, or supplied-regularity assumption.

Honest accounting: the raw variation, square completion, and local derivative
sign theorems are **100%**, together with their dedicated machinery.  A
separate interval `MonotoneOn` theorem is not yet stated (**0%**).  The cutoff
contradiction, Perelman no-local-collapsing, and `ham3_noncollapse` remain
theorem-level **0%**.  Broader entropy/noncollapse machinery is approximately
**75%**; whole HCG machinery remains approximately **60%**, with HCG endpoints
at **0%**.  The next live task is to inventory the existing cutoff/local-volume
API and state the smallest honest producer needed by the contradiction.

## 2026-07-16 interval W and lower-bound frontier

`w_rev_antitone` is checked on every positive closed reverse-time interval
inside both regular-time domains.  Thus the actual interval W monotonicity
theorem and its dedicated first-variation/square machinery are **100%**.  The
measure-theoretic normal form used by that proof has also been moved from a
private consumer helper to the canonical public theorem `wFunctional_base`.

The cutoff audit exposes two distinct remaining analytic stages.  First, the
closed-manifold Sobolev embedding must choose its constant before the test
function; `sobolev_closed` makes that quantifier order explicit while keeping
the old per-function theorem as a specialization.  This is groundwork for a
fixed-metric log-Sobolev/W lower bound, not the lower bound itself.  Second, the
project still lacks an intrinsic ball cutoff with support in `B(x,r)`, value one
on `B(x,r/2)`, and a gradient bound uniform in the ball.  Existing generic bump
existence and Euclidean profile APIs do not provide that geometric estimate.

Honest accounting: reverse-time interval W antitonicity is **100%**;
`w_fixed_lower`, the ball-cutoff estimate, the cutoff contradiction,
Perelman no-local-collapsing, and `ham3_noncollapse` are each theorem-level
**0%**.  Dedicated entropy/noncollapse machinery is approximately **78%**;
whole HCG machinery remains approximately **60%**, with HCG endpoints at
**0%**.  The next exact mathematical frontier is the uniform log-Sobolev/W
lower bound; after it, the substantial geometry frontier is the intrinsic
ball cutoff.  The chain still inherits the existing
`ShortTime/WeylEigenvalueCountingBound.lean` `sorry`.

## 2026-07-16 amplitude and intrinsic Sobolev checkpoint

The first fixed-metric estimate interfaces are now checked.  In
`Entropy/PotentialGeometry.lean`, `square_pot_energy` proves the exact
`v^2 |grad f|^2 = 4 |grad v|^2` conversion.  In `Entropy/WEstimate.lean`,
`w_square_form` rewrites the potential-form W functional into its Dirichlet,
scalar, entropy, and prefactor terms.  On the analytic side,
`sobolev_closed` chooses its constant before all test functions, and
`sobolev_intrinsic` composes it with the existing uniform chart-to-intrinsic
bound to control `L^{p*}` by the intrinsic scalar and gradient `L^p` norms.
All four producer layers are **100%** and add no cutoff or log-Sobolev
assumption.

The precise live frontier is now the entropy Jensen/log-Sobolev estimate for
normalized positive amplitudes.  That theorem is still **0%**, so the derived
fixed-metric W lower bound `w_fixed_lower` is also **0%**.  After those, the
substantial geometric frontier remains an intrinsic ball cutoff with a
scale-uniform gradient bound, followed by the cutoff contradiction.
No-local-collapsing and `ham3_noncollapse` remain theorem-level **0%**.
Dedicated entropy/noncollapse machinery is approximately **80%**; whole HCG
machinery remains approximately **60%**, with its endpoints at **0%**.

## 2026-07-16 fixed-metric W closure and cutoff frontier

The fixed-metric entropy chain is now checked end to end.  The new producers
`withDensity_prob`, `int_log_le_moment`, and `entropy_le_moment` supply the
measure-theoretic Jensen step.  `sobolev_lpNorm` exposes the intrinsic `L²` to
`L⁶` estimate, and `logSobolev_closed` chooses one three-dimensional closed-
manifold log-Sobolev constant before the scale and amplitude.  Finally,
`log_prefactor`, `w_fixed_lower`, and `w_density_lower` prove the actual
canonical W lower bound in both positive-amplitude and positive-density normal
forms.  These producer theorems are individually **100%** and introduce no
cutoff assumption or redundant dimension instance.

The audit now isolates one substantial analytic producer: a quantitative
intrinsic ball cutoff (or an energy-equivalent smooth approximation theorem).
The existing smooth bump API has no derivative estimate, the available
manifold smooth approximation is only `C⁰`/support controlled, and the current
normal-chart route has no proved uniform positive normal radius independent of
the injectivity-radius conclusion.  Therefore the intrinsic cutoff theorem,
the cutoff W upper contradiction, `NoLocalCollapsing`, and
`ham3_noncollapse` remain theorem-level **0%**.  Dedicated entropy/noncollapse
machinery is conservatively approximately **85%**; whole HCG machinery remains
approximately **60%**, and HCG endpoint theorems remain **0%**.  The chain
still inherits the existing `ShortTime/WeylEigenvalueCountingBound.lean`
`sorry`.

## 2026-07-16 cutoff-density correction and exact stop

The preceding cutoff audit understated the available approximation layer.
The branch already contains the genuine chart-Sobolev density theorem
`contMDiff_dense_in_WkpChart`, its arbitrary-order analogue
`contMDiff_dense_in_WkpChart_k`, and the per-chart strong-support theorem
`exists_smooth_strong_support_approx`. It also contains the uniform smooth
multiplier and smooth chart-to-intrinsic gradient estimates needed after an
input has entered `MemWkpChart`. Thus ordinary smooth density is not the live
frontier.

The exact missing producer is the nonsmooth entrance theorem for the intrinsic
distance tent: prove that the `4 / r`-Lipschitz function which is one on
`B_g(x,r/2)` and zero outside `B_g(x,3r/4)` lies in
`MemWkpChart g 1 2`, with a quantitative first-order bound uniform in `x` and
small `r`. This is Riemannian Rademacher/weak-gradient content. Neither
`MemW1pIntrinsicLp_of_MemWkpChart` nor the existing intrinsic/chart norm
comparisons supply it: their current public forms still require a smooth
input.

Once that producer exists, the remaining support bookkeeping is routine.
Approximate the tent by `contMDiff_dense_in_WkpChart`, choose a smooth outer
bump equal to one near the tent support and supported in `B_g(x,r)`, and
multiply. The multiplier bound lets the approximation error be chosen small
enough to retain definite inner `L2` mass and the scale-order Dirichlet bound.
The cutoff contradiction needs neither an exact plateau nor a nonnegative
approximant, because it uses the square of the amplitude and entropy Jensen on
its support.

The cheapest consumer-facing normal form is a theorem named
`exists_cutoff_energy` (exactly twenty characters): for each fixed `g`, choose
one finite constant before `x` and `0 < r <= 1`; then produce a smooth
amplitude supported in `B_g(x,r)`, with `L2` mass bounded below by a fixed
multiple of `Vol_g(B_g(x,r/2))` and Dirichlet energy bounded by
`C_g r^-2 Vol_g(B_g(x,r))`. A universal numerical constant such as `64` is
stronger than this route supplies and is not required by the fixed-metric
cutoff contradiction. The existing chart equivalences naturally produce a
constant depending on `g` and the canonical finite POU.

The remote Pro answer obtained during this checkpoint could not inspect the
repository and incorrectly reported that no `W^{1,p}` density theorem exists.
It is therefore not used as project evidence; the live declarations above are
the source of truth. No follow-up consultation was sent. Future consultations
are user-triggered only.

Honest accounting: `w_fixed_lower` and `w_density_lower` remain **100%**.
`exists_cutoff_energy`, the cutoff W upper contradiction,
`NoLocalCollapsing`, and `ham3_noncollapse` are theorem-level **0%**. The
dedicated cutoff machinery is approximately **55%** (density, outer support,
smooth multiplication, and smooth intrinsic estimates exist; the quantitative
Rademacher entrance producer is absent). Dedicated entropy/noncollapse
machinery remains approximately **85%**; whole HCG machinery remains
approximately **60%**, and HCG endpoints remain **0%**.

### Prepared consult prompt (superseded; do not send automatically)

```text
Please diagnose the smallest Lean 4 producer that closes the intrinsic cutoff
frontier in liao9yuan/differential-geometry. Inspect the GitHub reference page
for the canonical short-time-existence branch:
https://github.com/liao9yuan/differential-geometry/tree/short-time-existence
and, when visible, compare the aligned branch
https://github.com/liao9yuan/differential-geometry/tree/codex/short-time-existence-align
at commit 67c9b6b2ce31c2e3b32f424a90c5d27d30995593.

Relevant live producers are:
- Analysis/Sobolev/Approximation/ContMDiffDense.lean:
  contMDiff_dense_in_WkpChart
- Analysis/Sobolev/Approximation/SmoothDensity.lean:
  exists_smooth_strong_support_approx
- Analysis/Sobolev/Chart/SmoothDensity/SmoothMulQuant.lean:
  wkpNormChart_smooth_mul_le
- Analysis/Sobolev/Intrinsic/EquivalenceForward.lean:
  eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform

The missing input is a quantitative theorem saying that the intrinsic distance
tent, equal to one on B_g(x,r/2), zero outside B_g(x,3r/4), and Lipschitz with
constant 4/r, lies in MemWkpChart g 1 2 with a bound uniform in x and 0<r<=1.
After that, existing W1 density plus a smooth outer bump closes support, L2
mass, and metric-dependent C_g/r^2 energy estimates.

Please identify the cheapest repository-native proof route and exact existing
lemmas to reuse. If a generic Lipschitz-to-MemWkpChart theorem is too large,
give the smallest distance-tent-specific statement and proof decomposition.
Do not add consumer assumptions, do not use HasLocallyConstantChartAt, do not
hide the gap behind a wrapper hypothesis, and keep every new theorem name at
most 20 characters. Distinguish what is already proved on the cited GitHub
branch from what genuinely needs a new theorem.
```

## 2026-07-16 distance tent and intrinsic weak-gradient frontier

The preceding checkpoint's qualitative entrance is now closed.
`mem_chart_one_of_lip` proves that every bounded function Lipschitz for an
explicit `riemannianEDistOf g` belongs to `MemWkpChart g 1 p`, using the
Euclidean Rademacher/weak-partial API and the actual local chart domains.  Its
focused check and targeted module build passed.  This theorem is qualitative:
the compactness-produced chart constants are not the universal intrinsic
gradient constant.

The geometric tent itself is also checked in
`Geometry/Metric/DistanceTent.lean`.  `riemDistTent` reuses Mathlib's
`thickenedIndicator` rather than maintaining a parallel truncation API.
`riemTent_mem_Icc`, `riemTent_eq_one`, `riemTent_eq_zero`,
`riemTent_support`, `riemTent_tsupport`, and `riemTent_lip` give the exact
range, plateau, zero region, support margin, and `4 / r` explicit-distance
Lipschitz bound.  Infinite extended distances are handled correctly.

The exact remaining obstruction is now narrower and intrinsic.  The live
`MemW1pIntrinsicLp_of_MemWkpChart` still requires `ContMDiff` and forwards to
the smooth theorem; it is not a nonsmooth chart-to-intrinsic bridge.  Existing
chart density does not preserve the tent's intrinsic Lipschitz constant, and
the available smooth chart-to-intrinsic estimates introduce metric/chart
constants.  Thus they do not prove the scale-sharp a.e. bound

```text
|weakGrad_g (riemDistTent g x r)|_g <= 4 / r
```

with gradient supported in the radius-`r` ball.  A direct
`weak_grad_of_lip` route must still supply manifold a.e. differentiability,
the pointwise intrinsic derivative bound, and global weak integration by
parts; alternatively one would need a global smoothing theorem preserving
the intrinsic Lipschitz constant, which the branch does not contain.

No Pro consultation was sent.  Future consultations are user-triggered only;
if this intrinsic assembly reaches a genuine stop, prepare a copy-paste prompt
here and wait for the user to decide whether to send it.

Honest accounting: `riemDistTent` and its geometric/support API are **100%**;
`mem_chart_one_of_lip` is **100%**.  A theorem `weak_grad_of_lip` is not yet
stated or proved (**0%**); its dedicated prerequisites are approximately
**35%** because Euclidean Rademacher and chart localization are checked but
intrinsic reconstruction and weak IBP are absent.  `exists_cutoff_energy`, the
cutoff W upper contradiction, `NoLocalCollapsing`, and `ham3_noncollapse`
remain theorem-level **0%**.  Dedicated cutoff machinery is approximately
**65%**, broader entropy/noncollapse machinery approximately **86%**, and
whole HCG machinery remains approximately **60%**, with HCG endpoints at
**0%**.

## 2026-07-17 smooth cutoff energy closure

The intrinsic cutoff producer is now closed in `Perelman/CutoffEnergy.lean`.
`exists_cutoff_energy` constructs a smooth function supported in the radius
`r` ball, retains at least one half of the half-ball square-root volume in its
`L²` norm, and bounds its metric-gradient `L²` norm by `5 / r` times the
outer-ball square-root volume.  Squaring gives exactly the mass/Dirichlet
normal form needed by the cutoff contradiction.  Focused verification passed
without warnings.  No global frame, varying-fibre equality, new consumer
assumption, or `HasLocallyConstantChartAt` was introduced.

Honest accounting: `exists_cutoff_energy` is theorem-level **100%**, and its
dedicated machinery is **100%**.  The cutoff W upper contradiction,
`NoLocalCollapsing`, and `ham3_noncollapse` remain separate theorem-level
frontiers at **0%**.  Broader entropy/noncollapse machinery is approximately
**90%**; whole HCG machinery remains approximately **60%**, with the HCG
endpoint theorems at **0%**.  The next smallest frontier is to insert this
cutoff into the already checked fixed-metric W lower-bound framework and prove
the local collapsing upper estimate contradicts it.

## 2026-07-17 normalized cutoff W-form closure

`Perelman/CutoffW.lean` now closes the next honest layer:

- `normalize_cutoff` gives unit `L²` mass, support preservation, gradient
  integrability, and the exact Dirichlet rescaling identity;
- `exists_cutoff_wdata` combines it with `exists_cutoff_energy` and gives the
  explicit outer-gradient/half-ball-mass ratio bound;
- `exists_cutoff_wform` applies the verified support-entropy theorem and
  `w_form_upper`, producing the full scalar square-form cutoff upper bound.

All three are verified without `sorry`.  The cutoff square-form upper theorem
and its dedicated machinery are 100%.  The actual `wFunctional` theorem is
still 0% because the cutoff can vanish and `w_square_form` requires a strictly
positive amplitude; the positive regularization/limit bridge remains genuine
work.  The flow-uniform entropy lower bound and `NoLocalCollapsing` remain 0%.
The broader entropy/noncollapsing machinery is now about 92%; whole HCG
machinery remains about 60%, while the endpoint theorems remain 0%.

## 2026-07-17 curvature-controlled flow-ball assembly

The invariant curvature arm is now closed.  `scalar_abs_le_rm` proves the
canonical trace estimate `|R| ≤ n² |Rm|`; `scalar_le_of_rm` converts
`FlowMetricBall.IsRmControlled` into the scale-correct scalar upper bound on
the backward cylinder; and `flowball_wform` feeds that bound directly into the
verified normalized cutoff W-form theorem at the ball's distinguished time.
All three focused checks passed, and the lower curvature module targeted build
passed.

Honest frontier: the curvature-controlled flow-ball square-form producer and
its dedicated machinery are 100%.  The actual positive-amplitude
`wFunctional` cutoff theorem is still 0%; its smallest missing theorem is a
regularization/limit bridge from a possibly vanishing normalized amplitude to
strictly positive smooth amplitudes while preserving the W upper bound.  After
that, a collapsed-scale selection lemma must control the outer/half-ball volume
ratio, and a flow-uniform W lower bound must be connected across time.  Thus
`NoLocalCollapsing` and `ham3_noncollapse` remain 0%.  Broader
entropy/noncollapsing machinery is about 94%; whole HCG machinery remains about
60%, with its endpoint theorems at 0%.

## 2026-07-17 positive W cutoff closure

The positive-amplitude obstruction is now closed without a new convergence
assumption.  `Analysis/Integration/EntropyMix.lean` proves subadditivity of the
continuous entropy integrand `-x log x`.  `Entropy/PositiveApprox.lean` uses it
to mix the squared cutoff with a small uniform density, take a strictly positive
smooth square root, preserve unit mass, and keep the full square-form value
within any prescribed positive error.  Its Dirichlet energy is pointwise no
larger than the original one.

`exists_cutoff_wform` now returns the already proved Dirichlet integrability,
and `flowball_w_upper` combines that producer with `w_square_form`.  Hence a
curvature-controlled `FlowMetricBall` now has a genuine strictly positive
unit-mass test amplitude with an upper bound on the actual `wFunctional`, not
only on a scalar proxy.  Focused verification passed for every edited module;
the two new lower modules also passed targeted verification.

Honest accounting: the positive-amplitude approximation theorem and the actual
flow-ball W upper theorem are each 100%; their dedicated machinery is 100%.
`NoLocalCollapsing` and `ham3_noncollapse` remain theorem-level 0%.  The next
mathematical frontier is collapsed-scale selection controlling the outer-ball /
half-ball volume ratio; after that, the time-uniform lower W bound must be
assembled from the existing fixed-time lower theorem and flow monotonicity.
Broader entropy/noncollapsing machinery is now about 96%; whole HCG machinery
remains about 60%, with HCG endpoint theorems at 0%.

## 2026-07-17 selected W bound and exact flow frontier

Collapsed-scale selection is now closed.  `exists_coll_scale` chooses a genuine
nested dyadic `FlowMetricBall`, preserves the full backward-parabolic curvature
bound, does not increase normalized volume, and proves the exact outer/half
volume ratio needed by the cutoff.  `exists_sel_w_bound` then produces a
strictly positive unit-mass amplitude satisfying the actual estimate

`W ≤ collapseWConst n + log (Vol(B) / radius(B)^n) + δ`.

Both the selector and the selected W theorem are 100%, with their dedicated
machinery 100%.  They have no spectral-support constant, chart selector,
Bishop--Gromov input, or injectivity-radius assumption.

The remaining flow bridge was checked through three routes.  A direct use of
`gallim_pos` and `w_rev_antitone` initially has a scale/time offset; the new
checked `heat_pot_add` theorem removes that offset by translating the reverse
solution.  It does not close the comparison because the heat solution exists
only on an unspecified short interval and W antitonicity applies only inside
the open regular interval, excluding the prescribed initial cutoff slice.  A
fixed-time use of `w_fixed_lower` gives a constant depending on the time-slice
metric and therefore is not uniform as a finite singular time is approached.
A direct compact-family log-Sobolev bound also does not apply on a
`closedOpen 0 ω` flow: the existing solution predicate provides no uniform metric
control at the excluded singular endpoint.

The smallest honest missing producer is thus a finite-horizon W comparison:
first prove right continuity of the offset W functional at the prescribed
smooth Galerkin initial slice using the retained all-order Sobolev continuity,
then globalize the data-independent local heat existence across a compact
reverse-time interval.  Adding endpoint continuity as an assumption to a
consumer would merely hide this work and is not acceptable.

Honest accounting: the selected-scale cutoff contradiction machinery is about
99%, but the finite-horizon W lower theorem is not yet stated/proved and is 0%
(its dedicated existing machinery is about 90%).  `NoLocalCollapsing` and
`ham3_noncollapse` remain theorem-level 0%.  Broader entropy/noncollapsing
machinery is about 97%; whole HCG machinery remains about 60%, with HCG
endpoint theorems at 0%.

## 2026-07-17 Galerkin endpoint-continuity advance

The consult recommendation was checked against the live branch and narrowed to
existing native APIs. `potential_grad_sq` already existed, and the public
dimension-three estimate `hs3_grad_low2` already supplied the required
support-independent `H3` pointwise control, so neither was duplicated.

The first endpoint layer is now verified. `galLimExt_zero` gives the exact
Sobolev initial value; `sq_unit_eval_le` bounds a fully evaluated rank-one
tensor by its intrinsic fibre norm; `covGrad0_apply` scalarizes the rank-zero
covariant derivative. These feed `galLim_d_zero` and the stronger
`galLim_d_joint`, proving endpoint convergence of real-valued directional
derivatives in one actual local chart frame. This follows the scalar
local-to-global route and avoids any equality of dependent tensor/Hom fibres.

The moving inverse-Gram contraction `galLim_grad_zero` is assembled in source
but not yet counted as proved: its focused check was prevented before theorem
elaboration by a temporarily missing shared `RadialGronwall.olean`, downstream
of another lane's claimed `RadialGram` refresh. After that check is green, the
remaining endpoint chain is: glue with positive-time `gradSq_joint`; prove the
moving W integrand and integral continuous on the closed short interval using
`integral_family_cont`; compare the initial cutoff W value with positive-time
W antitonicity; then globalize the terminal-uniform span by the finite Good-set
induction from the consult route.

Honest accounting: the finite-horizon W comparison theorem remains
theorem-level **0%** and its dedicated endpoint-continuity machinery is about
**65%**. The selected-scale contradiction machinery remains about **99%**.
`NoLocalCollapsing` and `ham3_noncollapse` remain theorem-level **0%**.
Broader entropy/noncollapsing machinery remains about **97%**, and whole HCG
machinery about **60%**.

## 2026-07-17 Closed scalar endpoint and W frontier

The scalar Galerkin endpoint layer is now closed and verified.
`galLim_grad_zero` proves the inverse-Gram scalar contraction at reverse time
zero, while `galLim_grad_cont` glues it to positive-time smoothness on a
shortened closed interval. The latter constructs its regular metric window from
the terminal regular time and therefore introduces no new consumer assumption.

The next producer, `gallim_w_cont`, is assembled in `WVariation.lean`. It uses
the real moving Riemannian volume, the existing `potential_grad_sq` identity,
joint continuity of the density, scalar curvature, and density gradient square,
and `integral_family_cont`. Its first attempted verification was blocked before
the theorem elaborated by a stale upstream Galerkin object; the explicit refresh
is active. Thus `gallim_w_cont` remains theorem-level **0%** until the next
focused check is green, despite its source proof being present.

Honest accounting: the Galerkin scalar endpoint-continuity machinery is about
**85%**. The finite-horizon W comparison theorem remains theorem-level **0%**,
as do `NoLocalCollapsing` and `ham3_noncollapse`. Selected-scale contradiction
machinery remains about **99%**, broader entropy/noncollapsing machinery about
**97%**, and whole HCG machinery about **60%**.

## 2026-07-18 verified W endpoint continuity

`gallim_w_cont` now passes focused verification without changing its statement
or adding a consumer assumption. It gives continuity of the genuine moving
Galerkin W path through reverse time zero, using the moving Riemannian measure
and the scalar inverse-Gram gradient-square endpoint proved below the W layer.

The existing `Entropy/F` tree is not an unused competing noncollapsing route.
Its scalar weighted Green results, especially `weightedGreen` and
`weighted_grad_zero`, are already consumed by `WeightedHessian.lean` and hence
by the checked W square/monotonicity chain. Its Formula-5.10 endpoint is for the
separate `F` functional and cannot replace the remaining zero-endpoint W
comparison or finite-horizon heat continuation.

Honest accounting: `gallim_w_cont` and its dedicated endpoint-continuity
machinery are each **100%**. The finite-horizon W comparison theorem remains
theorem-level **0%**, as do `NoLocalCollapsing` and `ham3_noncollapse`.
Selected-scale contradiction machinery remains about **99%**, broader
entropy/noncollapsing machinery about **97%**, and whole HCG machinery about
**60%**.

## 2026-07-18 zero-endpoint W comparison

`gallim_w_le` is now checked.  On a genuine nontrivial shortened interval it
compares the moving Galerkin W value at every reverse time, including zero,
with its terminal value.  Positive reverse times are handled by shifting the
verified classical heat potential and applying `w_rev_antitone`; continuity
from `gallim_w_cont` supplies the zero endpoint.  All shifted identifications
are fully applied scalar equalities, so the proof avoids the dependent-fibre
normalization problem that blocked earlier whole-Hom statements.  No new
consumer assumption was introduced.

This closes the local terminal-time comparison but not the finite-horizon
theorem.  The next exact producer is a compact terminal-uniform Galerkin span
`gal_span`; after it, a target-length classical solution theorem `gallim_on`
and the finite Good-set induction can produce `w_span` without iterating
existential interval shrinks.

Honest accounting: `gallim_w_cont` and `gallim_w_le` are theorem-level
**100%**, and their dedicated local endpoint machinery is **100%**.
`gal_span`, `gallim_on`, `w_span`, `NoLocalCollapsing`, and
`ham3_noncollapse` remain theorem-level **0%**.  Selected-scale contradiction
machinery remains about **99%**, broader entropy/noncollapsing machinery about
**97%**, and whole HCG machinery about **60%**.

## 2026-07-18 compact-span diagnosis

The pointwise Galerkin radii cannot be globalized by taking an infimum of
chosen witnesses.  `lapDiffA20_short`, `conjA1_short`, `cc_a2_unif`,
`scalar_gal_bound`, and `scalar_gal_subseq` all freeze one terminal metric
before selecting their interval, and no lower-semicontinuity result for those
selected radii exists.

The initially proposed form of `gal_span` also asked for the last step
`h = T`, so that the reflected interval reaches time zero.  This is not
derivable from the present solution interface.  For a closed-open flow domain,
zero is a carrier endpoint but not a regular time.  `MetricFamilySmoothOn`
provides joint `C-infinity` regularity only on `D.regular` and merely `C0`
continuity on `D.carrier`; that does not control the first spatial metric jet
needed by A2 uniformly as positive times approach zero.

The cheaper mathematically valid route is to start the lower bound at one
fixed positive regular time, for example half the selected collapse time.
`w_fixed_lower` applies to that single smooth compact metric.  The finite W
propagation then takes place on a compact interval wholly contained in
`D.regular`, so no endpoint regularity upgrade is needed.  Any finite lower
bound at that positive time is enough for the final contradiction.

Even on this interior compact interval, one genuine producer is still absent.
The live API proves time continuity with a fixed background
(`metric_cp_tendsto`) and spatial continuity for fixed metrics
(`metricDerivNorm_cont`), but not the joint varying-background modulus

```lean
(base, var, x) |->
  metricDerivNorm 1 (G.metric var) (G.metric base) (G.metric base) x.
```

This modulus, uniform on a compact regular-time slab and the compact manifold,
is the smallest missing geometric input before the terminal metric and its
spectral spaces are introduced.  Its order-one scalar normal form should use
`metricCovDeriv_one_component_localFrame` (or the existing
`metricCovDeriv_one_component_eq_metricCovAtBase`) and a finite local-frame
cover.  It must not compare whole tensors in varying fibres.  Once this is
available, the existing A2/A1/critical-tame constructions can be replayed with
a target interval inside the common compact span; their lower constants may
still depend on the terminal time and Sobolev order.

Three rejected routes are now explicit: an infimum of arbitrary pointwise
radii has no positivity proof; iterating existential shrinks can Zeno; and a
span reaching the nonregular initial endpoint asks for spatial-jet control not
present in the current hypotheses.  The interior compact-span route is
mathematically sound, but the joint varying-background modulus is a
substantial missing API rather than a local elaboration repair.

### Prepared consult prompt (answered; superseded)

Inspect the GitHub repository
`liao9yuan/differential-geometry`, branch `short-time-existence`, especially:

- `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/Noncollapsing.md`;
- `DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/WVariation.lean`;
- `DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkin.lean`;
- `DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinEnergy.lean`;
- `DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/ConjGalerkinLimit.lean`;
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/Garding/MetricLapDiffTime.lean`;
- `DifferentialGeometry/Analysis/Spectral/Intrinsic/Garding/ScalarNonautUniform.lean`;
- `DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/MetricC1Continuity.lean`;
- `DifferentialGeometry/Geometry/Curvature/Realized/MetricFamily.lean`.

The verified local endpoint chain now contains `gallim_w_cont` and
`gallim_w_le`.  The next goal is a terminal-uniform local Galerkin/W span for a
finite Good-set induction.  Do not propose taking an infimum of the existing
pointwise witnesses: every current Galerkin radius freezes `G.metric T`, and no
lower-semicontinuity theorem for the selected witness exists.

The earlier target `h <= min rho T` allowed `h = T`, hence reached the initial
time zero.  On `RealTimeInterval.closedOpen 0 omega`, zero is only in the
carrier; `MetricFamilySmoothOn` gives joint smoothness on `(0,omega)` but only
`C0` continuity at zero.  Therefore an A2 span reaching zero is not justified
without a forbidden new endpoint assumption.  Please assess the replacement
route: choose one positive regular start time (for example half the collapse
time), apply `w_fixed_lower` there, and propagate W only on a compact interval
contained in `D.regular`.  Is any mathematical ingredient of the
noncollapsing contradiction lost by starting at this positive time?

For that interior route, give the cheapest Lean statement and proof normal
form for the missing compact-uniform modulus, before terminal spectral spaces
are introduced:

```lean
exists rho > 0, forall base var in a compact regular-time slab,
  |base - var| <= rho ->
  metricDerivNormSupOn Set.univ 1
    (G.metric var) (G.metric base) (G.metric base) <= epsilon.
```

The live repository has `metric_cp_tendsto` only for fixed `base`,
`metric_cp_bdd` for a fixed background, and `metricDerivNorm_cont` only for
fixed metrics.  At order one, available scalar bridges include
`metricCovDeriv_one_component_localFrame` and
`metricCovDeriv_one_component_eq_metricCovAtBase`.  Please identify the exact
existing inverse-Gram/local-frame continuity APIs that close the varying
background norm, or state the single smallest missing producer if they do not.
Keep all equalities fully evaluated and scalar; do not compare tensor/Hom
objects in varying fibres.

Then show how to replay the current `cc_a2_unif`, `scalar_crit_tame`,
`scalar_gal_bound`, and `scalar_gal_subseq` proofs on any target interval below
that common radius.  Say whether the fixed shrink factors in
`heatpot_of_gallim`, positivity, and `gallim_w_le` can be absorbed into the
common radius, or whether one target-length theorem is genuinely necessary.

Constraints: no new consumer assumptions, no `HasLocallyConstantChartAt`, no
wrapper black box, no equality between `tensorHs` spaces for different
terminal metrics, and every new theorem name must have at most 20 characters.
Give repository-native Lean statement skeletons with exact theorem references;
do not rely on local filesystem paths.

## 2026-07-18 varying-background span closure

The compact-interior consult route has been adopted.  The endpoint work
`gallim_w_cont` and `gallim_w_le` remains closed, and propagation will start at
one fixed positive regular time rather than trying to obtain first metric-jet
control at the nonregular original endpoint.

The first new producer, `metric_c1_span`, now passes focused verification.  For
every compact slab `Icc a b ⊆ D.regular` and every positive tolerance it gives
one positive radius such that all nearby `base` and `var` in the slab satisfy

```lean
metricDerivNormSupOn Set.univ 1
  (G.metric var) (G.metric base) (G.metric base) ≤ ε.
```

Its proof is genuinely varying-background and scalar.  It uses canonical
coordinate-frame Gram and inverse-Gram entries for the order-zero norm, scalar
spatial derivatives plus the coordinate Koszul formula for the order-one
component, a finite spatial subcover for each diagonal time, and a finite time
subcover of the compact slab.  It introduces no endpoint regularity, global
frame, whole varying-fibre tensor equality, `HasLocallyConstantChartAt`, or new
consumer assumption.

The existing `Entropy/F` tree remains useful but orthogonal to this producer.
Its `weightedGreen` and `weighted_grad_zero` theorems are already consumed by
`WeightedHessian.lean` in the checked W square/monotonicity chain.  The
Formula-5.10 F-functional assembly does not supply the target-length Galerkin
or heat-potential propagation theorem.

The exact next producer is `gal_span`: replay `scalar_gal_exists`,
`scalar_crit_tame`, `scalar_gal_bound`, and `scalar_gal_subseq` on every
prescribed target length below the common radius returned by
`metric_c1_span`.  After that come `gallim_on`, target-length positivity and
mass, and the finite Good-set induction on the positive interior slab.

Honest accounting: `metric_c1_span`, `gallim_w_cont`, and `gallim_w_le` are
theorem-level 100%, with their dedicated local machinery 100%.  `gal_span`,
`gallim_on`, the target-length positivity/mass package, the finite Good-set
induction, `NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level 0%.
Selected-scale contradiction machinery remains about 99%, broader
entropy/noncollapsing machinery about 97%, and whole HCG machinery about 60%.

## 2026-07-18 target-length Garding frontier

The compact-span replay now has a dedicated Garding module,
`ScalarNonautSpan.lean`.  It contains the intended `metricDiff_span` statement
and proof skeleton: one radius on `Icc a b ⊆ D.regular`, any frozen regular
time in that slab, and every requested backward length below the radius.  It
also contains `scalarFlux_span`, which reuses `scalarFlux_jet_grid` and has no
additional analytic frontier.

Focused verification succeeds with exactly one `sorry` warning and no Lean
errors.  The remaining obligation is the already-proved fixed-background
metric-difference joint-smoothness fact, currently private as
`metricDiff_joint` in `ScalarFluxJetBound.lean`.  It is needed only to apply
`joint_jet_bdd` on the prescribed compact interval.  Copying its long
bundle-realization proof was rejected; the canonical repair is to expose the
existing theorem and reuse it.

The subsequent target-length pairing replay has the same visibility issue in
`ScalarNonautUniform.lean`: `appRS_jet_bdd`, `fixed_jet_bdd`,
`fluxDiv_jet_bdd`, and `traceCast_jet_bdd` are generic but private.  Normal
claims on both source files failed because of old ownership-unknown claims
(tokens `4bc8c3d3-d009-4dce-bc77-21043f23e1d4` and
`a05069d7-e9e4-45fc-a965-f4abe11355eb`; recorded processes are dead).  They
were not force-released.

The exact next step is therefore a small canonical API exposure in those two
claimed files, followed by `cc_a2_span`, target-length `scalar_crit_tame`, and
`gal_span`.  Finite-subcovering the existing existential lifetimes is not a
valid substitute because the terminal metric, and hence the spectral space,
varies with the base time.

Honest accounting: `metric_c1_span`, `gallim_w_cont`, and `gallim_w_le` remain
theorem-level 100%.  `metricDiff_span` and `scalarFlux_span` are theorem-level
0% until their single producer `sorry` is discharged; dedicated machinery is
about 95%.  `cc_a2_span`, target-length critical tame/Galerkin, `gallim_on`,
target-length positivity/mass, finite Good induction, `NoLocalCollapsing`, and
`ham3_noncollapse` remain theorem-level 0%.  Broader noncollapsing machinery
remains about 97%, and whole HCG machinery about 60%.

## 2026-07-19 prescribed A2 and critical source

The compact-span Garding replay has now been written through `cc_a2_span`.
Only three existing producer declarations needed public visibility:
`metricDiff_joint`, `fluxDiv_jet_bdd`, and `finite_lap_unif`; the other internal
jet helpers remain private.  The source contains no local `sorry`, chooses the
common radius before the terminal metric and spectral type, and keeps all
constants independent of spectral support and Galerkin cutoff.

The next assembly `scalar_crit_span` is also source-complete.  It combines the
prescribed A2 inequality with `cc_a1_unif` on the caller's exact closed interval
and preserves the coercive top coefficient `23/12 < 2`; it does not select a
second lifespan.  The updated route is therefore reflected exactly:
propagation starts on a compact positive interior slab, not at the nonregular
initial endpoint.

Both edited producer modules pass focused verification.  The A2 span and
critical-span files are not yet theorem-level complete because a sequential
exported-object refresh is still running before their focused checks.  Their
dedicated source and machinery are approximately 99%.  `gal_span`,
`gallim_on`, target-length positivity/mass, finite Good induction,
`NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level 0%.  Broader
noncollapsing machinery remains approximately 97%, and whole HCG machinery
approximately 60%.

## 2026-07-19 operator-span source

Two further target-length producers are now source-complete.  `lapA20_span`
uses the compact varying-background metric modulus at the
dimension-adjusted extension threshold and returns continuity, a compact
operator-norm bound, and the genuine finite-core identity on the caller's
exact `Icc 0 h`.  `conjA1_on` similarly packages the existing lower-order
operator continuity and a finite norm bound without choosing a new lifespan.

These are the exact replacements for the two independently selected short
intervals in `scalar_gal_exists` and `scalar_gal_subseq`.  They add no consumer
assumptions and do not compare spectral spaces belonging to different terminal
metrics.

Verification is currently stopped at missing imported objects rather than a
proof goal.  `CovDerivPointwise` was rebuilt successfully and the edited
`ScalarFluxJetBound` source check then passed; its exported-object refresh is
still active.  A first check of `conjA1_on` next found the missing imported
object `ComponentSobolevBoundDerivBridge.olean`, so no second overlapping build
was launched.  `lapA20_span`, `conjA1_on`, and `scalar_crit_span` remain
theorem-level 0% until their own focused checks pass, with dedicated source and
machinery approximately 98--99%.  `gal_span`, `gallim_on`, Good induction,
`NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level 0%.

## 2026-07-19 exact Galerkin and positive-slab W source

The prescribed-interval source route now reaches the positive-slab W lower
bound.  `gallim_on` reconstructs the scalar Galerkin limit as an exact
`IsHeatPotOn` object; `gallim_pos_on` and `heatpot_mass_on` preserve positivity
and unit mass on the same caller-supplied interval.  `gallim_w_lt` then uses
the already verified local W continuity only for the right limit at reverse
time zero, while exact `w_rev_antitone` supplies the comparison at every
strictly interior reverse time.  Thus the unknown local continuity radius no
longer controls propagation length.

`w_span` performs the finite Good-set propagation on a compact positive
regular slab.  One horizon `r` is selected before the terminal metric; every
actual step is at most `r / 2`, so it lies strictly inside a heat interval of
length `r`.  The induction accepts arbitrary smooth positive unit densities,
including the selected cutoff density and every evolved slice.  Its invariant
is `theta + (t - a) < tauMax`.

All these new declarations are source-complete and contain no local `sorry`,
but none is counted as proved until the active upstream spectral export refresh
finishes and their focused checks pass.  Accordingly `gallim_on`,
`gallim_w_lt`, and `w_span` remain theorem-level **0%** with approximately
**80--95%** dedicated source.  The positive-time W lower route is source-
assembled, while the all-carrier `NoLocalCollapsing` endpoint remains **0%**:
times near the nonregular initial endpoint still need a uniform geometric
small-ball volume producer.  The current fixed-metric, fixed-centre
`exists_edist_vol` theorem does not by itself provide that family-uniform
statement.  `ham3_noncollapse` remains theorem-level **0%**.

## 2026-07-19 positive-slab noncollapse source

The positive-time argument now has its honest geometric target in
`NoncollapseSpan.lean`.  `noncollapse_span` combines the compact-slab W lower
bound with `exists_sel_w_bound`, chooses
`kappa = exp (L - collapseWConst n - 1)`, and proves the actual
`FlowMetricBall.IsKappaNoncollapsed` inequality in `ENNReal`.  It quantifies
only over times in one fixed positive regular slab; it does not pretend to
prove the stronger all-carrier `NoLocalCollapsing` predicate.

The ball-volume positivity needed to exponentiate the logarithmic estimate is
not a consumer assumption.  The former private proof in `FlowBallW.lean` was
moved to the public metric-volume theorem `VolumeComparison.edist_vol_pos` in
`Geometry/Comparison/Volume/SmallBall.lean`, and all existing flow-ball uses
now reuse that lower-layer API.  `w_span_uniform` also exposes the fact that
the W lower constant is chosen from the fixed metric at the positive base time
before the finite upper slab endpoint is quantified; the Galerkin step radius
may still depend on each finite slab without entering this constant.

The remaining initial-time obstruction was checked along three distinct
routes.  Pointwise `exists_edist_vol` cannot be finite-subcovered because the
centre neighborhood would have to shrink with the ball radius.  Joint metric
continuity gives short-time bilinear equivalence and existing distance
comparison, but there is no theorem converting that domination into a uniform
setwise Riemannian-volume lower bound.  The local Bishop comparison still has a
centre-dependent analytic/injectivity radius; the available compact uniform
injectivity theorem assumes lower semicontinuity of the injectivity radius,
which is itself not yet produced from joint exponential-map regularity.  Thus
the smallest honest missing producer remains `early_ball_low`: a normalized
small-ball lower bound uniform in short time, centre, and every radius with
`r^2 <= t`.  This is missing geometry, not a wrapper or a new convergence
assumption.

Source accounting only: `noncollapse_span`, `w_span_uniform`, and the public
volume-positivity refactor contain no local `sorry`, but remain theorem-level
**0%** until their focused checks pass after the active spectral artifact
refresh.  Even after they verify, `NoLocalCollapsing` and `ham3_noncollapse`
remain theorem-level **0%** until `early_ball_low` and the final all-time
assembly are proved.  The Galerkin classical-slice chain also still imports the
explicit Weyl counting frontier in `ShortTime/WeylEigenvalueCountingBound.lean`;
green downstream checks will therefore not make the entropy route axiom-clean.
Broader entropy/noncollapse machinery is approximately **98%**, while whole
HCG machinery remains approximately **60%** and its endpoint theorems remain
**0%**.

### Prepared consult prompt (not sent automatically)

```text
Please diagnose the smallest assumption-free Lean route to the remaining
initial-time producer for Perelman noncollapsing.  Use the GitHub page
https://github.com/liao9yuan/differential-geometry/tree/short-time-existence as
the source of truth for published declarations, and cite exact GitHub-visible
repo-relative files/lines or theorem names from that branch.  Do not invent
signatures.  The local post-merge checkout also has uncommitted proposed
theorems `Entropy.w_span_uniform` and `Perelman.noncollapse_span`; those are not
visible on GitHub and should be treated only as the following summary: the W
argument closes noncollapse uniformly on every fixed positive regular slab,
with a lower constant chosen before the finite upper endpoint.

The missing theorem should add no consumer hypothesis and may be named
`early_ball_low` (name <= 20 chars).  For a smooth Ricci-flow solution on
`closedOpen 0 omega`, it must provide tau,kappa>0 such that for every flow time
t<=tau, every centre p, and every r>0 with r^2<=t,

  ofReal kappa * ofReal r ^ finrank <=
    Vol_{g(t)} {x | edist_{g(t)} p x < ofReal r}.

Constraints: do not use `HasLocallyConstantChartAt`; do not replace the result
by a new hypothesis, convergence predicate, or wrapper black box; work in
`DifferentialGeometry/`; RFreference is reference-only.  Existing relevant
published APIs include `MetricFamilySmoothOn.metricTensor_cont`,
`metricTimeBundleQuad_cont_of_metricFamilySmoothOn`, `metricUnitOn_compact`,
`edistOf_mono`, `edistOf_scale`, `edistBall_scale`, `volume_scale_apply`,
`VolumeComparison.exists_edist_vol`, the local Bishop comparison in
`Geometry/Comparison/Volume/BishopLocal.lean`, and the conditional compact
uniform injectivity-radius theorem in
`Geometry/Comparison/InjectivityRadius.lean`.

Three routes have not yet closed: (1) metric equivalence lacks a theorem giving
setwise Riemannian-volume domination; (2) pointwise fixed-centre small-ball
bounds cannot be finite-subcovered uniformly at arbitrarily small radii; (3)
local Bishop comparison retains a centre-dependent analytic/injectivity radius,
while the compact uniform injectivity theorem requires lower semicontinuity not
yet produced from joint exponential-map regularity.  Please decide which route
actually closes with the published APIs, identify the first genuinely missing
producer if none closes, and give an exact minimal statement/proof normal form
for that producer.  Prefer scalar/chart or already-realized metric objects;
avoid whole varying-fibre tensor equalities.
```

## 2026-07-23 post-merge positive-start half-open theorem

`NoncollapseOpen.lean` now proves `noncollapse_after`.  This removes the finite
upper-endpoint limitation from the positive-time route on a half-open
`closedOpen 0 omega` flow interval: after any fixed positive start time, one
gets a uniform noncollapsing constant for all later carrier times below a fixed
radius.  The proof chooses a finite auxiliary endpoint below `omega` around the
queried time and calls `w_span_uniform`, whose W lower constant is independent
of that endpoint.

Focused verification and module artifact refresh passed.  The endpoint
frontier is now sharper: the final all-carrier `NoLocalCollapsing` assembly
only needs the genuine initial-boundary producer `early_ball_low`, plus the
routine min-constant case split with `noncollapse_after`.  `NoLocalCollapsing`
and `ham3_noncollapse` remain theorem-level 0% until that initial-time volume
producer is proved.

## 2026-07-23 initial-time frontier isolated

`EarlyBall.lean` now records the remaining initial-time Perelman adapter as
`early_vol_low`, but the actual `sorry` frontier has been moved lower to
`Geometry/Comparison/Volume/FamilySmallBall.lean` as
`VolumeComparison.family_vol_low`.  That lower statement keeps the real
geometric content visible: short time, every centre, every radius under the
fixed scale, and the condition `r^2 <= t` coming from the backward parabolic
cylinder.  It is left as the single `sorry` frontier because the existing APIs
still do not provide a compact-uniform small-ball volume theorem.

The same file also adds `early_ball_low`, the checked adapter from the raw
volume bound to flow-ball kappa noncollapsing, and `no_local_open`, the
all-carrier assembly from `early_ball_low` plus the positive-time theorem
`noncollapse_after`.  The assembly itself is routine: split at the early-time
threshold, use `IsRmControlled` only to recover `r^2 <= t` in the early case,
use `noncollapse_after` in the positive-time case, and take the minimum kappa.

Honest accounting: `family_vol_low` is theorem-level **0%** and remains the
actual producer blocker.  `early_vol_low`, `early_ball_low`, and
`no_local_open` are checked relative to that lower frontier.  The endpoint
`NoLocalCollapsing` source assembly is now approximately **98%** structurally,
but theorem-level completion remains **0%** until `family_vol_low` is proved
without `sorry`.  `ham3_noncollapse` therefore remains theorem-level **0%**.

Verification note: `FamilySmallBall` and `EarlyBall` focused checks pass, and
their module artifact refreshes pass.  The umbrella focused check currently
stops before these files on a missing unrelated spectral artifact
`SpectralPointwiseFlowDeriv.olean`; this is a stale-artifact/import-chain issue,
not a local Perelman proof error.

## 2026-07-23 scalar tail and endpoint closure

The two earlier blockers are both closed.

First, `VolumeComparison.family_vol_low` is proved by the fixed-parametrization
finite-cover route, and `early_vol_low`, `early_ball_low`, and
`no_local_open` are all checked. Second, the actual entropy chain did not need
the deferred arbitrary-valence Weyl theorem: its nine uses were all rank zero.
`ScalarWeyl.scalar_eigen_tail` now proves exactly that input from scalar
point-evaluation Sobolev control and a finite Bessel/reproducing-kernel
combination. Six consumers in `ConjGalerkinClassical` and three in
`ConjGalerkinOn` have been rewired, with no new assumptions.

The complete `EarlyBall` dependency refresh passed. Axiom audits for both
`scalar_eigen_tail` and `no_local_open` contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. Therefore the
original-flow `NoLocalCollapsing` theorem is theorem-level **100%** and its
dedicated machinery is **100%**. This is one completed producer inside the
larger Hamilton/HCG program; the unconditional HCG compactness endpoint remains
theorem-level **0%**, and whole-project HCG machinery remains conservatively
about **60%**.

The Hamilton consumer is now closed as well: `ham3_noncollapse` applies
`no_local_open` to the actual maximal-flow package and then uses the existing
rescaling adapter `ham3_noncollapse_of`.  Its focused check passes, and its
axiom replay likewise reports only `propext`, `Classical.choice`, and
`Quot.sound`.  Thus `ham3_noncollapse` is theorem-level **100%** with
dedicated machinery **100%**; this does not change the still-open
`ham3_cgh_limit` or the unconditional HCG endpoint from **0%**.
