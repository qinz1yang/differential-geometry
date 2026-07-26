# `ConjGalerkinClassical` status

## 2026-07-16 compact-interior coefficient jet mass

`galLimExt_coeff` and `galLim_jet_mass` are proved and focused verification is
green.  On one positive interior interval, every limiting rank-zero spectral
coefficient is smooth on compact subintervals and every time jet at every
natural Sobolev order has a single summable majorant uniform over that compact
subinterval.

The proof first uses `galLimExt_smooth` at a sufficiently high spatial order,
commutes the scalar coefficient continuous linear map with the iterated time
derivative, and then applies the rank-generic `mass_le_of_compact`.  The
negative tail is produced from the closed-manifold eigenvalue counting API;
no consumer regularity assumption and no whole-Hom equality is introduced.

Honest dependency accounting: the local theorem body contains no `sorry`, but
`weyl_eigenvalue_counting_bound_of_closed` currently depends on the existing
project `sorry` in `ShortTime/WeylEigenvalueCountingBound.lean`.  Therefore the
full dependency chain is not yet globally sorry-free.

`galLim_jet_mass`: theorem **100%**, dedicated machinery **100%**.  Rank-zero
joint scalar reconstruction and `heatpot_of_gallim` remain separate theorem
frontiers at **0%**.  Classical conjugate-heat dedicated machinery is about
**90%**; whole HCG machinery remains conservatively about **59%**, and every
HCG endpoint theorem remains **0%**.

## 2026-07-16 classical heat-potential closure

The classical reconstruction route is now closed.  `galLim_slice_cc` builds,
for each time slice, one genuine smooth rank-zero representative realizing all
natural spectral Sobolev orders.  `galLim_initial`, `galLim_joint_cont`,
`galLim_joint_top`, and `galLim_slice_pos` provide the initial value, endpoint
continuity, positive-time joint smoothness, and smooth spatial slices.

`galLim_pde` proves the fully pointwise original-time equation.  Its proof
differentiates the scalar series with `scalarSpec_d1`, identifies the derivative
coefficientwise with the lifted Galerkin velocity, and realizes the three
velocity arms by `scalarLapHs_core`, `lapDiffHs_core`, and `scalarPotHs_core`.
The final scalar normalization uses `rawLap_cc_scalar`, `scalarLapDiff_eq`, and
`scalar0_smul_cc`; no whole-tensor equality, whole-Hom equality, global frame,
or new consumer assumption is used.

`heatpot_of_gallim` packages these producers into a genuine `IsHeatPotOn` for
`reverseFamily (flowG S) T` on a nontrivial closed interval.  The final interval
is strictly inside the smooth/PDE windows, so the upper endpoint has a smooth
spatial slice as required by the structure.  Focused verification passes
without warnings.  The route still inherits the existing
`WeylEigenvalueCountingBound.lean` `sorry`; the new theorem bodies contain no
local `sorry`.

Honest accounting: `galLim_pde` and `heatpot_of_gallim` are each theorem-level
**100%**, and their dedicated classical conjugate-heat machinery is **100%**.
Perelman's no-local-collapsing theorem and `ham3_noncollapse` remain endpoint-
level **0%**; their broader dedicated entropy/noncollapse machinery is about
**52%**.  Whole HCG machinery is conservatively about **60%**.

## 2026-07-16 unconditional classical existence

`heatpot_exists` now composes `scalar_gal_subseq` with
`heatpot_of_gallim`.  Thus every smooth rank-zero initial tensor produces an
actual classical heat potential on a nontrivial reversed-time interval, with
the exact scalar initial trace.  `conj_heat_exists` then applies the existing
time-reversal bridge and produces an `IsConjHeatOn` solution with the exact
terminal trace.  Neither theorem assumes Galerkin limit data from its caller.

Focused verification passes without warnings.  The target theorem bodies have
no local `sorry`; as above, the full construction still inherits the existing
Weyl-counting `sorry`.  `heatpot_exists` and `conj_heat_exists` are each
theorem-level **100%**, and classical conjugate-heat existence machinery is
**100%**.  Positivity and unit-mass packaging remain separate producers, and
the current mass-conservation API still asks for global regularity stronger
than the interval-local solution package.  Perelman no-local-collapsing and
`ham3_noncollapse` remain theorem-level **0%**; entropy/noncollapse machinery
is about **54%**, and whole HCG machinery is conservatively about **60%**.

`gallim_nonneg` now intersects the classical existence interval with the new
`conjCoeff_bound` interval, restricts `IsHeatPotOn` through its canonical
`mono` theorem, and applies the existing weak maximum principle.  Hence every
nonnegative smooth scalar initial tensor produces a nonnegative classical heat
potential, without assuming a coefficient bound at the consumer.  Focused
verification passes.  `gallim_nonneg` is theorem-level **100%**; strict
positivity and unit mass remain separate, and no noncollapsing endpoint is yet
proved.

## 2026-07-16 positive unit-mass heat potential

The interval-local mass route is now closed without adding the old global
`MetricFamilyRegularAt` or `FunctionRegularAt` assumptions to consumers.
`heatpot_mass_deriv` directly applies `first_var_joint`: reverse-time chart
Gram smoothness comes from `IsSolutionOn.smoothMetric.frameCompSmooth`, the
reverse volume trace is `+2 R` by `metricDerivAt` and the canonical volume
trace API, and the heat equation cancels the scalar term before Green's
identity kills the remaining Laplacian integral.

`heatpot_mass_eq` shrinks the interval using only regularity of the terminal
time, restricts the genuine `IsHeatPotOn`, and proves closed-interval mass
constancy. The moving integral is continuous by `integral_family_cont`; its
zero derivative makes it constant on the open interior, and
`Set.EqOn.of_subset_closure` extends that equality to both endpoints.
`gallim_unit_pos` then combines `unit_init_or_empty`, `gallim_pos`, and this
mass theorem. Thus either the manifold is empty or there is a strictly
positive genuine reversed heat potential whose moving Riemannian mass is one
at every time of a nontrivial closed interval.

Focused verification is green without warnings, and targeted module
verification is green. These three theorem endpoints and their dedicated mass/positivity
packaging are each **100%**. This completes the positive unit-mass
conjugate-heat input, but it does not prove any noncollapsing conclusion:
Perelman's no-local-collapsing theorem and `ham3_noncollapse` remain
theorem-level **0%**. Their broader dedicated entropy/noncollapse machinery is
now about **58%**, while whole HCG machinery remains conservatively about
**60%**. The construction still inherits the previously recorded
Weyl-counting `sorry`; the new theorem bodies contain no local `sorry`.

## 2026-07-17 Galerkin endpoint derivatives

The retained Galerkin route now reaches spatial derivatives at the reverse-time
endpoint without constructing a dependent tensor-valued limit section.
`galLimExt_zero` identifies every Sobolev realization at time zero with the
prescribed smooth initial tensor. The fully applied rank-zero bridge
`covGrad0_apply`, together with the fibre Parseval estimate
`sq_unit_eval_le`, converts the dimension-three `H3` pointwise covariant-gradient
bound into a scalar directional-derivative estimate whose constant is
independent of spectral support.

`galLim_d_zero` proves convergence for every fixed point and tangent vector.
`galLim_d_joint` upgrades this to genuine joint `(s,x)` continuity in the
actual `chartBasisVecFiber` frame on its trivialization base set. Both theorems
passed focused verification. No global frame, whole-Hom equality,
`HasLocallyConstantChartAt`, or extra consumer convergence assumption is used.

The next finite inverse-Gram contraction, `galLim_grad_zero`, has been written
to turn those scalar components into moving gradient-square endpoint
continuity. Its focused verification is temporarily unobserved because the
shared volume lane removed `RadialGronwall.olean` while refreshing its claimed
`RadialGram` dependency; the check stopped at that missing import before
elaborating this theorem. The exact next action is to rerun the focused check
after that upstream refresh finishes, then combine this endpoint theorem with
the verified positive-time `gradSq_joint` route and feed the resulting joint
scalar continuity to `integral_family_cont`.

Honest accounting: `galLimExt_zero`, `galLim_d_zero`, and `galLim_d_joint` are
each theorem-level **100%**. `galLim_grad_zero` is not counted as proved until
the blocked check passes (**0% theorem; source proof assembled**). The finite-
horizon W comparison theorem is still unstated/unproved (**0%**); its dedicated
endpoint-continuity machinery is about **65%**. Perelman
`NoLocalCollapsing` and `ham3_noncollapse` remain theorem-level **0%**; broader
entropy/noncollapsing machinery remains about **97%**, and whole HCG machinery
about **60%**.

## 2026-07-17 Closed-interval gradient square

The endpoint contraction is now fully verified. `galLim_grad_zero` reconstructs
the intrinsic squared gradient from finitely many scalar directional
derivatives and the inverse chart Gram matrix. Its final normal form is fully
applied and scalar-valued; no dependent gradient section or whole-Hom equality
is introduced.

`galLim_grad_cont` is also verified. It combines the zero-endpoint theorem with
the existing positive-time `galLim_joint_top` and `gradSq_joint` route, returning
a nontrivial shortened interval on which the moving squared gradient is jointly
continuous. The public theorem does not require a supplied regular-time window:
it derives the needed smaller window from `T.2`. Internally,
`galLim_grad_zero` now separates the full Galerkin interval from the smaller
regular metric interval, so no stronger consumer assumption was hidden.

Honest accounting: `galLim_grad_zero` and `galLim_grad_cont` are each
theorem-level **100%**. The Galerkin endpoint-continuity machinery is about
**85%**; the finite-horizon W comparison theorem remains theorem-level **0%**
until its moving-integral proof verifies. Perelman `NoLocalCollapsing` and
`ham3_noncollapse` remain theorem-level **0%**; broader entropy/noncollapsing
machinery remains about **97%**, and whole HCG machinery about **60%**.

## 2026-07-19 exact closed-interval adapters

`galLim_slice_cc` is now public so exact-interval reconstruction can reuse the
canonical smooth slice instead of duplicating its spectral proof.
`heatpot_mass_on` is the exact-interval mass conservation theorem: given an
already constructed `IsHeatPotOn` object and reflected regularity on the
caller-supplied closed interval, it proves that every slice has the same mass
as the zero slice.  It does not choose a smaller lifespan.

Both changes are source-complete and contain no local `sorry`; they remain
theorem-level **0%** until the pending upstream refresh permits a focused file
check.  Their dedicated source is approximately **95%**.

## 2026-07-23 scalar spectral cutover

All six rank-zero `EigenvalueTailSummable` consumers now use the proved
`IntrinsicSpectral.scalar_eigen_tail`.  The direct import of
`ShortTime.WeylEigenvalueCountingBound` has been removed, so this module no
longer consumes the deferred generic tensor local-Weyl theorem.

Focused verification passes without warnings after also dropping the unused
positive-dimension instance from the three mass-conservation theorem
signatures.  No consumer assumption was added.  The scalar producer's axiom
audit contains only the standard foundational axioms and no `sorryAx`.
This section supersedes the earlier generic-Weyl dependency accounting:
`galLim_jet_mass` and its scalar spectral dependency chain are theorem-level
**100%** with dedicated machinery **100%**.  The downstream
`NoLocalCollapsing` and `ham3_noncollapse` producers are now also closed; their
status is tracked in the Perelman and Hamilton notes.
