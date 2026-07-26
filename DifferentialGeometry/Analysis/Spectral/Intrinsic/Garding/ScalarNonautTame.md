# Scalar nonautonomous tame coefficients

## 2026-07-13 applied coefficient layer

The fixed-background scalar decomposition is now represented by genuine
`SmoothCcTensor` coefficient fields.  `traceCast` retags the moving cometric
trace without changing its section, `scalarTraceCoeff` is the moving-minus-
fixed principal coefficient, and `connTraceCoeff` traces
`connDiffSection h q` with the moving cometric.  `scalarLapDiffCc` combines the
second-order and first-order arms with the sign from `lap_sub_conn`.

The read-off theorems `traceCast_apply`, `scalarTrace_apply`, and
`connTrace_apply` were checked in fully applied scalar normal form.  They never
ask Lean to identify whole Hom-bundle model values.  `scalarLapDiff_apply`
assembles those read-offs for the complete coefficient expression.  The
complete file passes focused verification.

This file does not yet prove `scalar_crit_tame`.  In particular, the applied
decomposition is not being reported as an equality with the external scalar
Laplacian on arbitrary Sobolev inputs; that realization remains supplied on the
finite core by `MetricLapDiffCore`.

## Exact analytic stop frontier

The rank-generic `appCc_jet_l2Sq_le`, `hsJet_le`, `hs_le_jet`, and the requested
covariant-gradient order-drop bridge provide a fixed-order proof route.  At a
fixed `k`, one can isolate the principal `(coefficient order, data order) =
(0,k)` term and obtain

```text
norm(A2 u in H^k)^2
  <= A(k) * K2(0) * norm(u in H^(k+2))^2
     + R(k) * norm(u in H^(k+1))^2.
```

The quantifier order can make `A(k)` independent of spectral support and of the
particular coefficient fields.  This is genuine progress, but it does not feed
the live all-order Galerkin consumer: that theorem requires one top coefficient
strictly below `2` simultaneously for every `k`, whereas this route supplies
`A(k) * K2(0)`.  A single time shrink does not control an unbounded family of
`A(k)` constants.

This is the fifth distinct route problem in the bootstrap audit.  The next
consult must decide between a direct covariant commutator/dissipation estimate
whose top coefficient is the order-zero ellipticity constant, moving the full
principal part to the left-hand side, or a different fixed-scale bootstrap that
still yields all orders on one fixed shorter interval.  Merely proving the
fixed-`k` operator-norm estimate and calling the existing all-order consumer
would be incorrect.

Honest accounting: `scalar_crit_tame` is not stated or proved (0%); its
dedicated machinery is about 55%.  `heatpot_of_maxreg` remains 0% with about
35% directly reusable machinery.  The classical moving conjugate-heat theorem
and Perelman no-local-collapsing endpoint both remain 0%; their dedicated
machinery is about 77% and 40%, respectively.  Whole HCG machinery remains
about 53%, with endpoint theorems at 0%.

## Direct dissipation consult -- 2026-07-13

The follow-up Pro consultation is recorded at
<https://chatgpt.com/g/g-p-6a05f8e7fb0881918ae46beec6dcd123-lean-pro-consult-handoff/c/6a55679f-4250-83e8-9f44-f3b67243e7ff>.
The prompt explicitly requested references to the GitHub branch
`liao9yuan/differential-geometry:short-time-existence`.  Pro could verify the
published non-autonomous engine there, but the named DeTurck, pairing, and
commutator files return 404 at that branch head; those claims were therefore
treated as local post-merge facts and checked against this worktree.

The corrected derivative count is decisive.  For
`P u = A^{ij} nabla_i nabla_j u`, the raw commutator with `1 - Delta` is third
order and contains `(nabla A) * nabla^3 u` and
`(nabla^2 A) * nabla^2 u`.  It is lower order only after balanced bilinear
integration by parts.  Consequently `cc_commutator_one` is not the first
producer.  The chosen order is:

1. divergence/flux factorization (`scalar_flux_split`);
2. the small principal pairing (`cc_principal_pair`);
3. the balanced commutator pairing (`cc_comm_pair`);
4. moving dissipation (`cc_energy_diss`);
5. the generic coefficient-one Dirichlet gap only in final assembly.

The two generic algebraic precursors are now focused-verified: `appCc_assoc`
and `covDiv_appCc`.  The divergence proof must reuse `appCc_assoc`; repeating
the same whole-Hom extensionality inside the consumer hits a deterministic
kernel timeout.

The exact live mathematical/API frontier is now the scalarized metric/cometric
naturality producer `trace_slot_flat`, followed by the coefficient-to-flux
factorization

```text
scalarTraceCoeff q h
  = trace_q (slotExtend (scalarFluxCoeff q h)),
```

where `scalarFluxCoeff` is the covector endomorphism representing the moving
inverse-cometric difference.  `trace_slot_flat` is valid for every covariant
rank-two tensor, so it requires neither Hessian symmetry nor a consumer-side
assumption.  Its cheap proof normal form is a fully applied scalar double-frame
sum; no whole-Hom equality should be elaborated.  Once it is proved,
`trace_retag_eq` and `scalar_trace_factor` are field-level adapters, and
`scalar_flux_split` follows from `covDiv_appCc` by algebra.

Honest accounting: `scalar_crit_tame` remains unstated/unproved (0%); its
dedicated machinery is now about 58%.  `heatpot_of_maxreg`, the classical
moving conjugate-heat theorem, Perelman no-local-collapsing, and
`ham3_noncollapse` all remain theorem-level 0%; their dedicated machinery is
about 35%, 77%, and 40% respectively.  Whole HCG machinery remains about 53%,
with endpoint theorems at 0%.

## Scalar flux producer -- 2026-07-13

The pointwise producer `trace_slot_flat` is now proved and focused-verified.
Its field adapters `trace_retag_eq`, `traceCast_self`, and
`scalar_trace_factor` also pass complete focused verification.  The generic
linearity lemmas `slotExtend_sub` and `appCcRS_sub_right` were moved to their
canonical operator-field modules and verified there.

`scalar_flux_split` has now been stated and proved by combining
`scalar_trace_factor` with the verified `covDiv_appCc` product rule and the
successor normal form for `iteratedCovGrad`.  The exact producer refresh and
the complete consumer focused check both passed.  The proof uses the named
successor equality directly; a broad `rw` was rejected because it first
expanded the nested `nabla U` occurrence and left the wrong normal form.

The exact live frontier is now the small principal pairing
`cc_principal_pair`, followed by the balanced commutator pairing.  The raw
commutator is not being treated as lower order before integration by parts.

Honest accounting: `scalar_crit_tame` remains unstated/unproved (0%); its
dedicated machinery is about 61%.  `heatpot_of_maxreg`, the classical moving
conjugate-heat theorem, Perelman no-local-collapsing, and `ham3_noncollapse`
remain theorem-level 0%; their dedicated machinery is about 35%, 77%, and 40%
respectively.  Whole HCG machinery remains about 53%, with endpoint theorems
at 0%.

## Principal pairing -- 2026-07-14

The scalar flux evaluation is now connected to the intrinsic cometric-slot
operator, and `cc_principal_pair` is proved and focused-verified.  Its only top
coefficient is the order-zero metric perturbation
`delta / (1 - delta)`; the proof uses the negative-sign slot pairing estimate
and the scalar Green identity.  It adds no consumer assumption and does not
depend on spectral support.

The live audit also rules out reusing the raw commutator theorem in
`ConnLapCommutatorCoefficientTame`: that theorem is third order, is specialized
to rank-two DeTurck data, and assumes a resolvent-family presentation.  The
closest correct route is the private balanced transport chain in
`DeTurckPrincipalArmEnergyPairing`.  Its endpoint compares the transported
Dirichlet pairing with the top slot pairing and bounds the difference by
`C * J_n * J_(n+1)`.

The exact frontier is therefore to extract that endpoint at arbitrary base
covariant rank (or at least rank zero), using the already-public self-adjoint
`oneMinusConnLap` algebra, curvature/divergence commutator identities, and the
generic negative cometric-slot estimate.  Once available, `cc_comm_pair` is a
small scalar adapter; the raw commutator remains deliberately unused.

Honest accounting: `scalar_crit_tame` remains unstated/unproved (0%); its
dedicated machinery is about 65%.  `heatpot_of_maxreg`, the classical moving
conjugate-heat theorem, Perelman no-local-collapsing, and `ham3_noncollapse`
remain theorem-level 0%; their dedicated machinery is about 35%, 77%, and 40%
respectively.  Whole HCG machinery remains about 53%, with endpoint theorems
at 0%.

## Balanced scalar dissipation -- 2026-07-14

The missing passenger-slot transport is now a public, rank-generic producer.
`BalancedPairing` and `SlotTransportPairing` are focused-verified and their
targeted module refreshes pass.  The scalar adapters `cc_last_pair`,
`cc_comm_pair`, and `cc_energy_diss` are also proved and the complete
`ScalarNonautTame` file is focused-verified.  The top coefficient is exactly
`delta / (1 - delta)` and the commutator remainder is the product of the two
adjacent covariant-jet windows.  Constants are independent of spectral support.

The proof never estimates the raw third-order commutator.  It transports
`1 - Delta_nabla` through the bilinear pairing, telescopes the passenger slot,
and uses the existing HEq-to-rank-cast bridge only after the tensor has reached
the fully applied top pairing.  No new consumer assumption or local-chart
hypothesis was introduced.

The exact next analytic producer is the rank-generic coefficient-one
Dirichlet gap `cc_dirichlet_gap`.  The finite spectral core and generic
spectral-to-jet APIs already exist; after this gap, a scalar finite-combination
pairing adapter must identify the weighted Galerkin cross term with the proved
smooth pairing.  Near the frozen time, `metric_cp_tendsto` supplies arbitrary
metric smallness; fixing `delta = 1/4` will give the strict top-energy
coefficient required by the Galerkin consumer once the smallness-to-
`gFibreOpBound` adapter is applied.

Honest accounting: `cc_comm_pair` and `cc_energy_diss` are complete (100%).
`scalar_crit_tame` remains unstated/unproved (0%); its dedicated machinery is
about 72%.  `heatpot_of_maxreg`, the classical moving conjugate-heat theorem,
Perelman no-local-collapsing, and `ham3_noncollapse` remain theorem-level 0%;
their dedicated machinery is about 35%, 77%, and 40% respectively.  Whole HCG
machinery remains about 53%, with endpoint theorems at 0%.

## Full scalar Laplacian pairing -- 2026-07-14

The fixed-`(q,h)` first-order connection arm is now closed by
`cc_conn_pair`, a direct specialization of the rank-generic
`iterL_pair_jet_le`.  Its constant is independent of spectral support and its
remainder is the same product of adjacent covariant-jet windows as the
principal-arm estimate.

`cc_lap_pair` combines that absolute connection-arm bound with
`cc_energy_diss` and the subtraction in `scalarLapDiffCc`.  The resulting full
moving-minus-fixed scalar Laplacian pairing retains the exact principal
coefficient `delta / (1 - delta)` and adds only a support-independent adjacent-
window remainder.  This is a fixed-coefficient theorem: it deliberately makes
no time-uniform claim and introduces no new assumption.  Focused verification
of the complete file passes without warnings.

The remaining frontier is consumer-side: identify the finite spectral/Galerkin
cross term with this smooth pairing and combine it with the rank-generic
Dirichlet gap.  No new coefficient or commutator estimate is needed for that
step.

Honest accounting: `cc_conn_pair` and `cc_lap_pair` are complete (100%).
`scalar_crit_tame` remains unstated/unproved (0%); its dedicated machinery is
about 75%.  `heatpot_of_maxreg`, the classical moving conjugate-heat theorem,
Perelman no-local-collapsing, and `ham3_noncollapse` remain theorem-level 0%;
their dedicated machinery remains about 35%, 77%, and 40% respectively.  Whole
HCG machinery remains about 53%, with endpoint theorems at 0%.

## Scalar operator linearity -- 2026-07-15

`scalarLapDiff_add` and `scalarLapDiff_smul` now expose the actual real
linearity of `scalarLapDiffCc` in its scalar section.  They use the public
linearity of `appCc` and the iterated covariant gradient; no geometric
assumption or supplied operator is added.  Focused verification passes without
new warnings.

These are completed algebraic producers (**100%**) needed to bundle the
smooth-core A2 action as a `LinearMap`.  They are not the completed
`H^(m+2) ->L H^m` operator, which remains theorem-level **0%** until dense-core
extension and compatibility are checked.  Perelman no-local-collapsing and
`ham3_noncollapse` remain endpoint-level **0%**.
