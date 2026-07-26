# B1 moving inverse/root consultation

## Checked state

Route A's support-sensitive finite-stage configuration is closed.  In
`StepCStageFill.lean`, `HasSuppConvData.cfgSub_conv` gives arbitrary-reindexing
`C^infinity` convergence of the actual weights and smooth two-bump-filled
target tuple to the diagonal configuration.  `HasSuppConvData.pts_eq_ne` gives
one common finite tail on which every nonzero actual slot selects an old
`InterSlot` and the filler equals the raw two-transition target.  No weight
gluing, pointwise chart selector, subtype identification, whole-cage target
assumption, or endpoint-radius assumption is used.

The final theorem is already stated as `MetricCompactBase.exists_b1_raw` with
the unchanged `StepB1RawInput` target.  Its proof remains theorem-level 0%:
the real integer-radius diagonal must be constructed before the dependent
`StepB1RawInput.comparison` record can honestly be opened.

## Resolved architecture and current stop

The consultation decision is resolved.  Do not begin with a monolithic C4
inverse-convergence theorem.  The canonical order is generic `C^infinity` ODE
stability in `Analysis/ODE`, metric-to-geodesic-phase specialization in
`Geometry/Exponential`, generic compact moving-root stability in
`Analysis/Calculus`, and only then a thin HCG inverse wrapper.  The center
application targets `invVelSum`; `chartCmEqnB_factor` is used only for zero-set
and fixed-stage identification.

The generic map-convergence API has been moved to `Analysis/Calculus` without
renaming declarations.  The proof-independent metric spray and
`normalGeodesicSpray_conv` are checked.  The exact low-level theorem
`MapCInfConvOnCompacts.ode_solutionAt` is now stated and typechecked with no
stage-family stay assumption, but its all-order compact-tube/variational-jet
proof is the earliest honest analytic frontier and remains one explicit
`sorry`.  Forward normal-phase endpoint convergence, compact moving-root
stability, selected inverse convergence, and `invVelSum` root convergence have
not yet been stated as proved producers.  The new proof-level question for this
frontier is recorded in `B1_ODE_STABILITY_CONSULT.md`.

## Historical consultation request (answered 2026-07-15)

```text
We need an architecture ruling for the first remaining analytic bridge in the
Lean Hamilton-Cheeger-Gromov compactness Step B/C producer.

Current checked state
---------------------

Route A is now implemented and focused-green.

1. `StepCStageFill.lean` contains the fixed 6/7 activity bump and 7/8 safety
   clamp, old-`InterSlot` finite totalization, actual stage weights and filled
   target tuple.
2. `HasSuppConvData.cfgSub_conv` proves, for arbitrary `kn, ln -> infinity`,
   `MapCInfConvOnCompacts` convergence of the full actual stage configuration
   to the diagonal configuration on each fixed source patch.
3. `HasSuppConvData.pts_eq_ne` gives one common finite tail: every arbitrary
   nonzero actual slot selects an old `InterSlot`, and the smooth filler equals
   the raw two-transition target there.
4. The canonical global `stageComparisonMap` is already defined independently
   of source charts and identified with a local center by unique global
   minimization plus zero-weight energy congruence.
5. `MetricCompactBase.exists_b1_raw` is already stated with the final unchanged
   `StepB1RawInput` target.  It has one honest `sorry`; the target theorem and
   concrete B1 producer remain 0% until the real master diagonal and analytic
   bridges exist.

Existing geometric APIs
-----------------------

- `StepBLocalMetrics.exists_metricLimit_normalCoord` returns, on one fixed open
  `U`, a subsequence, a smooth positive-definite `gInf`, and

    MapCInfConvOnCompacts U
      (fun n => normalCoordMetric ... n ...) gInf.

- `normalDiagAtFull` selects at every stage an
  `e_n : OpenPartialHomeomorph (E x E) (E x E)`.
- `IsNormalDiag.full_transport` provides the exact phase/diagonal-exponential
  identities, smoothness of `e_n` and `e_n.symm`, and a common closed
  `delta`-ball contained in every `e_n.target`.
- `DiagInvBranch.readoutDomInf` supplies all-order smoothness for one selected
  branch.
- `NormalBranchHessian.chartCmEqnB_factor` factors the branch center equation
  through `normalReadCLM` and `invVelSum`; `invVelSum_inv` gives its center
  derivative isomorphism.
- `existsCmExtensionB`, `cmExtB_contDiffOn`, and `cm_sol_cd` are fixed-stage
  implicit-center results only.

Live search found no convergence theorem for `e_n.symm`,
`DiagInvBranch.inv`, `diagReadout`, `invVelSum`, or `chartCmEqnB`.
`ApproximatesLinearOn` is only first-order.  `normalTotal` is a per-stage cutoff
extension and should not be made the convergence object.

The mathematical dependency appears to be:

  normal metric jets converge
    -> Koszul/Christoffel acceleration fields converge
    -> normal phase endpoint maps e_n converge on a fixed source ball
    -> inverse maps e_n.symm converge on a common target delta-ball
    -> diagReadout / invVelSum / chartCmEqnB converge
    -> center roots converge on one common parameter neighborhood.

Please decide the smallest correct Lean architecture and give exact theorem
signatures (all important quantifiers, fixed open/compact domains, subsequence
placement, and `MapCInfConvOnCompacts` conclusions) for the next producer chain.
In particular answer these questions:

1. Should `exists_diagInv_conv` be one HCG-specific theorem, or should we first
   prove forward phase-endpoint convergence and then apply a generic
   compact-graph moving-root/inverse theorem to
   `G_n(u,w) = e_n(u) - w`?  We would like to reuse the same generic theorem
   later for the moving center equation if that is genuinely smaller.
2. What is the minimum honest theorem from
   `MapCInfConvOnCompacts normalCoordMetric gInf` to convergence of the forward
   phase endpoint maps?  Identify any missing ODE smooth-dependence API and its
   canonical `DifferentialGeometry/Analysis` or `Geometry/Exponential` home.
3. What should the common-domain inverse theorem assume so that it derives,
   rather than accepts as a new endpoint input, a fixed target ball and uniform
   inverse control?  Is the existing common closed `delta`-ball plus compactly
   nested source balls sufficient?
4. After inverse convergence, should the center-equation producer target
   `invVelSum` first and obtain `chartCmEqnB` by `chartCmEqnB_factor`, or is a
   direct equation-convergence theorem smaller?
5. Give the exact generic moving-root theorem needed to obtain one relatively
   compact parameter neighborhood `W`, eventual smooth roots `Phi_n`, local
   uniqueness, and

     MapCInfConvOnCompacts W Phi PhiInf.

   State whether it can serve both the inverse-map step and the later center
   step without becoming an oversized parallel API.
6. Explain how to retain the cube-tail quantifier

     exists N, forall n k l >= N, ...

   and how the finite source-slot diagonal and later integer-radius master
   diagonal should be ordered.  Do not return to
   `eventually n, exists N_n, forall k l >= N_n`.

For each proposed theorem, classify the work as routine Lean packaging,
missing reusable API, or genuinely new analysis, and name the earliest honest
stop point if the chain cannot yet be proved.

Hard constraints
----------------

- Keep `StepB1RawInput` unchanged.
- Add no branch-specific field to `MetricCompactnessInputs`.
- Add no endpoint-radius assumption.
- Do not glue source-local limit weights or introduce a pointwise chart
  selector.
- Do not identify old and refined `InterSlot` subtypes.
- Do not impose whole-cage target containment.
- Do not identify the reverse stage comparison map with the exact inverse;
  `Function.invFunOn` remains the B1 reverse map.
- Do not manufacture an all-order numerical recurrence unless it is actually
  required; qualitative `C^infinity` convergence is preferred.
- Place reusable analysis at the lowest native `DifferentialGeometry` layer,
  with only thin HCG-facing producer theorems in C4.
```

## Accounting at the stop

- Route-A stage-filler/configuration machinery: checked, 100%.
- Proof-independent metric spray and `normalGeodesicSpray_conv`: checked, 100%.
- `MapCInfConvOnCompacts.ode_solutionAt`: statement/placement 100%; theorem
  proof 0%, with one honest `sorry`; dedicated all-order stability machinery 0%.
- Compact moving-root API, selected inverse convergence, `invVelSum` root
  convergence, and the all-pairs chart tail: 0%.
- Dedicated Step-B/B1 machinery: about 95%.
- Chapter 4 machinery: about 87%.
- Whole HCG machinery: about 57%.
- `MetricCompactBase.exists_b1_raw`: stated, proof 0% while its `sorry`
  remains.
- Concrete `StepB1RawInput`, textbook B1, and all compactness endpoints: 0%.
