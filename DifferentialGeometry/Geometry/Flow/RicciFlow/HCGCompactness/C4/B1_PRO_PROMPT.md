# GPT Pro consultation prompt: B1 uniform quantitative inverse-exp radius

You are consulting on the live Lean repository at
`E:\testdifferential-geometry`, **branch `short-time-existence`**.  Base every
claim on that branch's current files.  Do not answer from `main`, another
checkout, an old commit, or remembered Mathlib APIs.  This branch contains the
current Step-C atom package, common-domain work, and the now-complete conditional
Step-D assembly.

We are formalizing MSM135 Chapter 4, Steps B/C, to construct the honest
`StepB1RawInput` consumed by `stepB1_of_raw`, `directed_of_b1`, and the checked
Step-D theorem `compactness_of_b1`.  The conditional compactness endpoint itself
is still 0% proved because no theorem yet constructs `StepB1RawInput` from
`MetricCompactnessInputs` and the concrete C-track data.

Please consult on the smallest mathematically honest route from the checked
pointwise inverse-exp branch to the sequence-uniform quantitative branch scale
needed by the current global-sigma B/C design.  Do not add a consumer-side
hypothesis that merely renames the missing radius, inverse branch, root
equation, or Hessian input, and do not resurrect the false theorem deriving B1
from properness alone.

## Checked live state

- `B1_JOIN_HANDOFF.md` is the running source of truth.
- `StepCAtoms.lean`, `StepCAtomConv.lean`, `StepCAtomJoin.lean`, and
  `StepCAtomPackage.lean` provide the finite-hat atom/weight package and one
  strict subsequence with the required convergence data.
- `StepCCmDomain.lean` provides the actual selected center, compact pinned-root
  gluing, subtype continuity, injectivity-based agreement, and the conditional
  `centerReadout_zero` producer.
- `exists_diagInvDom_inf` and `exists_readoutDom_inf` provide one genuine open
  inverse/readout domain carrying all differentiability orders for the existing
  `diagExpInv` branch.
- `exists_chartExp_jointContDiffOn_infty` gives one fixed phase ball on which
  the joint forward chart-exponential map is `C^infty`.
- `exists_readoutEBall` extracts a finite positive Riemannian extended radius
  for each fixed `(M, g, p)`.  `centerPairs_lt_of`, `centerPairs_lt_le`, and
  `centerPairs_lt` prove the local containment ledger; in particular
  `dist p q <= R` and `R + 2*r < δ` place the selected center and every point in
  the readout domain, with the finite-hat application taking `R = 4*lambda`.
- `exists_halfSqDist_md`, `expDiffeoRadius`, `expDiffeo_mem_of_lt`, and
  `diagInv_eq_normal_lt` provide the pointwise differentiability and
  intrinsic/realized inverse agreement once their source and smallness
  hypotheses are established.
- The independent book-scale Hessian/Neumann producer is still open;
  `CmHessianBoundInput.toInv` is only a projection from that input.
- `C4/StepDAssembly.lean` now proves `compactness_of_b1`; D6 is not the blocker.

## Exact frontier

The qualitative all-order domain and the local containment inequalities are
complete.  The extracted radius is `δ(k, alpha) > 0` for each fixed live center;
no theorem proves `inf_{k,alpha} δ(k,alpha) > 0`.

The current inputs cannot imply that statement:

1. `NormalCoordMetricBoundInput.metricC` is uniform, but `radius k x` has only
   pointwise `radius_pos`, with no positive floor and no compatibility field
   tying it to `decay` or `expMapC2Radius`.  The radius can be shrunk by a factor
   tending to zero while preserving every field.
2. `ExpInverseDerivBoundInput.r1` controls fixed-center transition derivatives
   in the input variable; it does not control the moving-base derivative of
   `chartedDiagExp` or the target of its inverse branch.
3. The private `diagExpIFT` uses qualitative
   `ContDiffAt.toOpenPartialHomeomorph` in arbitrary `extChartAt`/tangent charts.
   Existing quantitative data are in normal coordinates, with no uniform atlas
   chart control, so the target radius of this chosen branch is not recoverable
   from the current records.

Mathlib already has `ApproximatesLinearOn.toOpenPartialHomeomorph` and
`ApproximatesLinearOn.closedBall_subset_target`.  The suspected smallest missing
producer is a project-native uniform normal-coordinate statement of the form

```lean
ApproximatesLinearOn normalChartedDiagExp (unipotentCLE E)
  (Metric.ball 0 R) c
```

with `R > 0` and `c < ‖(unipotentCLE E).symm‖₊⁻¹` independent of `k` on live
centers, derived from a uniform radius floor plus metric/Jacobi/ODE estimates.
The existing `diagExpIFT` would then need to be built or identified from this
explicit branch.  A separate quantitative inverse does not automatically
enlarge the target of the current chosen branch.

A logically different option is to use pointwise radii at each fixed index,
take finite minima over live hats, and redesign the subsequence/diagonal
construction.  This solves fixed-index containment only; it must still produce
the eventual all-`k` package demanded by `StepB1RawInput`.

## Consultation questions

1. Is the global-sigma route mathematically/book-faithfully preferable here, or
   can a fixed-index finite-minimum plus diagonal/eventual construction really
   satisfy the exact `StepB1RawInput` quantifiers without a uniform radius?
2. If the global route is retained, what is the weakest honest extension of
   `NormalCoordMetricBoundInput` that expresses the radius floor already
   guaranteed by MSM135/[H6], without adding the desired branch radius itself?
3. Give the shortest sequence of project-native quantitative lemmas from
   `metric_equiv`/`metric_deriv` to a uniform derivative-deviation estimate for
   the normal-coordinate geodesic phase flow, and then to the
   `ApproximatesLinearOn normalChartedDiagExp` statement above.
4. Show how to construct or refactor the existing `diagExpIFT`/`diagExpInv` from
   that explicit quantitative branch so its target contains a stated ball and
   no second-branch uniqueness gap remains.
5. State the exact final radius theorem needed to combine with
   `centerPairs_lt_le`, `SigmaScaleField`, and the finite-hat bound
   `4*lambda + 2*r`, and identify the smallest independent Hessian/Neumann
   frontier left afterward.

## Forbidden routes

- No new `sorry`-backed wrapper or polished assumption equivalent to the target.
- No `CenterInput` on the whole configuration vector space or an ambient
  neighborhood of simplex-boundary weights.
- No dead-slot geometry requirements before stabilization.
- No second unrelated inverse branch unless its equality with `diagExpInv` is
  proved on the exact common domain.
- No claim that the checked conditional B1 or D6 consumers prove the textbook
  B1 theorem or `MetricCompactnessInputs.metricCompactness`.

Acceptance criterion: the proposal must either produce a genuinely
sequence-uniform explicit target-ball radius for the existing inverse/readout,
or give a complete replacement of the global-sigma architecture that reaches
the exact eventual all-`k` `StepB1RawInput` quantifiers.  It must not treat
pointwise positivity, a fixed-index finite minimum, or a renamed consumer input
as the missing theorem.
