# Pro consultation prompt: smooth quantitative normal endpoint

Work against `E:\testdifferential-geometry` on the **`short-time-existence`
branch**, Lean/Mathlib v4.29.0.  Do not answer from `main`, another checkout, an
older commit, or remembered Mathlib APIs.  If the checkout cannot be mounted,
separate names supplied below as checked from any API names you are only
proposing.

## End goal

The HCG Step-B/C lane now has a quantitative retained-endpoint
`OpenPartialHomeomorph` with a sequence-uniform source ball and explicit target
ball.  To make that branch the branch consumed by the center/readout API, we
need the retained endpoint to be jointly `C^infinity` in the initial phase point
on the same open source ball.  A checked generic theorem then makes the inverse
of that exact partial homeomorphism `C^infinity` on its full target.

The requested answer is the shortest honest Lean producer for that forward
smoothness.  Do not solve the problem by assuming smoothness or by returning to
the pointwise qualitative `diagExpIFT` germ.

## Checked state

All names in this section are focused-check green on the branch.

- `NormalPhaseRealization.normalPhase_contDiff` proves the autonomous normal
  phase field is globally `ContDiff Real infinity`.
- `NormalPhaseSym.exists_normal_biflow` gives one family
  `Phi : (E x E) -> Real -> E x E` on `[-1,1]` with:
  initial identity, per-orbit continuity and ODE derivatives, phase-box
  confinement, and
  `ApproximatesLinearOn (fun z => (z.1, (Phi z 1).1)) freeDiag` on a common
  closed ball.
- `NormalPhaseEndpoint.exists_normal_diag` uses that same family and proves the
  exact square

  ```text
  normalPair (e z) = diagExp (normalTangent z)
  ```

  while retaining the quantitative source, target-ball containment, and radius
  formula.
- `PhaseFlow.exists_quant_inv` constructs `e` with
  `e.source = ball 0 q` by
  `ApproximatesLinearOn.toOpenPartialHomeomorph`.
- Newly checked `PhaseFlow.quantInv_smooth` proves, for a finite-dimensional
  Banach space, that if the forward map `f` is `ContDiffOn Real infinity f s`,
  then the inverse of this exact quantitative partial homeomorphism is
  `ContDiffOn Real infinity` on its target.  It does not choose a second branch.
- `diagExpInv_diagExp` gives only a pointwise germ for the older generic
  `diagExpInv`; it cannot yield a sequence-uniform source radius.

## Exact missing theorem

The desired producer is semantically:

```lean
theorem normalDiag_smooth
    ...
    (Phi : (E x E) -> Real -> E x E)
    (hPhi0 : ...)
    (hPhiODE : ...)
    (hPhiBox : ...)
    ... :
    ContDiffOn Real infinity
      (fun z => (z.1, (Phi z 1).1))
      (Metric.ball (0 : E x E) q)
```

Please improve the hypotheses and placement rather than treating this exact
sketch as fixed.  The theorem name must be at most twenty characters.

## Audit of apparent routes

### Route A: strengthen the fenced Picard family

`PhaseFlow.exists_fenced_Icc` currently selects Picard fixed points and exposes
only per-orbit data and confinement.  Mathlib's
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
can provide a family uniformly Lipschitz in the initial point, enough to package
an `Analysis.ODE.Flow.IsLocalFlow` after the anisotropic scaling.

The project has `IsLocalFlow.contDiffOn_top`, but its explicit nesting theorem is
short-time: it requires `M * T_mid < 1`.  The source file also records that the
current `IsLocalFlow` API has no time-subdivision/semigroup structure.  It is not
clear how to reach the retained time `1` without adding such a composition API.

### Route B: recover smoothness from the endpoint square

One could express the retained endpoint through `normalTangent`, intrinsic
`diagExp`, and the inverse normal coordinates on the named `expMapC2Radius`
ball.  `normalExpPD` / `normalBallDiffeo` are `C^infinity`, and the relative
radius profile controls their domains.  However the current public total-space
theorem is `diagExp_contMDiffAt_zero`, only at the zero section.
`diagExp_variation_contMDiffAt_of_smallField` explicitly says it is a
curve/field theorem, not total-space smoothness at an arbitrary small tangent.
So this route appears to require a new moving-base off-zero `diagExp`
smoothness producer.

### Route C: use the old qualitative branch

This is rejected.  `ContDiffAt.toOpenPartialHomeomorph` makes arbitrary local
choices; openness gives a radius only after fixing `(k,x)`.  It cannot prove the
uniform target containment needed by `StepB1RawInput`.

## Questions

1. Which of Route A or Route B is the shortest in the live dependency graph?
   Identify any existing theorem that removes the apparent missing step.
2. Give exact, dependency-safe theorem statements and a proof skeleton.  Mark
   every recalled/unverified API name.
3. If Route A is best, specify the smallest time-shift, restriction,
   composition, or semigroup lemma needed to propagate local smooth dependence
   from time `0` to time `1`, and show how the fenced family supplies it.
4. If Route B is best, specify the smallest off-zero moving-base `diagExp`
   smoothness theorem and show how its domain follows from the already checked
   phase-box and `NormalRadiusProfile` inequalities.
5. State the final theorem that combines forward smoothness with
   `quantInv_smooth`, so the exact quantitative branch has a `C^infinity`
   inverse on its explicit target.

## Constraints

- No smoothness assumption that merely restates the missing producer.
- No naked `branchRadius` or uniform containment assumption.
- No finite minimum at a fixed sequence index.
- No replacement of the checked bilateral family by an unrelated flow unless
  equality with it is proved on the whole consumed source.
- No second totalized inverse branch.
- Keep generic `diagExpInv` stable as a compatibility API; the HCG lane may
  select the transported quantitative branch.
- The `StepB1RawInput` producer and textbook B1 theorem remain unstated and
  unproved, both 0%.
