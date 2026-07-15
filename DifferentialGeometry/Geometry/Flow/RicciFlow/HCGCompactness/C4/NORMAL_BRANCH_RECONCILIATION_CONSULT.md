# Pro consultation prompt: canonical quantitative moving-inverse branch

> **Disposition (2026-07-10):** the qualitative-germ containment route is not
> quantitatively recoverable from the private IFT choices.  The HCG lane will
> parameterize/select the transported quantitative branch and keep generic
> `diagExpInv` as a compatibility API.  `PhaseFlow.quantInv_smooth` has closed
> inverse smoothness conditional on forward smoothness of that exact branch.
> The remaining single producer and current consultation prompt are in
> `NORMAL_ENDPOINT_SMOOTH_CONSULT.md`.

Work against branch `short-time-existence` of the RicciFlower repository,
Lean/Mathlib v4.29.0, checkout `E:\testdifferential-geometry`.  If the checkout
is unavailable, reason from the exact checked state below and distinguish
verified API names from recalled Mathlib names.

## End goal

The HCG Step-B/C lane needs one sequence-uniform moving inverse-exponential /
readout branch on the relative normal scale.  It must feed the existing
center-of-mass and `StepB1RawInput` consumers without adding a naked
`branchRadius` assumption and without silently exposing two unrelated inverse
branches.

## Checked state

All declarations below are focused-check green; the relevant targeted module
builds also pass.

- `NormalRadiusProfile.floor_le_radius`, `floor_le_exp`, and the
  `mul_lambda_lt_*` lemmas provide the intended relative scale
  `ratio * mu(distance)` on the consumed exhaustion.
- `NormalPhaseSym.exists_normal_biflow` gives one common exact flow on
  `[-1,1]`, confined to the controlled phase box, with the forward retained
  endpoint `ApproximatesLinearOn PhaseFlow.freeDiag`.
- `NormalPhaseInverse.exists_normal_q` chooses a positive phase radius satisfying
  the fence, acceleration, and strict quantitative-IFT thresholds.
- `PhaseFlow.exists_quant_inv` gives an `OpenPartialHomeomorph e` with explicit
  source ball, explicit positive target-ball containment, and an exact radius
  formula.
- `covAlong_natCrossAt`, `geodesicOn_mapLocal`, `normalGeo_map`, and
  `geo_end_eq_intr` close arbitrary-velocity cross-model naturality and endpoint
  uniqueness.
- `NormalPhaseEndpoint.exists_normal_diag` uses the *same* bilateral flow and
  proves the exact square

  ```text
  normalPair (e z) = diagExp (normalTangent z)
  ```

  on the quantitative source ball, while retaining the explicit error and
  target-ball radius.
- Generic `DiagExpDerivative.diagExpInv` is the existing consumer-facing branch
  constructed from a private qualitative `diagExpIFT :=
  ContDiffAt.toOpenPartialHomeomorph ...` at the zero section.
- `exists_diagInvDom_inf` / `exists_readoutDom_inf` expose one pointwise open
  `C^infinity` domain for that fixed branch, but no numerical radius uniform in
  the sequence/basepoint.
- `diagExpInv_diagExp` proves the source-side germ identity
  `diagExpInv (diagExp u) = u` near the zero section.
- `NormalPhaseEndpoint.normal_inv_eq` proves equality with `normalTangent` when
  the existing branch projection/intrinsic identities and the two concrete
  `expDiffeoRadius` inequalities are available.

Thus endpoint realization and uniqueness on every verified overlap are done.

## Exact design gate

The quantitative branch has an explicit sequence-uniform model target ball.
The totalized `diagExpInv` is tied to Mathlib's privately chosen qualitative IFT
source/target germ.  Openness of that germ gives a positive radius only after
fixing one `(k,x)`; its construction carries no quantitative lower bound.
Nothing currently proves that the whole explicit target ball lies in this exact
qualitative target, and a finite minimum at one fixed index does not produce the
relative sequence-uniform scale needed by `StepB1RawInput`.

The mathematical inverse is unique on overlap, but totalized `diagExpInv`
outside its IFT target is arbitrary.  Therefore overlap uniqueness alone cannot
extend equality to the full quantitative target ball.

## Candidate architectures

1. **Quantify the existing IFT branch.**  Prove that the exact private
   `diagExpIFT.source/target` contains transported explicit balls with the needed
   uniform relative radius.  Explain whether this is possible for Mathlib's
   `ContDiffAt.toOpenPartialHomeomorph` construction, or whether its arbitrary
   local choices make such a theorem unavailable without redefining the branch.

2. **Refactor the canonical consumer branch.**  Introduce the smallest branch
   package parameterizing the center/readout APIs by an explicit
   `OpenPartialHomeomorph` plus forward/inverse/projection/smoothness facts.
   Instantiate it with the transported quantitative normal branch in HCG, while
   retaining `diagExpInv` as the generic compatibility instance and proving the
   already checked overlap identity.  The HCG critical path would then have one
   selected branch, not two competing totalized functions.

3. **Redefine `diagExpInv` itself.**  If feasible, replace its private
   qualitative IFT implementation by an explicit branch construction that can
   accept quantitative normal-coordinate source/target data without making the
   generic exponential layer depend on HCG structures.  Explain how to avoid an
   import cycle or proof/data dependency on `NormalCoordMetricBoundInput`.

## What I want from the review

1. Recommend one architecture and explain why the other two are inferior or
   impossible in the present dependency graph.
2. Give the smallest new Lean data structure/theorem statements, with public
   names no longer than twenty characters where they are declarations.
3. Identify exactly which existing consumers should become branch-parameterized
   (`diagExpReadout`, `centerReadout`, `exists_readoutDom_inf`, or a lower layer),
   and which compatibility wrappers should remain stable.
4. Show how `exists_normal_diag` supplies every field of the proposed package,
   including source, target-ball containment, smoothness order, projection, and
   inverse identities.  If one field is genuinely missing, state the smallest
   producer lemma rather than adding it as an assumption.
5. State the acceptance theorem that is strong enough for the finite-hat /
   `StepB1RawInput` lane and explicitly preserves the relative scale.

## Constraints

- Do not infer a uniform radius from pointwise openness or uniform `metricC`.
- Do not take a finite minimum at one index and call it sequence-uniform.
- Do not add `branchRadius`, target-containment, or branch-equality hypotheses
  that merely restate the desired conclusion.
- Do not compare two independently chosen phase flows; `exists_normal_diag`
  already uses one common bilateral flow.
- Do not discard the existing generic `diagExpInv` API without a compatibility
  wrapper and migration plan.
- Keep theorem completion honest: `exists_normal_diag` is proved, but the
  uniform canonical-branch reconciliation theorem and `StepB1RawInput` producer
  are not yet stated/proved (0%).

Return the recommended architecture first, then exact Lean interfaces and a
dependency-safe migration sequence, and finally list any unavoidable new
mathematical producer.
