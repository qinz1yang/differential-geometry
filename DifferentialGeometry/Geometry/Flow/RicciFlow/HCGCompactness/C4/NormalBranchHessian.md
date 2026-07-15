# NormalBranchHessian

## 2026-07-14 route

This file is the active branch-native Hessian/Neumann assembly.  The selected
inverse is first read in the common normal frame.  The center equation then
factors through the finite weighted inverse-velocity sum; at a root that sum
vanishes, so differentiating the frame contributes no term.  The remaining
weighted derivative is handled by `ContinuousLinearMap.sum_near_neg_inv`.

No endpoint radius field, glued weight family, or second selected-branch
hierarchy is introduced.

## Verified state

The branch-native chain is now focused-green and its exact module refresh
passes.  `cm_deriv_inv` factors the center readout through the common normal
frame, cancels the frame derivative at a root, and applies the weighted
Neumann theorem to the inverse-velocity derivative.  `cm_sol_strict` retains
that invertible derivative, proves the selected readout is `C1` on the same
branch `readDom`, and invokes the existing strict implicit-function theorem.

This closes the selected-branch analogue of `CmHessianInput`; the old abstract
`chartCmEqn` input is not repackaged as a second branch-specific input.

## Frontier and accounting

The independent remaining theorem is `StrictDistInput`: `hess_half_inv`
already closes the branch-native `lbl412` identity, but no checked producer yet
turns it into the `lbl413` uniform positive Hessian lower bound and per-target
geodesic `StrictConvexOn`.  That producer remains theorem-level **0%**.

The selected-branch Hessian/Neumann and strict-IFT producer is **100%**.  The
concrete `StepB1RawInput` producer, textbook B1 theorem, and compactness
endpoints remain **0%**.  Dedicated Step-B/B1 machinery is about **90%**,
Chapter 4 machinery about **83%**, and whole-HCG machinery about **55%**.

## 2026-07-14 strict-distance closure

This section supersedes the open-frontier accounting above.  The quantitative
normal-chart route is now checked: `IsNormalDiag.hess_inv_sixth` gives the
uniform positive lower bound and `HasNormalBrFull.hess_pos` transports it to
the selected physical branch.  The generic comparison lemmas in
`Geometry/Comparison/HessianAlongGeodesic.lean` and
`HasNormalBrFull.strict_dist` then produce the complete `StrictDistInput` for
`minJoin`.

Focused verification and exact target refresh passed for the Hessian module
and its convexity consumer.  The selected-branch Hessian, Neumann, strict-IFT,
and strict-distance machinery is **100%**.  The concrete `StepB1RawInput`
producer, textbook B1 theorem, and compactness endpoints remain theorem-level
**0%**.  Dedicated Step-B/B1 machinery is about **94%**, Chapter 4 machinery
about **86%**, and whole-HCG machinery about **57%**.

## 2026-07-14 arbitrary-order local solution

`IsNormalDiag.cm_sol_cd` is focused-green.  It upgrades the selected-branch
implicit center solution to every finite differentiability order `n >= 1` on
the same `readDom`, reusing the checked invertible derivative from
`cm_sol_strict` and the all-order smoothness of the normal-coordinate inverse.
It introduces no new input and does not by itself provide the global
cross-manifold comparison map or the all-pairs tail required by
`StepB1RawInput`.

The theorem-level accounting is unchanged: the concrete `StepB1RawInput`
producer, textbook B1 theorem, and compactness endpoints remain **0%**.  This
closes one arbitrary-order branch-local regularity brick inside the already
reported **94%** dedicated Step-B/B1 machinery.
