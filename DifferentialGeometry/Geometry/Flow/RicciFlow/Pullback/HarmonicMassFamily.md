# HarmonicMassFamily

## Status

The source implementation is present on `codex/analytic-producers-e87b` but
has not yet been checked by Lean.  It was written while the shared
Ricci--DeTurck Edge build owned the Lean runner, so no competing focused check
or targeted build was started.

This is intermediate harmonic-map heat-flow machinery.  The exact theorem
`ricci_flow_forward_unique` remains theorem-level **0%**.

## Producers

* `hmfVolumeReal` retains the one two-sided compact-window measure-comparison
  constant from `hmfVolumeEquiv` and converts its forward inequality into the
  real total-volume bound
  `vol_(g(t))(M) <= C.toReal * vol_q(M)` for every time in the same window.
* `hmfSpecTime_cont` promotes the scalar continuity supplied by
  `hmfStateTime_cont` to operator-norm continuity of `hmfSpecMassOp`.  It uses
  `hmfSpecMass_state` on a radius that is simultaneously inside the state-mass,
  pointwise-mass, and local-addition differentiability radii.
* `hmfMassFamily` chooses one radius after the common volume constant, mass
  Lipschitz constant, and time-continuity radius are fixed.  On that one closed
  ball, every time-slice mass is state-Lipschitz, has the uniform lower bound
  `(C.toReal^-1 / 2) * ||v||^2`, and is operator-norm continuous in time.

The coercivity radius is quantitatively restricted by
`L * R <= C.toReal^-1 / 2`, exactly the hypothesis consumed by
`Analysis.ODE.coerOn_of_lip`.  The closed ball is also placed strictly inside
the open time-continuity ball.  There is no per-time shrink.

## Verification

Static review found no `sorry`, `admit`, `axiom`, or `opaque` producer.  All
new public theorem names are at most twenty characters and both files are
below the 3000-line limit.  `git diff --check` must pass before handoff.

The required focused check remains queued until the active shared build
releases the Lean runner.  Until then these declarations are source-only and
count as **0% verified**.

## Honest accounting

* this compact-window mass-family package: mathematical/source assembly about
  **90%**, Lean verification **0%**;
* finite faithful HMF mass/coercivity infrastructure: advanced but still
  intermediate;
* `ricci_flow_forward_unique`: **0%**;
* `ricci_flow_unif_existence`: unaffected by this file.
