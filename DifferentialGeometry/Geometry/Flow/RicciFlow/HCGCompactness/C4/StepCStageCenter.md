# StepCStageCenter.lean

## 2026-07-18, framed stage-center distance readout

The two moving-manifold distance consumers now use the canonical
orthonormally framed normal chart. `HasStageRootCube.symm_dist_tail` and
`HasSuppConvData.pts_dist_tail` both decode their model points through
`framedChartAt.symm`.

Their target-domain proofs consume the existing `geom_on` conclusion
`U alpha ⊆ ball 0 expRadiusGp`. Membership in the framed chart target is
proved directly through `framedExp_source`, `normalFrame_sqrt`, and the
existing intrinsic-to-raw smoothness-radius bridge. No endpoint-radius
assumption, chart selector, or raw/framed compatibility theorem was added.

The first focused check saw the stale installed form of
`NormalCoordMetricEquivOn.symm_dist_le`, whose live source had already moved
from raw to framed coordinates. After the coordinated upstream refresh, the
focused check passed with no local diagnostics. This was an artifact refresh,
not a proof or mathematical blocker.

The framed stage-center distance seam is complete (100%).
`MetricCompactBase.exists_b1_raw` has a complete live proof body, but it is not
yet framed-green; the separately named textbook B1 theorem remains
theorem-level 0%. Dedicated Step-B/B1 machinery remains roughly 95% and
Chapter-4 machinery roughly 87%, but the selected route is not fully
framed-validated until its downstream comparison/readout files are repaired.
Whole-HCG machinery remains about 60%.

## 2026-07-18, exact refresh frontier

The exact `StepCStageCenter` target was retried after the canonical
`NormalLimitPhase` and `NormalDiagBranch` refreshes. It stopped in the next two
upstream source consumers, `NormalBranchScale` and `NormalBranchMin`;
`StepCSupportCapstone` was therefore not started. `NormalBranchScale` still
supplied raw `expMapC2Radius` bounds to the now intrinsic
`pair_mem_of_closed`, while `NormalBranchMin` still mixed raw chart/exp decode
steps with framed `normalExpPD` and `chart_mem_norm_le` outputs. This is a
source-migration blocker, not a local regression in `StepCStageCenter`.

`NormalBranchScale` and `NormalBranchMin` have since been migrated and
exact-refreshed.  The next authorized `StepCStageCenter` exact run stopped one
layer deeper in `NormalBranchHessian`: the selected-branch readout API in
`StepCSmoothness` still interpreted its fixed-base parameters through raw
`normalChartAt`, and Hessian retained raw chart-target, raw-radius neighborhood,
and raw left-inverse calls.  The H6 lane owns the canonical repair
`StepCSmoothness -> NormalBranchHessian`.  The StageCenter source remains
focused-green; `StepCSupportCapstone` was again not started, as required by the
abort-on-first-real-failure protocol.

After that owner chain was focused- and exact-refreshed, the authorized exact
`StepCStageCenter` target passed (`4004/4004`). Thus the canonical framed
stage-center module is now exact-green. This validates this module and its
current import chain only; it does not by itself complete the downstream B1
producer validation or the separately named textbook theorem.
