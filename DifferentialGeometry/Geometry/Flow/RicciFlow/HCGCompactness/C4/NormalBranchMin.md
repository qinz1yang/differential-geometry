# NormalBranchMin

## 2026-07-14 branch-native Hessian identity

`IsNormalDiag.hess_half_inv` is implemented, focused-green, and sorry-free.
It upgrades the checked `grad_half_inv` identity to the intrinsic `lbl412`
formula on the same open half-cage: the Hessian of half squared distance is the
metric pairing with the Levi-Civita derivative of the negative selected inverse
tangent.  The proof uses the germ-local Hessian bridge and the generic
`DiagInvBranch.inv_snd_inf`; no branch field, endpoint-radius assumption, or
global smoothness claim was added.

This closes the germ-local Hessian bridge, not the center-of-mass strictness
endpoint.  Selected minimizing-branch Gates 1--6 remain 100%; Step-B/B1
machinery is about 88%, Chapter 4 machinery about 82%, and whole-HCG machinery
about 54%.  `StepB1RawInput`, textbook B1, the compactness endpoint,
`CmHessianInput`, and `StrictDistInput` remain theorem-level 0% until their
actual Lean statements and proofs are completed.  The next independent
frontier is the finite weighted Neumann/readout assembly.

## 2026-07-13 Gate 4 complete

`IsNormalDiag.grad_half_inv` is implemented, focused-green, and sorry-free.
It combines the already checked minimizing inverse `inv_is_min`, half-cage
smoothness `halfSq_inf`, and the comparison-layer producer
`grad_halfSqDist_min`. The conclusion identifies the gradient with the
negative selected inverse tangent for both diagonal and non-diagonal pairs.

The theorem retains the honest pointwise input
`rho / 2 <= expRadiusGp`; it adds no endpoint radius assumption and does not
identify `expMapC2Radius` with `expRadiusGp`. Gates 1--4 in this file are now
100% theorem-complete. Gate 5 is completed in `StepCCenterOfMass.lean` and
`StepCCmDomain.lean`; Gate 6 is now completed by the optimal
`gpCoerciveConst` comparison, H6 `gpRatio` floor, `normalMinScale`, and its
live-cage consumer.

Whole-project accounting remains conservative: the selected minimizing-branch
pointwise chain is complete, but `StepB1RawInput`, textbook B1, and the
conditional compactness endpoint are each still 0%. Step-B/B1 machinery
is about 79%, Chapter 4 machinery about 75%, and whole-HCG machinery about 52%
after rounding. The selected minimizing-branch Gates 1--6 machinery is 100%;
the post-packing finite-cage/Item-3 and independent Hessian/Neumann frontiers
remain.

## Earlier 2026-07-13 integration checkpoint (superseded)

After the latest `short-time-existence` progress was merged into the alignment
worktree, the missing `NormalDiagBranch` dependency was refreshed and the
focused check of `NormalBranchMin.lean` passed.  The saved proof of
`IsNormalDiag.halfSq_inf` is therefore now verified and sorry-free.  Gate 3 is
complete, and the verified pointwise declarations through Gates 1--3 are:

- `normalTan_metric` and `normalTanHome_target`;
- `IsNormalDiag.tan_mem_of_small`;
- `IsNormalDiag.inv_is_min`;
- `IsNormalDiag.halfSq_eq_inv` and `IsNormalDiag.halfSq_inf`.

The next mathematical target remains Gate 4,
`IsNormalDiag.grad_half_inv`.  No Gate 4 Lean code has been added.  The
pointwise Gates 1--3 infrastructure is now 100% verified, while Gate 4, the
uniform scale producer, concrete `StepB1RawInput`, textbook B1, and the
compactness endpoints remain 0%.  The merge does not by itself raise the
project-level estimates recorded in `PROJECT_MAP.md`.

## 2026-07-12 paused state: selected minimizing branch

This file is the pointwise part of the fourth B/C route.  It captures genuine
Hopf--Rinow minimizing tangents in the already selected quantitative diagonal
branch; it does not yet provide the sequence-uniform scale or the B1 endpoint.

Verified declarations:

- `normalTan_metric` and `normalTanHome_target`;
- Gate 1, `IsNormalDiag.tan_mem_of_small`;
- Gate 2, `IsNormalDiag.inv_is_min`;
- the first half of Gate 3, `IsNormalDiag.halfSq_eq_inv`.

Saved but not yet verified:

- `IsNormalDiag.halfSq_inf` is fully stated with a proof candidate using
  `DiagInvBranch.inv_inf`, metric-section smoothness, and
  `ContMDiffOn.clm_bundle_apply₂`.  The last focused verification did not reach
  this declaration because the upstream object
  `Tensor/RSTensor/Tensor0SRiemannian/Comparison.olean` was missing.  A narrow
  dependency refresh was in progress and was intentionally stopped when the
  task was paused to free resources.  This is therefore a verification/tooling
  blocker, not a reported theorem error.

The next action is exactly: rerun the focused check of `NormalBranchMin.lean`.
If it is green, mark Gate 3 complete and start Gate 4
`IsNormalDiag.grad_half_inv`.  The Gate 4 route must normalize the minimizing
tangent for `pt != y`, use `halfSqDist_dir_deriv`, and handle `pt = y` by the
local-minimum gradient lemma.  No Gate 4 Lean code has been added yet.

The radius contract remains explicit and honest.  The pointwise results assume
`rho / 2 <= expRadiusGp`; the current `NormalRadiusProfile` only controls
`expMapC2Radius`.  Thus `normalMinScale` has not been derived, Gate 6 remains a
real producer frontier, and no endpoint radius assumption has been added.

Progress accounting at pause:

- `halfSq_inf` theorem: 0% verified; its saved proof candidate is about 90%;
- Gate 3: one of two declarations verified (about 50% theorem completion);
- Gates 1--3 pointwise infrastructure: about 80% verified;
- Gate 4 first variation: not started as Lean code (0%);
- Gate 5 center readout and Gate 6 uniform scale: 0%;
- concrete `StepB1RawInput`, textbook B1, and compactness endpoints: 0%;
- Step-B/B1 machinery remains about 77%, Chapter 4 machinery about 74%, and
  whole-HCG machinery about 51%.  These overall estimates are deliberately not
  raised for an unverified local proof candidate.
