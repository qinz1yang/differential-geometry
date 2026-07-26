# BranchRadius

## 2026-07-23 fixed-first selected inverse calculus

The canonical branch radius keeps the selected-branch center independent of
the later fixed source point.  The file now defines `branchEnergy` and
`branchRadius` and proves:

- `exp_inv_mfderiv`, the differential of the selected fixed-first inverse is a
  right inverse of the intrinsic exponential differential;
- `inv_exp_mfderiv`, the corresponding left-inverse identity on the selected
  source;
- `branchRadius_infAt` and `branchRadius_open`, all-order smoothness of the
  branch radius at every selected nonzero launch vector, including an explicit
  open endpoint neighborhood;
- `grad_branchEnergy` and `grad_branchRadius`, the intrinsic first-variation
  formulas obtained from `intrinsic_gauss`;
- `branchRadius_ray`, the exact affine radial identity along a selected ray.

These proofs use only the open selected branch, intrinsic exponential
smoothness, and the canonical fixed-first coordinate readout.  They do not add
`ConnectedSpace`, a raw exponential-domain hypothesis, or a quantitative
radius.  Focused verification passed with no local placeholders, and the new
module's exact artifact is current.

The fixed-first inverse calculus in this file is complete (100%), and Layer A
of the radial-Laplacian route is complete (100%).  This is producer
infrastructure: the radial-Laplacian endpoint is accounted separately until
its own theorem is proved and verified.  Whole HCG supporting machinery
remains roughly 60%, while unconditional `compactnessSol` remains 0%.

## 2026-07-24 canonical `ExpInvBranch` migration

The fixed-first calculus now consumes the canonical `ExpInvBranch` directly.
The redundant moving-base center argument and tangent-bundle pair packaging
have been removed from `branchEnergy`, `branchRadius`, and all of their
derivative formulas. Existing diagonal consumers are recovered through
`DiagInvBranch.fixed`; this file is no longer a second proof hierarchy tied to
the diagonal branch.

The new theorem `ExpInvBranch.edist_le_radius` proves the exact inequality
needed by the Calabi support construction: the intrinsic radial curve selected
by the branch has endpoint distance at most its branch radius. It uses path
length only and does not assert that the branch curve minimizes nearby
endpoints.

The migrated file is focused green and remains placeholder-free. Its targeted
artifact refresh is temporarily waiting for the concurrently edited
conjugacy-reversal upstream module to become focused green. This brick is
complete at theorem level; `calabiDist_support` itself remains unstated and
therefore 0%. Route B-prime remains about 45%, whole HCG supporting machinery
about 60%, and unconditional `compactnessSol` theorem-level 0%.
