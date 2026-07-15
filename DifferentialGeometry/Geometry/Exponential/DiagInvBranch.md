# DiagInvBranch

## 2026-07-11 selected-branch interface

`DiagInvBranch` is the generic explicit branch object recommended by the HCG
normal-branch review.  It records one `OpenPartialHomeomorph`, membership of the
zero tangent vector in its source, equality of its forward map with intrinsic
`diagExp` on that source, and all-order smoothness of its inverse on the target.
Quantitative radii deliberately remain producer data rather than record fields.

The file also proves the reusable consequences `right_inv`, `left_inv`,
`proj_eq`, `exp_eq`, `center_mem`, and `center_inv`; no duplicate inverse-law or
projection fields are stored.  `inv_eq_normal_lt` additionally identifies any
selected branch inverse with the moving normal chart inside the existing named
`expDiffeoRadius`, using only the branch inverse laws.  Focused verification
passed without warnings or local `sorry`s.

This closes the generic branch-interface brick (100%).  It does not yet provide
the quantitative radius needed by a concrete configuration.  The standard and
transported HCG branches, their readout domains, and finite-family containment
are now checked elsewhere.  The concrete `StepB1RawInput` producer and textbook
B1 theorem remain 0%; Step-B/B1 machinery is about 77%, Chapter 4 machinery
about 74%, and whole-HCG machinery about 51%.

## 2026-07-12 intrinsic-endpoint recovery

Added `DiagInvBranch.inv_eq_of_exp`: a tangent vector already in the selected
source is recovered by `B.inv` when its intrinsic exponential endpoint is the
given second point.  The stable proof uses `simpa only [diagExp_apply, hexp]`;
an unrestricted `simp` unfolds the intrinsic exponential too far.  Focused
verification passed, and the module object was refreshed.  This is a generic
branch-interface adapter, so the interface brick remains 100%; it does not
change the concrete B1 endpoint (still 0%) or the project-wide machinery
estimates above.

## 2026-07-14 fixed-endpoint inverse section

Added `DiagInvBranch.inv_snd_inf`.  On any set whose fixed-endpoint pairs lie
in the selected branch domain, the inverse fiber component is a smooth tangent
section based at the moving first point.  The proof only composes the existing
`inv_inf` producer and corrects the total-space base with `proj_eq`; it adds no
branch field or quantitative assumption.  Focused verification passed, and the
module object was refreshed successfully.
