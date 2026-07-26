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

## 2026-07-23 fixed-first inverse map

Added `DiagInvBranch.inv_fst_inf`.  On a set whose pairs with fixed first point
lie in the branch domain, the selected inverse is a smooth tangent-bundle map.
The proof is the direct composition of the fixed-first pair map with `inv_inf`;
it adds no chart choice, radius, or endpoint assumption.

The accidental file-wide `ConnectedSpace M` assumption was also removed.
Focused verification passed for the complete file.  This closes the small
component-local branch API needed by the Calabi preparation, but the actual
fixed-metric Calabi support theorem remains unstated and therefore 0%; its
dedicated branch/Hopf infrastructure is still only supporting machinery.

## 2026-07-23 fresh-import proof repair

A targeted refresh exposed that the older proofs of `inv_eq_of_exp` and
`exp_eq` depended on stale simplifier shapes for `diagExp`.  Both proofs now
change directly to the defining intrinsic-exponential equality before applying
the branch inverse laws.  In particular, they no longer invoke the exported
`diagExp_apply` theorem, whose surrounding module still carries an unrelated
connectedness seam.

Focused verification against the refreshed intrinsic-exponential artifacts
passed, and the exact targeted refresh is GREEN (`3780/3780`).  The component-
local `diagExp` projection seam is now repaired in `ExpVariationSmooth`, so the
branch proof no longer depends on either stale simplifier state or an accidental
connectedness hypothesis.  This is a proof-stability repair only: the generic
branch API remains complete, while the Route B' Calabi distance-support theorem
remains 0%.

## 2026-07-23 fixed-first coordinate readout

Added `DiagInvBranch.inv_fst_coord_inf`.  It composes the existing smooth
tangent-bundle inverse with the canonical geodesic-chart fiber coordinate and
uses `proj_eq` to identify the fixed fiber.  Downstream inverse-function
calculus can therefore work in the model space `E` without unfolding a
trivialization or adding a chart selector.

Focused verification and the exact module refresh both passed.  This coordinate
readout theorem is complete (100%).  It is one infrastructure brick for the
fixed-first radius route; the eventual `radialLap_eq_mean` theorem remains
unstated (0%), its dedicated Route B-prime machinery is roughly 35%, and the
whole HCG supporting machinery remains roughly 60%.

## 2026-07-24 canonical fixed-first projection

Added `DiagInvBranch.fixed`, which restricts a diagonal selected branch to one
fixed first point and returns the canonical `ExpInvBranch`.  Its source and
target are the direct preimages

```text
u ↦ ⟨p, u⟩ ∈ B.hom.source
y ↦ (p, y) ∈ B.dom,
```

and the inverse is the existing fixed-first coordinate readout
`((B.inv (p, y)).snd : E)`.  The smooth fiber insertion is proved through the
canonical tangent-bundle trivialization; no singleton product is incorrectly
claimed open.  The simp projections `fixed_source` and `fixed_target` expose
the two membership formulas without unfolding the construction.

Focused verification against the current `ExpInvBranch` artifact passed with
zero diagnostics.  This compatibility projection is complete (100%) and adds
no radius or endpoint hypothesis.  The fixed-metric
`calabiDist_support` theorem is still unstated (0%); this projection is one
completed API brick in its dedicated machinery.
