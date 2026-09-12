# SbrRadialHessian.lean

Verified 2026-09-08 in the dev checkout. The native perpendicular index-form comparison retains the exact radial projection square and identifies it with the actual branch gradient. Both sharp comparisons are proved for a supplied smooth inverse-exponential branch along the actual minimizing segment; lower comparison sources are unchanged.

Empty focused output: 22.5s. Lint-clean named build: 25.1s.
Fresh external public axiom audit: 16.8s; all 2 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrRadialHessian-result1.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source follow-up. Claim
`eb6dc989-6304-40e1-a6f3-ce4b3e6d2aaa` retained. SOURCE-WRITTEN / UNVERIFIED.
Chapter23 owns the compiler window through18:10; this work is source-only.

The sbr-* census found that the checked native radial-Hessian theorem
exports the coarser `inner Y Y / L` bound. Its proof already establishes
the perpendicular estimate and exact radial/mixed vanishing. This leaf
retains the orthogonal-projection square instead of discarding it.

The proof reuses the existing private comparison, mixed-radial and symmetry
lemmas through `open private`; the source of RadialHessian is unchanged.
The algebraic decomposition follows the checked native proof, with its
last weakening replaced by the exact squared-projection identity. A second
statement uses the actual `gradientFun` of `branchRadius`, identified by
`grad_branchRadius`, to give the book's gradient form of the sharp bound.

Inputs remain the actual smooth inverse-exponential branch, unit initial
velocity, positive length, minimizing property and nonnegative curvature
along the actual segment. No Hessian estimate is assumed. This is the
smooth branch form used by the native coray supports; a statement for an
arbitrary smooth distance germ without specifying such a branch would
also need the corresponding distance-to-branch producer and is not claimed
merely from this source. The main Busemann-convexity producer already uses
the checked coarser estimate, so this sharpening is an interface completion,
not a new prerequisite retrofitted into the verified retraction chain.

Two public declarations are intended. Full focused, linted named-build and
external public dependency audit remain pending. New Markdown stays local
and ignored as requested.
