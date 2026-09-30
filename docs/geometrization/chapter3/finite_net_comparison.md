# Finite nets with the restricted metric approximate the original compact space

`GromovHausdorff.ghDist_subtype_le_of_net` takes a nonempty compact metric
space X, a nonempty compact subset s with its restricted ambient metric, and
an actual epsilon-net property. It proves dGH(X,s) <= epsilon. Epsilon may
be zero. The proof embeds both spaces into X by identity and inclusion and
applies Mathlib's Hausdorff estimate. `ghDist_finset_le_of_net` specializes
this to a finite set of centers. Nonemptiness of the subtype is explicit
because the existing compact GH distance is defined for nonempty spaces.
For a net in nonempty X, the witnessed coverage hypothesis supplies that
nonemptiness if a caller has not yet installed the instance.

This is the exact MC03/MC04 finite-net bound, without the larger constant
from the general global-map estimate. Neither metric is intrinsic to s.
No continuity of a nearest-center selection is required.

Source comparison uses blueprint207A, compact GH definition and the last
clause of the correspondence theorem (lines901–970), and the unchanged
source reading in reference_checks_revision58.md. The original claim is
BBI Example7.3.11, printed254–255/PDF269–270, with the same isometric ambient
inclusion. BBI2001 SHA256:
4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971.
No new errata reading is claimed. The actual Mathlib definitions and
`ghDist_le_hausdorffDist` and `hausdorffDist_le_of_mem_dist` signatures were
read at the target pin; their compactness and nonemptiness premises are
retained. The new leaf compiled; its declaration audit is in the manifest
receipt.
