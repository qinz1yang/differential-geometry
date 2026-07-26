# DiagInvFixed

## 2026-07-23 fixed-base branch adapter

`DiagInvBranch.fixedPD` packages one selected diagonal-exponential branch at a
fixed base point as a `C∞` partial diffeomorphism from the model tangent space
to the manifold.  Its source and target are exactly the fixed-fibre slices of
the branch source and target.  The forward map is `expMapIntrinsic`; the inverse
is the existing fixed-first coordinate readout.

The construction reuses `intrinsicFiber_smooth`,
`DiagInvBranch.inv_fst_coord_inf`, and the branch inverse laws.  It adds no
radius, connectedness, chart-selector, or curvature assumption.  Small simp
lemmas expose the forward and inverse values, the two domains, and the
zero/center behavior.

The first focused pass exposed only two elaboration details: the fixed base
must be the center parameter already carried by `DiagInvBranch`, and the
preimage-shaped source and target goals must be normalized explicitly before
applying the total-space inverse laws.  No alternative mathematical route was
needed.

Focused verification passed without warnings or local `sorry`s, and the exact
module refresh is GREEN (`3803/3803`).  The adapter is complete (100%).  The
global constant-curvature classification theorem remains unstated (0%); its
dedicated local-to-global machinery is approximately 32%, with the
Cartan/Jacobi transfer and global gluing still constituting the real frontier.

## 2026-07-24 compatibility projection

`fixedPD` no longer constructs and proves a separate fixed-base partial
diffeomorphism. It is definitionally the partial diffeomorphism carried by
`DiagInvBranch.fixed`, the canonical projection to `ExpInvBranch`. The
existing `fixedPD_*` declarations remain as compatibility lemmas for Cartan
consumers.

The refactored source is focused green and placeholder-free. This adapter
remains theorem-level 100%; it does not advance the unstated
`calabiDist_support` endpoint, which remains 0%.
