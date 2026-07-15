# BalancedPairing

## Purpose

This module is the generic home for balanced connection-Laplacian estimates
that were previously private to the DeTurck principal-arm energy proof.

## Extracted producers

- `iterL_jet_le` controls every covariant jet of an iterate of
  `1 - Δ_∇` by the expected finite jet window.  Its proof reuses the existing
  public raw-connection-Laplacian iterate estimate instead of duplicating the
  old private commutator recursion.
- `curv_iterL_pair_le` controls the balanced pairing with
  `pointwiseTensorCurv`.  The datum rank is an arbitrary `s₀`; the old DeTurck
  proof hard-coded rank `2` even though none of the argument used that rank.
- `iterL_pair_le` exposes the basic self-adjoint split as a norm-product bound,
  so scalar lower-order arms can balance derivatives without rebuilding the
  pairing algebra.
- `iterL_pair_jet_le` combines that split with the fixed-coefficient `appCc`
  jet window.  It controls a first-order coefficient action by the adjacent
  balanced windows `J_n * J_(n+1)` at every base covariant rank; its constant
  depends on the fixed smooth coefficient field, never on spectral support.
- `iterL_pair_jet_of` is the supplied-window form used by compact-parameter
  families. Its constant depends only on the common action window, so the
  coefficient parameter is quantified after the constant.
- `iterL_window_pair` packages the generic supplied-window version of the same
  balancing argument.  It accepts an arbitrary base tensor rank, arbitrary
  common pairing rank, an explicit split of the iterate, and independent jet
  budgets for the two arms.  The two budget inequalities are exactly the
  derivative bookkeeping needed to enlarge the finite windows; no new
  geometric or convergence assumption is introduced.

Only the norm, pairing-transport, monotone-window, and finite-sum helpers needed
by these declarations were retained.  No DeTurck coefficient fields or
consumer hypotheses were moved into this layer.

## Verification

Focused verification now passes without warnings after the shared upstream
refresh completed.  The only source repair needed was to make the intermediate
jet-window endpoints explicit in `iterL_pair_jet_le`; the arithmetic fact is
the direct consequence of the finite-range membership already in scope.

The later `iterL_pair_jet_of` refactor also passes focused verification. It is
dedicated machinery rather than an endpoint theorem; the downstream endpoint
remains 0% until its own Lean declaration is proved.
