# SectionalRicci

## Role

This file converts pointwise sectional-curvature hypotheses into the Ricci
lower bounds consumed by comparison geometry.

## Route

- `ricci_nonneg_of_sec` expands membership in the native sectional-nonnegative
  cone, chooses an orthonormal frame perpendicular to the tested vector, and
  uses `ricci_eq_sum_perp`. It does not require a global positive-dimension
  instance: the zero-vector case closes directly, while a nonzero tested
  vector locally supplies positive finite rank.
- `ricci_pos_of_sec` uses the same trace formula. The explicit positive
  codimension hypothesis makes the strict finite sum nonempty and locally
  supplies the nonzero-dimension instance.
- `ricciLower_of_sec` packages the pointwise nonnegative conclusion as
  `RicciBoundedBelow g 0` for Bishop comparison.
- Curvature summands are connected to `metricRm04StdAt` through the native
  `rm04_eq_inner_riem` bridge.
- Static signature preflight confirmed that `exists_perp_pos` returns the
  required orthonormal/perpendicular frame and that `ricci_eq_sum_perp` has
  exactly the summand orientation used here. The sectional-cone projection
  also produces `metricRm04StdAt g x a b b a` in the required slot order.
- `exists_perp_pos` is declared in the canonical variation module
  `Geometry.Comparison.Variation.PerpFrame`. The prior imports did not expose
  it, so this file now imports that narrow producer directly.
- The file's `[I.Boundaryless]` instance supplies
  `BoundarylessManifold I M`, so the curvature bridge does not force a
  stronger public manifold hypothesis.

## Status

All three theorem bodies are source-complete, and their checked dependency
`rm04_eq_inner_riem` is current. The first focused attempt stopped at the
file-level bare `∞` manifold grade: this file opens `Manifold` but not the scope
that disambiguates that notation, so every later diagnostic was a cascade. The
binder now uses the notation-free smooth grade
`IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M`. The next focused attempt passed that
binder and stopped at the unknown identifier `exists_perp_pos`. This was an
exact missing-import diagnosis, not a missing theorem or proof obligation: the
declaration is in `PerpFrame.lean`, which is now imported directly. The import
repair has not yet been rechecked, and no named `SectionalRicci` artifact
refresh has been performed.

The target theorems themselves remain unverified until focused checks pass;
their checked completion is therefore 0%, while their dedicated source proof
implementation is 100%. Once verified, this file completes the
sectional-to-Ricci bridge needed by the strict-volume branch, but not the
strict-volume theorem itself (which remains a separate endpoint). This bridge
is roughly 5% of that dedicated rigidity branch and well below 1% of the full
Morgan--Tian/Poincare program.

After the binder and import repairs, the remaining first-check risks are
confined to local elaboration: constructing
`Nontrivial E` from a nonzero tangent vector, synthesizing the local `NeZero`
finite-rank witness, and the concrete witness shape expected by
`Finset.sum_pos`. No source signature or hypothesis mismatch remains visible
in the static review.
