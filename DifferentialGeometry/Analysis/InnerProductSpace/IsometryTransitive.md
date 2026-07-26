# IsometryTransitive.lean — notes

Verification: focused `lake env lean` PASSED (exit 0), no `sorry`, no warnings.
(Fresh elaboration, not cached — exit 0 trustworthy here; will be re-confirmed when
a downstream file imports it and triggers an olean build.)

## Provides

`exists_linearIsometryEquiv_unit {u v : E} (hu : ‖u‖=1) (hv : ‖v‖=1) :
∃ e : E ≃ₗᵢ[ℝ] E, e u = v` — O(n) transitive on the unit sphere, for any
finite-dimensional real inner product space `E`.

## Route (reused Mathlib)

- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (PiL2.lean:1035):
  extend an orthonormal family on a subset to a full `OrthonormalBasis (Fin n)`.
  Used with `s = {i0}` a singleton, so the orthonormality hypothesis collapses to
  `‖w‖ = 1`.
- `OrthonormalBasis.equiv` (PiL2.lean:830) + `equiv_apply_basis` (839): the
  `LinearIsometryEquiv` mapping one orthonormal basis to another; with
  `Equiv.refl` and both bases pinned to send `i0 ↦ u`, `i0 ↦ v`, it sends `u ↦ v`.

## Gotchas hit

- Real inner product notation: under `open scoped RealInnerProductSpace` it is
  `⟪x, y⟫` (the `_ℝ` suffix is NOT part of the notation — writing `⟪w,w⟫_ℝ` mis-parses).
  Cleaner to avoid the notation and finish via `real_inner_self_eq_norm_mul_norm`.
- Singleton subtype `↥({i0} : Set _)`: provide `Subsingleton` explicitly via
  `Set.mem_singleton_iff.mp` on the two membership proofs; don't `rw` a `∈` as an `Eq`.

## Role

Step 1 of the `spaceForm_const_metric` plan (plan-on-taking-a-spicy-kitten.md):
point-transitivity backbone for the homogeneity curvature argument. Only
unit-vector (1-tuple) transitivity is needed — the one-point curvature computation
covers all `X,Y` at the pole, then naturality + isometry-preserves-Gram spreads it.
