# Scalar Laplacian bridge

## 2026-07-09

- `divergence_levi_eq` identifies the algebraic trace of the canonical
  Levi-Civita covariant derivative with the Voss--Weyl divergence.
- The proof expands both traces in one `g`-orthonormal basis.  The basis and
  identity inverse metric are constructed locally from the metric fibre, so
  this operator layer does not import a higher curvature module.  It reuses the
  intrinsic divergence theorem without unfolding coordinate representations
  downstream.
- `laplacian_levi_eq` and `laplacianAt_eq_delta` then identify the realized
  scalar Laplacian with the divergence-form `Delta_g` whenever the stored
  connection is canonical.
- Focused source verification passed without warnings or `sorry`.  The former
  upstream `nablaRSFun_eval_moving_raw` elaboration wall is closed by the
  scalar/model-projection repair recorded in `Derivation.md`, and a fresh
  targeted build of this bridge now passes.

This proves the source-level operator interface needed between the
interval-local heat-potential predicate and conjugate-heat mass conservation;
the bridge is available to downstream integration.  It does not provide
nonautonomous heat existence.  That theorem remains 0%; Perelman
no-local-collapsing remains 0%; whole HCG endpoint theorems remain 0%.

## 2026-07-16 zero-rank closure

`divergence_levi_eq`, `laplacian_levi_eq`, and `laplacianAt_eq_delta` no longer
expose `NeZero (finrank E)` to consumers.  The divergence proof handles rank
zero directly and installs the nonzero instance only in the complementary
branch; the two Laplacian bridges inherit that result.  Focused verification
and the targeted module refresh passed without a new `sorry`.

This removal was needed by the dimension-uniform `W` square assembly.  It is a
producer cleanup, not progress on the no-local-collapsing endpoint itself.
