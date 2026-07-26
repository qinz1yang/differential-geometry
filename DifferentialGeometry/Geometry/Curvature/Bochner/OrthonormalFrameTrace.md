# OrthonormalFrameTrace

## 2026-07-16: public endomorphism trace formula

The pointwise endomorphism formula previously existed only as the private
`linearMap_trace_eq_orthonormal_bilin_sum`.  No equivalent public theorem was
found in `DifferentialGeometry/`; the public bilinear-form theorem
`orthonormal_basis_bilin_trace` is more general but is not the fully applied
normal form needed by divergence consumers.

The existing theorem is now exposed as `trace_eq_ortho_sum`:

```text
LinearMap.trace ℝ (TangentSpace I x) T
  = ∑ i, g.inner x (T (B i)) (B i)
```

It is pointwise and takes only the endomorphism, the frame, and the frame's
orthonormality proof.  The proof transports the metric to an inner-product
instance, promotes the full-cardinality family to an `OrthonormalBasis`, and
uses `LinearMap.trace_eq_sum_inner`.  A zero-dimensional branch removes the
old `NeZero` dependency.  The exported statement also omits the unrelated
model inner-product, sigma-compactness, Hausdorff, and boundaryless instances.
No whole-bundle equality or field regularity hypothesis is introduced.

Focused verification passed with no new warning and no `sorry`; the file's
three older private unused-section-variable warnings remain unchanged.

## Honest progress

- This public trace adapter: 100%.
- The intended weighted-divergence producer that consumes it: still 0% in this
  file; this change supplies one algebraic input only.
- The weighted Hessian-square split and W-monotonicity endpoint: 0% here.
- Perelman noncollapsing endpoint: 0%; dedicated entropy/noncollapsing machinery
  remains roughly 65--70% assembled in the active lane.
- Whole HCG compactness project: approximately 60%; unchanged by this adapter.

