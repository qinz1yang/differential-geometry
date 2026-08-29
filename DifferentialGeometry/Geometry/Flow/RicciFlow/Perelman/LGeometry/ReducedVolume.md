# ReducedVolume

## Checked assembly

- `redDensity` is the positive normalized reduced density, and `redVolume`
  integrates its nonnegative lift against the metric at time `T - tau`.
- `lExpPartial` realizes the fixed-time L-exponential map as a partial
  diffeomorphism on `lInjDomain`.  Its source, target, value, and parameter
  density are identified by `lExpPartial_source`, `lExpPartial_target`,
  `lExpPartial_apply`, and `lExpPartial_density`.
- `lExp_inj_cover` puts the complement of the strict image inside the L-cut
  image.  `lExp_inj_ae` combines this with `lCut_null`, so change of variables
  loses only a null target set; it makes no false claim that the complement of
  the tangent-space source domain is null.
- `redVolume_lint` applies the generic weighted parametrization formula and
  rewrites the resulting model density as
  `ofReal (lRedJac * lSrcDensity)` on the strict domain.
- `redVolume_anti` compares these integrals on nested strict domains using the
  proved pointwise theorem `lRedJac_anti`.

The public capstone assumes compactness and connectedness of the fixed
manifold, positive `tau1 <= tau2`, and regularity of the single backward slab
`Icc (T - tau2) T`.  The smaller slab is derived internally.

## Verification and progress

Focused verification passes without warnings or proof placeholders.  The
axiom audit for `redVolume_anti` reports only `propext`, classical choice, and
quotient soundness.

- `redVolume_anti`: **100%** (stated, proved, and focused-check verified).
- Fixed-manifold L7 monotonicity assembly: **100%**.
- Dedicated compact ordinary-flow L-geometry, including the separate
  Euclidean small-time normalization follow-up: about **99%**.
- Generic infrastructure used by this proof route: **100%**.
- P2 remains below **1%**; the whole Poincare program remains approximately
  **3--5%**.
