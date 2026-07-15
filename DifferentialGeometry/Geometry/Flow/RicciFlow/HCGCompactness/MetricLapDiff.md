# Moving scalar Laplacian difference

## 2026-07-13 short-time alignment

The order-one covariant-norm bridge now transports the tensor-level `sub_zero`
equality through `normSq0S` explicitly.  This replaces a representation-level
rewrite that no longer matches after the tensor API merge.  The theorem
statements are unchanged, and focused verification passed without warnings.

## Goal

Bound the canonical scalar Laplacian difference by the fixed-background
metric `C¹` modulus, the fixed Levi-Civita Hessian, and `du`, without a
globally selected frame or a varying-fibre continuity statement.

## 2026-07-10

- Added `lcDiff_norm_le`. It chooses a moving-metric orthonormal basis only at
  the current point, consumes the existing Koszul/component estimate, and
  rewrites the first covariant metric norm to `metricDerivNorm 1`.
- Added `lapDiff_sq_le`. If
  `n * metricDerivNormSupOn univ 1 h g g <= 1/2`, order-zero smallness first
  gives `g ≃₂ h`; the theorem then proves
  `|Delta_h f - Delta_g f|^2 <= 8 n^2 rho^2 |Hess_g f|^2 +
  72 n rho^2 |df|^2`.
- The proof uses `lap_sub_conn`, `trace_sub_le_c0`, `connOut_norm_le`, and
  pointwise tensor norms. It never compares whole bundle/Hom models and never
  constructs a global frame.
- A transient instance failure at the `Delta_g`/canonical-laplacian bridge was
  caused by declaring both a standalone normed-space instance and the one
  inherited from `InnerProductSpace`. Removing the redundant instance restored
  the canonical single-instance world.
- Focused verification passed without warnings. The downstream spectral
  energy theorem and continuous-linear-map packaging remain separate.
