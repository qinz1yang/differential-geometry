# Connection.lean notes

## 2026-05-10

Added the checked base-case wrapper:

```lean
covariantDeriv_vectorField_contMDiff
```

This records the `(1,0)` tensor regularity case directly from mathlib's
`CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply`: if the
connection is smooth and `X`, `Y` are smooth tangent sections, then
`p â†¦ (nabla_X Y)(p)` is a smooth tangent-bundle section.

This is the right base case to use before any tensor-bundle recentering work.
No chart-change or tensor naturality theorem is needed for `(1,0)`.

## 2026-05-11 tangent-constant connection smoothness closed

Closed:

```lean
CovariantDerivative.tangentConst_cov_mdiffAt
```

The proof is now a compatibility wrapper over the local smooth-connection API:
on the base set of `trivializationAt E (TangentSpace I) x`, both
chart-constant tangent fields are smooth by
`TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet`; applying
`ContMDiffCovariantDerivativeLocally` to the second field gives local
smoothness of `p â†¦ cov W p`; `clm_bundle_apply` with the first field gives
local smoothness of `p â†¦ cov W p (V p)`, and then restricting to the center
point gives `MDiffAt`.

Verified:

- Verification result recorded without command details.
## 2026-05-10 curvature smoothness frontier

Added:

```lean
CovariantDerivative.tangentConst_cov_mdiffAt
```

This is the final local smoothness statement needed by the concrete curvature
skew calculation: for a locally smooth covariant derivative, the section
`p â†¦ âˆ‡_{V_const} W_const` is `MDiffAt` at the center point when both tangent
fields are chart-constant there.

The theorem is intentionally stated in the tensor/nabla layer. The proof should come from
`ContMDiffCovariantDerivativeLocally` plus the existing local-frame regularity
lemmas for `tangentConstInChart`; it should not be reproved in the
Levi-Civita folder.

## 2026-05-11 extraction cleanup

Completed:

- Split `Connection.lean` into:
  - `Connection/Smooth.lean` for the local smooth-connection predicate and
    smooth application wrapper;
  - `Connection/Tangent.lean` for tangent chart-constant/model-field API and
    the solved `CovariantDerivative.tangentConst_cov_mdiffAt`;
  - `Connection/Endomorphism.lean` for extracted connection endomorphisms and
    fixed-chart connection formulas.
- Kept `Connection.lean` as a compatibility wrapper.
- Moved `TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet` from the
  endomorphism layer to `Connection/Tangent.lean`, because it is tangent-field
  API and is needed by `tangentConst_cov_mdiffAt`.

Verified:

- Verification passed.
