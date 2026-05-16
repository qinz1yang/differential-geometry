# NablaOnTensors FixedChart Notes

## 2026-05-11 mixed fixed-chart route correction

Worked:

- Reintroduced only the mixed tensor representative layer:
  `tensorRSModelAt`, `tensorRSModelAt_trivializationAt_symm`, and
  `tensorRSModelInChart`.
- These mirror the `(0,s)` representatives and are now used by the aligned raw
  RS definition in `RawDefs.lean`.
- The old analytic fixed-chart RS route remains deleted: there is still no
  `fixedChartNablaRSModel` or fixed-model smoothness proof here.

Reason:

- The previous raw RS definition used the pointwise
  `tensorRSSpace_continuousLinearEquiv`; that did not align with the `(0,s)`
  tensor-bundle trivialization style and made the scalar derivative bridge
  harder to state.
- The new representatives are coordinate infrastructure, not a revival of the
  fixed-chart naturality proof.

Remaining:

- `FixedChart.lean` is not blocked.
- The remaining `nablaRS_reg` frontier is in `Regularity.lean`: prove the
  intrinsic Hom-coordinate scalar smoothness theorem using the self-chart mixed
  derivation rule.

## 2026-05-11 extraction cleanup

Completed:

- Split fixed-chart support into:
  - `FixedChart/Models.lean` for tensor model representatives such as
    `tensor0SModelAt`, `tensor0SModelInChart`, `tensorRSModelAt`, and
    `tensorRSModelInChart`;
  - `FixedChart/Nabla0S.lean` for fixed-chart `(0,s)` nabla helper formulas.
- Kept `FixedChart.lean` as a compatibility wrapper.
- Did not delete fixed-chart helpers during this cleanup, since coordinate
  files still use the fixed-chart API.

Verified:

- Verification passed.
