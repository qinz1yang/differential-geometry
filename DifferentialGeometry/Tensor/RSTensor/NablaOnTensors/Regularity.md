# NablaOnTensors Regularity Notes

## 2026-05-11 `(0,s)` regularity cleanup

Worked:

- `NablaOnTensors/RawDefs.lean` owns `nabla0SFun`, `nablaRSFun`,
  `Nabla0SRegular`, `NablaRSRegular`, `nabla0S`, and `nablaRS`.
- `NablaOnTensors/Regularity.lean` owns the regularity proofs.
- `NablaOnTensors/Raw.lean` is a compatibility import of `Regularity`.
- `nabla0S_reg` is closed at `âˆž` by local-frame coefficients: evaluate
  `nabla0SFun` on the tangent frame from `trivializationAt E (TangentSpace I) xâ‚€`,
  prove scalar smoothness by the moving-slot derivation formula, and reconstruct
  with `contMDiff_multilinearSection_iff_coord`.
- The old `nabla0SFun_fixedChart_eventuallyEq` route is no longer used.

Important adjustment:

- The closed regularity target is `âˆž`, not the stronger `âŠ¤` target.  The current
  smooth multilinear evaluation and scalar directional derivative APIs are
  stated at `âˆž`.

## 2026-05-11 mixed Hom-coordinate work

Worked:

- `nablaRS_reg` now reduces mixed tensor smoothness through the explicit
  Hom-coordinate criterion from `Tensor.RSTensor.Basis`: apply an input `(0,r)`
  model basis tensor, then evaluate the output `(0,s)` tensor on basis vectors.
- `TensorRSSpace.trivializationAt_basis_coord` rewrites each fixed-trivialization
  Hom coordinate into intrinsic evaluation on a local `(0,r)` input tensor and
  local tangent slots.
- The local `(0,r)` input tensor section is now named
  `Tensor0SSpace.constInChart`.

Current frontier:

```lean
ContMDiffAt I ð“˜(ð•œ, ð•œ) âˆž
  (fun p =>
    (nablaRSFun r s cov X T p)
      (Tensor0SSpace.constInChart r xâ‚€ Î²Ï p)
      (fun a => (trivializationAt E (TangentSpace I) xâ‚€).symmL ð•œ p (vÏƒ a)))
  xâ‚€
```

What failed:

- The deleted mixed fixed-chart route compared raw `nablaRSFun` with a
  fixed-chart model expression and reintroduced the moving-center problem.
- A direct scalar derivative bridge for
  `y â†¦ (tensorRSSpace_continuousLinearEquiv ... (T ...)) ...` hit the same
  issue: the raw RS definition uses the pointwise model equivalence at the
  varying output point, while the regularity coordinate is naturally phrased by
  fixed-chart moving sections.

Next useful frontier:

- Prove an operator-specific moving-section derivation theorem for `nablaRSFun`,
  analogous to `nabla0SFun_eval_coordFrame_moving_raw`, but for a local `(0,r)`
  input tensor section and local output vector sections.
- If that theorem again requires comparing the pointwise
  `tensorRSSpace_continuousLinearEquiv` at varying points with a fixed
  trivialization, the design issue is the raw RS definition rather than the
  Hom-coordinate layer.  At that point the better replan is to align the raw RS
  definition with the fixed-trivialization style already used by `(0,s)`.

## 2026-05-11 RS raw-definition alignment

Worked:

- `RawDefs.lean` now defines `mcovariantDeriv_tensorRSWithin` using
  `tensorRSModelInChart` and the fixed mixed tensor-bundle trivialization,
  mirroring the `(0,s)` definition instead of using
  `tensorRSSpace_continuousLinearEquiv` pointwise.
- Added the centered scalar derivative bridge
  `fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun`.
  It identifies the model derivative of the aligned mixed scalar evaluation
  with the intrinsic `extDerivFun` term.
- The proof needed the standard `Tensor0SModel` transparency option and one
  local rewrite from a forward trivialization coordinate to
  `continuousLinearMapAt` before applying the `symmL` round-trip.

Verified:

- Verification passed.
Current frontier:

- `nablaRS_reg` still has the single scalar smoothness `sorry`.
- The definition mismatch is no longer the main issue. The remaining theorem is
  to prove smoothness of the intrinsic Hom coordinate

```lean
fun p =>
  (nablaRSFun r s cov X T p)
    (Tensor0SSpace.constInChart r xâ‚€ Î²Ï p)
    (fun a => (trivializationAt E (TangentSpace I) xâ‚€).symmL ð•œ p (vÏƒ a))
```

using the mixed self-chart derivation formula and the already proved `(0,s)`
regularity inputs.

## 2026-05-11 local Hom derivation attempt

Worked:

- Added `localCovariantDerivTensor0SAt`, a pointwise local `(0,r)` input
  correction for local tensor input sections.
- Proved the self-chart mixed derivation theorem
  `nablaRSFun_eval_moving_raw`.
- The proof stayed in the intended route: aligned raw RS definition,
  `covariantDeriv_tensorRSModelWithin_eval_derivation`, the centered RS scalar
  derivative bridge, and the vector-field chart formula for output slots.
- It did not reintroduce a comparison between unrelated chart centers `p` and
  `xâ‚€`.

Reflection:

- `nablaRS_reg` is still realistic, but it is not just an algebraic rewrite now.
- The remaining smoothness gap is the local analytic assembly after the Hom
  derivation formula:
  1. scalar directional derivative of `p â†¦ T p (B p) (V p)`;
  2. output-slot correction terms using smoothness of `cov (V a)`;
  3. input correction term
     `p â†¦ T p (localCovariantDerivTensor0SAt r cov X B p) (V p)`.
- The third item is the real remaining helper: prove smoothness of the local
  `(0,r)` covariant-derivative input correction for
  `B p = Tensor0SSpace.constInChart r xâ‚€ Î²Ï p`, then prove smooth RS
  evaluation on that local input and fixed tangent slots.

Current obstruction:

- `nablaRS_reg` still has one `sorry`, now after the useful derivation theorem.
- The next implementation should add a local smoothness theorem for
  `localCovariantDerivTensor0SAt` on fixed-chart constant `(0,r)` inputs, not a
  fixed-chart RS naturality theorem.

Remaining:

- `nablaRS_reg` still has one explicit `sorry`.
- `Connection.lean` still has the pre-existing `tangentConst_cov_mdiffAt` sorry.

## 2026-05-11 extraction cleanup

Completed:

- Split regularity proofs into:
  - `Regularity/Derivation.lean` for scalar derivative bridges and local
    moving-slot derivation formulas;
  - `Regularity/Tensor0S.lean` for local `(0,s)` input-correction machinery
    and `nabla0S_reg`;
  - `Regularity/TensorRS.lean` for mixed Hom-coordinate regularity and
    `nablaRS_reg`.
- Kept `Regularity.lean` as a compatibility wrapper.
- Made a few formerly file-private helper lemmas visible across the split
  because `TensorRS.lean` depends on the `(0,s)` chart-differentiability and
  local correction lemmas from `Tensor0S.lean`.

Verified:

- Verification passed.
- The stale note above is superseded: the current split has no `sorry` in
  `Connection` or `Regularity`, and the scan of the NablaOnTensors tree returns
  no `sorry`/`admit` matches.

## 2026-05-11: Infinity regularity rebuild

- Rechecked the derivation, `(0,s)`, and mixed `(r,s)` regularity stack after removing the raw `top` default.
- The only proof edit needed in `Regularity/Tensor0S.lean` was a local `IsManifold I (infty + 1 + 1) M` instance derived from `[IsManifold I infty M]` for the tangent-constant covariant-derivative smoothness helper.
- Verification passed.
