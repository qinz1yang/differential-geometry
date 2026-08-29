# CutLocus

## Result

`CutLocus.lean` defines the fixed-time L-cut domain, its L-exponential image,
and its conjugate and multiple-minimizer pieces.  `mem_lCutDomain` identifies a
cut tangent as one minimizing at the displayed time with no strictly later
minimizing extension.  `lCut_split` is the direct set-level consequence of
the native `lCut_alt` theorem.  At positive time, `lMinSlice_closed` proves
closedness of the fixed-time minimizing slice by a common regularity slab and
the existing minimizing-vector limit theorem; `lCutDom_closed` then removes
the open strict-injectivity domain.  `lCutDom_meas` records the resulting Borel
measurability of the tangent-space cut domain.

## Verification

Focused verification passed without warnings after consuming the targeted
`CutInjectivity` artifact that supplies `lInjDomain`.  The source contains no
placeholder proof.  Axiom audits for the split, closedness, and measurability
endpoints report only `propext`, classical choice, and quotient soundness.

## Scope

This is a set-theoretic decomposition layer with the stated positive-time
domain closedness and measurability.  It makes no claim about measurability or
measure-zero properties of the L-cut image.

Project accounting: this verified decomposition is a small interface layer
within the global L-geometry program.  It does not constitute a cut-locus
regularity or image-measure theorem.

## Next exact frontier

The image-null theorem splits into `lCutConj_null` and `lCutMulti_null`.
The conjugate branch can use Mathlib's finite-dimensional Sard lemma, but the
generic chart-null transfer currently lives only as a consumer-specific result
deep in the elliptic Hessian tree; it must be factored into the integration
measure layer before L-geometry can consume it without an architectural
inversion.  The multiple-minimizer branch additionally needs a local
Lipschitz theorem for `lCost` on positive compact slabs and a native
manifold-chart Rademacher/null-transfer bridge.  No image measurability or
nullity is assumed here.

- Tangent cut-domain closedness and Borel measurability: 100%.
- Conjugate/multiple-minimizer set split: 100%.
- Cut-image measurability and measure-zero theorem: 0%.
- `redVolume_anti`: 0%.
