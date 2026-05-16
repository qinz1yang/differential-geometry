# MSM110 Chapter 6

## 2026-05-12 chapter index

`BK.MSM110.Chapter06` imports the Section 6.1 companion. The companion is
book-facing only; the scalar evolution derivation lives in
`RicciFlower.RicciFlow.Evolution.Scalar`.

Verification passed.

## 2026-05-13 Section 6.2 import

`BK.MSM110.Chapter06` now also imports the Section 6.2 Uhlenbeck companion.
The canonical statement layer is `RicciFlower.RicciFlow.Evolution.Uhlenbeck`;
BK keeps only label-preserving wrappers.

Verification: the new Section 6.2 file itself passed a focused check.  A later
targeted BK module build is currently blocked by an unrelated current failure
in `RicciFlower/Curvature/Components.lean`, where the proof near lines 1220 and
1227 leaves coordinate-input equality goals unsolved.

## 2026-05-13 Section 6.3 import

`BK.MSM110.Chapter06` now also imports the Section 6.3 curvature-operator
companion.  The canonical statement layer is
`RicciFlower.RicciFlow.Evolution.CurvatureOperator`; BK keeps only
label-preserving wrappers.

Verification: the Section 6.3 wrapper passed a focused file check and targeted
module build.  The aggregate Chapter 6 import is currently blocked by an
unrelated current failure in `RicciFlower/Curvature/Components.lean`, where the
proof near lines 1220 and 1227 leaves coordinate-input equality goals unsolved.
