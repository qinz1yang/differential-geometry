# MSM110 Chapter 6

## 2026-05-31 Retired Outline Wrappers

Section 6.1, 6.3, 6.4, and 6.7--6.10 wrappers were removed from the chapter
index because they only depended on theorem-label outline modules or open
global inputs outside the HPR-only cleanup surface.  Future book-facing
wrappers should be reintroduced only when they point at proved RicciFlower
producer theorems or explicitly accepted final black-box interfaces.

Focused verification previously passed for the chapter index before the
HPR-only pruning.  Recheck the BK wrapper only if this branch is meant to keep
BK as a build target.

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
