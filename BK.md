# BK

## 2026-05-12 MSM110 companion root

The `BK` library is a thin book-companion layer. It imports chapter companion
indices and maps book labels to theorem names whose proofs live in
`RicciFlower`.

Verification passed.

## 2026-05-15 MSM135 Chapter 6 companion root

The `BK` root now imports `BK.MSM135.Chapter06`.  This is a first-pass
statement companion for MSM135 Chapter 6, with proofs remaining in or deferred
to `RicciFlower.RicciFlow.Perelman`.

Verification passed for `BK.lean`.

## 2026-05-12 MSM110 Chapter 6 root

The `BK` root now imports `BK.MSM110.Chapter06`, which currently exposes the
Section 6.1 scalar curvature evolution wrapper. The proof remains in
`RicciFlower.RicciFlow.Evolution.Scalar`.

Verification passed.
