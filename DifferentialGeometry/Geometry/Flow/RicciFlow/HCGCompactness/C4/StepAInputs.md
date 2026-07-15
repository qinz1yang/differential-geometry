# StepAInputs.lean

## 2026-07-01, subsequence projection

Added `InjRadiusDecayInput.subseq`, the A0 decay-data projection along a
subsequence.  It reindexes the supplied distance and decay estimate and uses
`BaseInjBound.subseq` for the basepoint injectivity lower bound.

The projection is data-valued, so it is a `def`, not a theorem.  Verification
passed.

## 2026-07-01, A0 prime subsequence projection

Added `VolumeComparisonInput.subseq`, the companion projection for the
Bishop--Gromov/packing multiplicity input.  It reindexes the supplied distance
and keeps the same multiplicity function.

This keeps the Step-A honest inputs stable under later diagonal/refinement
subsequences.  Verification passed.

## 2026-07-08, joint cap correction

Corrected `VolumeComparisonInput.ballMult` so the cap is on the containing
scale `m * r <= r0`, not only on the separation scale `r <= r0`.  This matches
the volume-comparison plan's hyperbolic counterexample audit: a fixed
multiplicity bound cannot be true if `m * r` is allowed to grow without a cap.

`VolumeComparisonInput.subseq` was updated mechanically to preserve the same
joint-cap field.  Verification passed.
