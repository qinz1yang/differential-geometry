# FrameTowerRegularity

## Purpose

Transfer the joint spacetime regularity of the coordinate curvature tower to
components in an arbitrary smooth local frame.

## Current state

`frameTowerSmooth` expands each local-frame vector in the coordinate frame,
uses the all-level realization bridges on both sides, and reduces every term to
`coordTowerSmooth`. It takes both the smooth frame witness and its explicit
`C^1` downgrade, matching the Christoffel API without synthesizing hidden
regularity data. The former `[CompactSpace M]` binder was artificial: the proof
is entirely local, and focused verification passes without it. The module
artifact was intentionally not refreshed in this pass.

This producer proves regularity only. The fixed-base time/spatial derivative
swap is discharged separately by `frameTowerSwap`.

The theorem `frameTowerSmooth` is complete. This cleanup does not itself prove
the arbitrary-dimensional residual successor: that endpoint remains unstated
and therefore at theorem-level 0%; it only removes one unnecessary compactness
assumption from already-checked regularity machinery.
