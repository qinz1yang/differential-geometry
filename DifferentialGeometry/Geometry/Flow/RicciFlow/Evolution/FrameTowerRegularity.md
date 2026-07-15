# FrameTowerRegularity

## Purpose

Transfer the joint spacetime regularity of the coordinate curvature tower to
components in an arbitrary smooth local frame.

## Current state

`frameTowerSmooth` expands each local-frame vector in the coordinate frame,
uses the all-level realization bridges on both sides, and reduces every term to
`coordTowerSmooth`. It takes both the smooth frame witness and its explicit
`C^1` downgrade, matching the Christoffel API without synthesizing hidden
regularity data. Focused verification and the targeted module build passed.

This producer proves regularity only. The fixed-base time/spatial derivative
swap is discharged separately by `frameTowerSwap`.
