# TangentPartialDiffeomorph

## Role

This module provides the coordinate-layer tangent lift needed to transport a
partial diffeomorphism without selecting a second local inverse branch.

## Current state

- `PartialDiffeomorph.tangentHome` packages the tangent map on the preimage of
  the source and the inverse tangent map on the preimage of the target as one
  `OpenPartialHomeomorph`.
- `PartialDiffeomorph.mfderiv_cont` applies the forward differential to any
  continuous tangent-bundle input whose base stays in the source, returning a
  continuous target tangent-bundle map.
- The construction only requires differentiability order at least one.
- Its inverse laws are derived from the chain rule and the original partial
  diffeomorphism inverse laws.

Focused verification passed without proof or style warnings.

## Frontier

The HCG normal-coordinate consumer must compose this tangent lift and the
product lift of `normalExpPD` with the already selected quantitative model
branch. The volume-family consumer now reuses `mfderiv_cont`; no duplicate
consumer-local continuity adapter remains.
