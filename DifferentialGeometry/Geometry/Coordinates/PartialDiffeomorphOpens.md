# PartialDiffeomorphOpens

## Role

This module provides the cross-model version of restricting a smooth partial
diffeomorphism to a source open and its image.  It is a general coordinate
API, not an HCG-specific inverse-branch assumption.

## Current state

- `codRestr_contMDiffAt` handles open codomain restriction across different
  model-with-corners structures.
- `image_opens_isOpen` proves openness of the restricted image.
- `PartialDiffeomorph.toOpensDiffeoCross` packages the restriction as a global
  diffeomorphism between open subtypes.
- `PartialDiffeomorph.opensDiffeo_mfd` identifies its derivative with the
  ambient partial-diffeomorphism derivative.

Focused verification and the targeted module build passed without proof or
style warnings.

## Frontier

The HCG normal-coordinate layer must construct an infinite-order partial
diffeomorphism on the chosen normal ball before applying this API.  The
forward and inverse smoothness theorems already exist; packaging them is the
next consumer-side step.
