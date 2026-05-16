# TensorRS regularity notes

## 2026-05-14: Consume tensor local-frame layer

Worked:

- `TensorRS.lean` now relies on the extracted
  `Tensor/RSTensor/LocalFrameRegularity.lean` import through the `(0,s)`
  regularity layer.
- The mixed regularity proof still owns only the Hom-derivation and
  connection-specific scalar smoothness assembly.
- Added the local linter setting needed by the existing uniform section
  variable shape.

Verification passed.

Lesson:

- Mixed tensor regularity should consume tensor/Hom evaluation smoothness from
  the lower tensor layer and reserve this file for the connection derivation
  proof.
