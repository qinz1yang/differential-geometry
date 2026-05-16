# CotangentRiemannian

## 2026-05-15 sharp evaluation helper

- Added `cotangentSharp_inner_eval`, the slot-evaluation form of
  `cotangentSharp_inner`.
- This is the convenient rewrite for comparing a sharped one-form field with
  the original one-form evaluation on a tangent slot.
- Verification passed for this file.
- Remaining frontier is not in this file: the next needed API is smoothness of
  the sharped one-form field `fun y => cotangentSharp g y (alpha y)` from a
  smooth one-form field and smooth metric.
