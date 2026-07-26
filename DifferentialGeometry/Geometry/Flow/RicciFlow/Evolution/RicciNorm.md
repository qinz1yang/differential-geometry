# RicciNorm — notes

## 2026-07-12 — short-time branch alignment

- `pair04_apply` now isolates the definitional evaluation of the pointwise tensor
  product in one explicitly typed local equality, then composes that equality instead
  of asking `rw` to unfold the opaque `Tensor0SSpace` representation.
- The result is now the public canonical `ricciPair04_apply`, reused by improved
  pinching instead of maintaining a duplicate proof.
- Obsolete simp arguments exposed by the compatibility change were removed.
- Focused verification passed without `sorry`; the local compatibility repair is
  complete (100%) and has no remaining blocker.
- This is consumer compatibility only. The headline short-time theorem remains
  complete (100%); its branch-alignment integration is about 95% pending the large
  downstream rerun.
