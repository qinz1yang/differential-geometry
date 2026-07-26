# TensorBackedReaction

## 2026-07-12 branch-alignment compatibility

`tensor02OfRawAt_realizes` now uses the definitional evaluation of the curried/uncurried raw
bilinear tensor, so its old broad `simp` proof was replaced by `rfl`. Focused verification and
targeted build passed. The realization theorem is complete (100%); the Hamilton endpoint remains
separate.
