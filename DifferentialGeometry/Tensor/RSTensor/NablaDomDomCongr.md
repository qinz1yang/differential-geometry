# NablaDomDomCongr

## 2026-07-12 — short-time branch alignment

- Slot-reindexing evaluations now explicitly enter the fiber-level `ContinuousMultilinearMap.domDomCongr` expression and then use `Tensor0SSpace.domDomCongr_apply`.
- This avoids relying on the old section-topology definitional equality.
- Focused verification passed without `sorry`; no local blocker remains.
