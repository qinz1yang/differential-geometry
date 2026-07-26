# ProductNablaLeibniz

## 2026-07-12 — short-time branch alignment

- The Leibniz realizer proof now changes once to the fiber-level sum of reindexed products, then uses the project-native reindexing and tensor-product evaluation APIs.
- Obsolete `Fin.coe_*` proof steps were replaced by the current `Fin.val_*` API while preserving the index argument.
- Focused verification passed without `sorry`; no local blocker remains.
