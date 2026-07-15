# ComponentConvAssembly status

## 2026-07-09: order-dependent reference endpoint

The fixed-reference assembly remains intact. The file now also contains the checked refs path
`exists_pairs_refs` -> `pairs_pinned_refs` -> `exists_tower_refs` -> `exists_patch_refs` ->
`metricCInf_refs`. Bounds may be measured against `gRef r` for every `q <= r`, while the output
`MetricCInfConvOnCompacts` uses one fixed `gBase`.

The long good-frame estimate was not duplicated: private `TowerExtractor` and
`exists_patch_core` contain the common proof, and the old/new public wrappers provide their
respective tower extractors. Focused verification and the targeted module build passed. No new
`sorry` or mathematical frontier was introduced.
