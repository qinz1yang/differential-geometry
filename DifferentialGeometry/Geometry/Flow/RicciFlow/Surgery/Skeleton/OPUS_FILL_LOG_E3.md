# Lane E3 log (cap alternative under one comparison, general time)

- 2026-09-26: generalized in place (implicit `t₀`, same names, time-0 consumers unify):
  `StrongNeck.transport'` (NeckTransportDecoupled), `StrongNeck.exists_transport_of_local_comparisons`
  (LocalNeckTransport), `StrongNeck.axial_fderiv_eq_of_right_trans`, `orderedNeckChainTransport`,
  `LocalCap.map` (CanonicalCapTransport). No corollaries needed; `comparison_jet_zero_contDiffOn`
  left private (unused).
- New `Perelman/CanonicalNeighborhood/CapComparisonTransport.lean`: `MetricComparisonOn.restrictTimes`,
  `LocalCap.exists_transport_tolerance_of_metricComparisonOn`,
  `exists_tolerance_depth_image_of_metricComparisonOn`,
  `LocalCap.exists_deep_transport_tolerance_of_metricComparisonOn`.
- New `Perelman/CanonicalNeighborhood/CanonicalAlternativeComparisonTransport.lean`:
  `CanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn` (neck and cap; positive and
  round excluded: they need a global `connectedComponent` equality a local comparison cannot give).
- Compiled read-only against a scratch olean overlay `D:\e3o` (junctions + copied oleans, edited
  modules compiled there): all five files exit 0, no warnings. Axioms: propext, Classical.choice,
  Quot.sound. Not registered in the root aggregate; dependents of the edited modules not rebuilt.
