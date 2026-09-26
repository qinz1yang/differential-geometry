# SG3 — spatial witness ε-monotonicity (gap G3 of SFR)

- 2026-09-26: new file Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMonotone.lean (195 lines).
  mono_eps for SpatialOrderedNeckChain/LocalNeck/LocalCap (via SpatialNeck.mono), SpatialRoundComponent
  (MetricComparisonOn.mono, order ⌈ε⁻¹⌉ decreases), SpatialCanonicalAlternative, SpatialCanonicalWitness,
  capTubeHasNeckChart.mono_eps (alpha ≤ alpha' < 1/11); predicates IncomingSlab.spatiallyCanonicalBefore_mono_eps,
  spatiallyCanonicalOn_mono_eps, RetainedCoreHistory.eventSlabsSpatiallyCanonical_mono_eps.
  All fields monotone; no enlargeConstants needed. lake env lean (+mathlibStandardSet): exit 0, no output.
  Axioms: propext, Classical.choice, Quot.sound. Not yet in root aggregate (lead wires).
