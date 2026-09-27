# S13 (queue 13a) — spatial canonical witness

- 2026-09-25: `Perelman/CanonicalNeighborhood/SpatialCanonicalWitness.lean` (defs) compiles clean
  (`lake env lean`, 0 diagnostics).
- `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessProjection.lean` compiles clean in a
  concatenated scratch copy (no olean for file 1 without a lake build); axioms of the projections:
  propext, Classical.choice, Quot.sound.
- `SpatialNeck.exists_neckBuffer_pullback_bound` already existed (`Geometry/Neck/SpatialNormalization.lean`);
  only the scalar twin was new: `Geometry/Neck/SpatialSourceBounds.lean`
  (`SpatialNeck.scalar_upper_bound_neckBuffer`), compiles clean, same three axioms.
- Not wired into the root aggregate (lead).
