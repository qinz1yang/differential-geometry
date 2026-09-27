# Lane A2 log: Kleiner–Lott 71 input from a chain of necks at fixed accuracy

- 2026-09-26: `Surgery/Topology/NeckChainAxialArms.lean` (one new file, not wired, not lake-built).
- SpatialOrderedNeckChain is too weak for the non-compounding bound: it states no overlap of consecutive slabs, no linear order, and no separation (a tube wrapping S^2 x S^1 defeats any metric-only argument). The chain input is taken as a neck necklace: `c : ℕ → M`, `nk k : SpatialNeck g eps (c k)`, `c (k+1) = (nk k).map ((nk k).center, L)`, scalar `R(c i₀) ≤ 4 R(c k)`, and the topological input "central sphere k separates c i from central sphere k+1" (Disjoint with connectedComponentIn), plus reach `D ≤ √R(x) d(x, c 0)`, `D ≤ √R(x) d(x, c m)`.
- Reusable lemma `metricDistance_ge_of_separating_slices`: Σℓ_j − 2Σe_j ≤ d(c i, c m) via minimizing arms cut at each separating slice; errors are additive per step, so no compounding.
- Angle: `arccos (9/2 · 14/(√(1−eps) L) − 1)`; corollary uses eps = 1/3000, L = 100 (angle ≥ π/2); small D (9D < 3000) falls back to the single-neck lemma.
- Compile: scratch LEAN_PATH over D:\differential-geometry-pc oleans (same sources) with HornNeckImprovement/NeckRegionAxialArms oleans built into a junction mirror D:\pc3chain-mirror2. Axioms: propext, Classical.choice, Quot.sound.
