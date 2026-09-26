# B8 — canonical witness at the base of the ancient limit, pulled back to the approximants (2026-09-26)

- Start. Read AGENTS.md, NAMING §2–6, Skeleton/README, DESIGN_CROSSING (B8, F4, F8), logs B6B/B6C,
  `AncientPointedFlowLimitCurvature.lean`, `TracedRegionAncientLimit.lean` (headline statement),
  `AncientCanonicalNeighborhood.lean`, E3 (`CanonicalAlternativeComparisonTransport.lean`), Lane T,
  L7, `UniformKappaCanonicalThreshold.lean` (Deep pattern), `CrossingContinuation` (current).
- Route decision (deviation from the brief, reason): the Deep leaf does NOT transport a limit witness
  through E3; it builds a `WindowedModelWitness` (closeness to a κ-solution model at accuracy δ)
  on the approximant and applies `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts`
  (`WindowedBufferedCanonical.lean:20`), whose round and non-round branches cover all four
  alternatives (F8 disappears: positive/round handled). B8 does the same with model := the ancient
  limit `flowOfMetric ancientTimeInterval P G hsol` (B6c's κ-solution), embedding := B6a's
  convergence partial diffeomorphism `F.partialDiffeomorph (ψ i)`, comparison from
  `eventually_metricComparisonOn_of_local_flow_convergence` (`CompactTimeComparison.lean:23`,
  spatial C^p convergence uniform in t ⇒ `MetricComparisonOn` with genuine time jets).
  Orientation: the transfer only needs `TangentOrientationSection` of the MODEL (the limit); the
  preservation clause of `OrientedWitness` is unused by the proof. Taken as hypothesis (a global
  section on the limit cannot be pulled back from the approximants without a global map).
- (+~1h) `Surgery/Topology/AncientLimitCanonicalWitness.lean` compiles in-repo (all imports have
  oleans; `LEAN_NUM_THREADS=2 lake env lean`, no output). Proved:
  `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness` (the Deep transfer
  with only a model orientation) and the old-base headline
  `exists_canonicalWitness_of_ancient_pointed_flow_limit`: ∀ ε ∈ (0,1/11), ∃ C ≥ 1, τ₀ = δ(ε)⁻¹+1,
  ∀ B6a/B6b data + current-slab identification + B6c's κ-solution + orientation of the limit,
  if eventually `[tₙ − τ₀/Rₙ, tₙ] ⊆ carrier` and `(tₙ − τ₀/Rₙ, tₙ) ⊆ regular` then eventually along
  `f ∘ ψ` a `CanonicalWitness (S n) ε C C yₙ tₙ` with `capTubeHasNeckChart ε`.
  Age arithmetic (replaces F4's τ₀ = 2·C2can+1): on `IncomingSlab` (`closedOpen a s`) the window
  condition is exactly `τ₀ ≤ Rₙ (tₙ − a)`, τ₀ depending on ε only.
- Next: young bases (derivative + gradient only) through the survivor flow `h k n` itself.
- (+~2h) Young bases done through the survivor flow itself: the same limit comparison is taken
  against `h k n` (local flow on `W k n`, a genuine Ricci flow on `[−(k+2), 0]` across surgeries),
  giving a `WindowedModelWitness` for `{h k n}` at `(yₙ, 0)` (embedding = `F.partialDiffeomorph`
  restricted to `W` via an open-inclusion partial diffeomorphism); its canonical witness's
  `time_derivative`/`gradient` fields are transported to `S n` at `(yₙ, tₙ)` by the current-slab
  identification on a left neighbourhood of `s = 0` only (`derivWithin_parabolic_scalar_Iic`,
  `scalar_gradient_bound_of_localPull_scaleMetric`). No age condition.
- DONE. File `Surgery/Topology/AncientLimitCanonicalWitness.lean` (812 lines), in-repo compile
  `LEAN_NUM_THREADS=2 lake env lean <file>`: no output. Scratch copy (scratchpad) with
  `linter.mathlibStandardSet` + `#lint`: 0 errors, 14 linters, 13 declarations; axioms of the four
  public theorems: propext, Classical.choice, Quot.sound. Names unique library-wide. Not registered
  in the root aggregate (no git writes by this lane).
- Public theorems (namespace `…Perelman.CanonicalNeighborhood.FiniteHorn`):
  1. `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness` (Deep transfer,
     model orientation only; should be promoted next to `WindowedBufferedCanonical.lean`).
  2. `exists_canonicalWitness_of_ancient_pointed_flow_limit` (old bases: witness, τ₀ = δ(ε)⁻¹+1).
  3. `eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit` (all bases: `∂ₜR` and `∇R`
     with the same C).
  4. `canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds` (packs 2+3 into the exact
     per-point clause of `CanonicalBoundsOn`, constants C ≤ C1, C2, Ctime, Cgrad, τ₀ ≤ τmin).
- Inputs NOT supplied by B6b/B6c as they stand (assembler must supply): (a) `IsSolutionOn` of
  `{h k n}` on `closed (−(k+2)) 0` (B6b has it internally, input `hsol` of B6a — export it);
  (b) `TangentOrientationSection` of the limit `P.M`; (c) B6c's κ-solution statement needs B6c-κ
  and B6d (open, see B6C log); (d) the link `stageMetric (activeStage tₙ) = G.flow.base.metric` on
  the slab and `stageDomain ⊇ slab carrier`, and `R n = G.flow.scalar tₙ yₙ`.
