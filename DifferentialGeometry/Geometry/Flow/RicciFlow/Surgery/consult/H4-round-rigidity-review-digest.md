# Review H4 (single statement: R0a space-form rigidity for the round component), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-h` @ 9f9b7d94d (`DESIGN_SMALLSCALE.md` §6.3–6.5).
Overall: **OK; do not build Cartan–Ambrose–Hicks.** The tree already has the global round cover with
the exact pullback-metric identity; simple connectivity trivialises it.

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (a) developing map / Killing–Hopf | OK, reuse | `KillingHopf.lean` and its consumer `Geometry/Metric/Sphere/Quotient/PositiveSpaceForm.lean` already export the global cover with the pullback identity (`exists_round_sphere_cover_of_constant_positive_sectional_curvature`, line 218: `IsLocalDiffeomorph`, surjective, `IsCoveringMap`, `(scaleMetric c g).inner (cover x) (dF v) (dF w) = roundMetric.inner x v w`). Verified in source. |
| (b) exponential-map route | FIX (design §6.4 wrong) | `exp` on the ball of radius `π√6` misses the antipode and degenerates at the boundary; `RoundModelCoveringBall.lean` supplies Bonnet–Myers diameter/distance transport, not a global cover. |
| (c) quotient shortcut | not available | `SpatialRoundComponent.Z` is an arbitrary compact connected constant-curvature model without a quotient field; simple connectivity of `Z` comes from `map/source_eq/target_eq` (`Z ≅ U`), not from closeness; any quotient presentation must keep the isometry with `metric`. |
| (d) traps | noted | R0a must output a metric-preserving diffeomorphism, not the sphere subtype's Euclidean chordal distance; "quotient simply connected ⇒ Γ trivial" needs a free faithful covering action (trivial action of a nontrivial group is the counterexample). |

Minimal assembly (reviewer): apply the cover theorem with `n = 3`, `c = 1/6`, `g = h`; take
`e := hcover.diffeomorphSc hlocal` (`Topology/Covering/SimplyConnected.lean:82`, needs
`[SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z]`); multiply the identity by 6 to get
`e*h = 6·roundMetric = roundSphereThreeMetric`. Remaining: instance setup, the `metricRm04At ![v,w,w,v]`
↔ `metricRm04StandardAt` conversion (`Geometry/Curvature/Naturality/Pullback/CurvatureOperator.lean:31`),
scaling. Constants: `vol_h Z = 12√6π²`, `vol_g U ≥ (2Q)^{-3/2} vol_h Z = 6√3π² Q^{-3/2}`.

Lead's additional finding: the tree's round-sphere volume is only `S²` (`TotalArea.lean:370`, `4π`);
`vol S³(1) = 2π²` is NOT in the tree, so R0b remains a genuine brick. Since the leaf only needs SOME
positive `ε`-independent constant, R0b may be delivered as the exact value or as the explicit lower
bound `vol S³(1) ≥ 4π/3` (one graph chart over the open unit 3-ball, density `(1−|x|²)^{-1/2} ≥ 1`),
which changes R1's constant to `4√3π Q^{-3/2}`; either is acceptable, the constant is recorded in
`DESIGN_SMALLSCALE.md` §6.3.

Decision: one proof lane (R0) for R0a + R0b + R0 + R1 (`SpatialRoundComponent.volume_lower_of_simplyConnected`),
unconditional, via the cover route; §6.4's exponential-map route is withdrawn.
