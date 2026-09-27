# B6c-κ — parabolic κ-noncollapsing of the ancient pointed limit from local approximants (2026-09-26)

- Start. Read AGENTS.md, NAMING §2–6, Skeleton/README, review F digest item 3, OPUS_FILL_LOG_B6C /
  B6B2, `TracedRegionAncientLimitData.lean` (B6b', uncommitted), `AncientPointedFlowLimitCurvature.lean`,
  `Noncollapsing/Parabolic.lean:43`, `KappaSolutions/PointedNoncollapse.lean`, both `ReferenceChange.lean`,
  `CompactTimeComparison.lean:23`, `OpenTimeJetExtension.lean:28`, `ParabolicNoncollapseLimit.lean`,
  `AncientLimitCanonicalWitness.lean` (B8 plumbing).
- Route decision. The reference problem of the B6C log is already solved in the tree:
  `exists_metric_time_jets_extension_on_compact` (`OpenTimeJetExtension.lean:28`) converts the
  `G 0`-referenced local convergence into closeness measured with `G t` itself, uniformly in
  `t ∈ [c, b]` (this is the reviewer's uniform reference conversion), and
  `eventually_metricComparisonOn_of_local_flow_convergence` (`CompactTimeComparison.lean:23`) packages
  it as `MetricComparisonOn G (h k n) E K J order eps` for LOCAL approximants on `W k n` (B8 uses it
  with `E i = F.partialDiffeomorph ∘ (opensInclusion W).symm`, `AncientLimitCanonicalWitness.lean:672`).
  With a `MetricComparisonOn` on `K = closedBall_{G σ}(z, r)`, the global template
  `ConvergesOn.isKappaNoncollapsed_of_isParabolicallyRmControlled` (`ParabolicNoncollapseLimit.lean:115`)
  runs verbatim: curvature transfer `rmNormSq_image_le_of_rmNormSq_le` (factor 324, fixed eps ≤ 1/10,
  so the test radius shrinks to r/5), ball capture `ball_subset_image_of_metric_lower_crossModel`,
  volume transfer `MetricComparisonOn.volume_image_le`. Loss: κ' = κ/250 (same as the global template).
  Extra local step: compactness of the approximant closed ball (B6b' test hypothesis): capture with
  L = 10/9 gives ball(9r/40) ⊆ E''closedBall_G(z, r/4) (compact), closedBall(r/5) closed inside it.
- Heartbeat note: one monolithic proof hit the 200000 declaration budget (nlinarith over a heavy
  context, and explicit `metricRm04At` terms): split into a transfer lemma + small private real lemmas;
  no option override.
- Owner directive (mid-lane) received: deliver unconditionally from B6b' exports + convergence.
  Delivered a composed theorem in B6b''s exact output shape. The ONLY input not in B6b''s export is
  completeness of the earlier slices `G t` (t < 0); it is not derivable from B6b' data (B6b' gives
  curvature bounds `K(A, T)` that grow with the radius `A`, so `G t ≥ c·G 0` only on bounded regions
  with `c` depending on the region; an incomplete `G t` would make the parabolic ball non-precompact
  and the B6b' test inapplicable). It is derived here from B6c's
  `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete` (Rm ≥ 0 from the approximant
  pinching `hpinch`, `Q → ∞`, `AdmissiblePinchingFunction Phi`), the same route as DESIGN_CROSSING B6c
  and the global template (which also assumes completeness).
- DONE. File `Surgery/Topology/AncientPointedFlowLimitNoncollapsing.lean` (430 lines). Public:
  1. `MetricComparisonOn.volume_ball_ge_of_image_parabolic_volume_bound` (N M : Type u, 3-manifolds):
     `C : MetricComparisonOn G g E (closedBall_{G t}(p, r)) (Icc (t − r²) t) 2 eps`, `G t` complete,
     closed ball ⊆ `E.source`, `0 < eps ≤ 1/10`, `40 eps ≤ 1/r²`, `0 ≤ κ`, `r⁴|Rm_G|² ≤ 1` on
     `B_{G t}(p, r) × [t − r², t]`, and the approximant test at `(E p, r/5)` (compact closed ball +
     curvature control ⇒ `ofReal(κ (r/5)³) ≤ vol`) ⇒ `ofReal(κ/250)·ofReal r³ ≤ vol_{G t}(B(p, r))`.
     Capture with L = 10/9 (ball 9r/40 ⊆ E''closedBall(r/4)) gives the compactness of the approximant
     closed ball.
  2. `isKappaNoncollapsed_of_local_flow_limit`: one parabolic ball of `{G}` on `ancientTimeInterval`.
  3. `parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit`: `∀ ρ > 0, … (κ / 250) ρ`, inputs:
     B6b' (ii) `hsol`, (v) `hnc` with general `radii → ∞`, B6b's `f, F, V (monotone, covering), N,
     φ, hφ, hφF, G, ψ, hconv`, and `hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t)`.
  4. `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit`: B6b''s exact shape
     (`radii = ρ₀·√Rₙ`, `hRlim`, `MetricComplete P`, `ConnectedSpace P.M`, `V k = B(p∞, (k+1)/2)`,
     `G 0 = P.metric`) + pinching (`hQ`, `hPhi`, `hpinch`, B6c's inputs) ⇒ `∀ ρ > 0, … (κ / 250) ρ`.
  Loss κ' = κ/250 (factor 5 radius shrink from the fixed-eps curvature factor 324, factor 2 volume).
- Verification: in-repo read-only `LEAN_NUM_THREADS=2 lake env lean <file>`: no output. Scratch copy
  (outside the tree, removed): `#print axioms` on all four: [propext, Classical.choice, Quot.sound];
  `linter.mathlibStandardSet` + `#lint`: 0 errors on 8 declarations, 14 linters. Assembly check
  (scratch module = B6b' uncommitted file + this file + an `example` destructuring B6b''s headline
  and feeding it to theorem 4, leaving only `hQ hPhi hpinch`): compiles clean. Lines ≤ 100 except
  imports. Public names unique library-wide. Not registered in the root aggregate (lead).
