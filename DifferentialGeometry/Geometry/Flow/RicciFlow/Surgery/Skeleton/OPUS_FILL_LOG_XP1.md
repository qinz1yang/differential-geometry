# OPUS fill log XP1 — bricks P3, P2, P1s, X4-ev of DESIGN_X4D.md (2026-09-26)

Worktree `D:\differential-geometry-pc3`, base e68bf6466. Read-only compiles only.

## P3
- File: `Perelman/StandardSolution/StandardCloseComparison.lean` (new). Statement copied verbatim from §1.1.
- Proof: η := min η_lower η_upper from `StandardActionComparison.lean:40, 115`; `1 ≤ R_Q` from
  `PartialStandardSolution.one_le_scalar` (domain via `uniformStandardLifetime_slab` + `Icc_subset_lifetimeInterval_iff`);
  `cap ≤ Λ g_Q` from `standard_metric_bounds_on_shorter_windows` (`MetricUniformEquivalentOn`, first clause);
  `Lc := 2Λ` (so `Lc² = 4Λ² ≥ 2Λ`), not `√(2Λ)`: an internal constant choice, statement unchanged.
- Compile: exit 0, no warnings (58 s). Statement verbatim §1.1.

## P2
- File: `Surgery/Topology/CapWindowBallCapture.lean` (new). DEVIATION (placement only): the design suggested
  `Geometry/Comparison/`, but the statement names `standardCapWindow`, `ThreeModel`, `ThreeSpace`, `StandardCap.metric`
  (all under `Geometry/Flow/RicciFlow/Surgery`), so a `Geometry/Comparison` home would import Flow back. Namespace
  `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`. Statement verbatim §1.2.
- Proof: `ball_subset_image_of_metric_lower_on_opens` with `g := scaleMetric lam g`, `h := StandardCap.metric`,
  `R := r`, `L := Lc`; compactness `StandardCap.isCompact_metric_closedBall z₀ r.toNNReal` (defeq);
  radial containment from `radial_difference_le_edist`; ball rescaling by `riemannianBallOf_scaleMetric`
  (`Geometry/Metric/Distance/Ball.lean:55`).
- Compile: exit 0, no warnings (20 s).

## X4-ev
- File: `Surgery/Topology/SurvivorTraceScalar.lean` (new, next to TimeControl). Statement verbatim §1.6.
- Proof: build a second `BackwardPointTrace` from the survivor maps (`point j := f ⟨j, …⟩ x`, endpoint from `hlast`,
  crossings from `hcross`), identify `Bt.point = f j₀ x` by `BackwardPointTrace.point_unique` (`Backward.lean:27`),
  `w ∈ stageDomain (activeStage w)` by `activeStage_mem`, then `hid j₀`, `metricScalarAt_scaleMetric`,
  `metricScalarAt_localPull`, `mul_inv_cancel_left₀`.
- Compile: exit 0, no warnings (34 s).

## P1s
- File: `Surgery/Topology/CrossingPersistenceInputs.lean` (new, the file the design names). Conclusion verbatim §1.3.
- DEVIATION (binders only, strict generalization): stated with explicit minimal hypotheses instead of the whole Σ
  `include` block: `hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory)` (= `(hH n).1`),
  `hqcan : ∀ n, (n:ℝ)+1 ≤ qcan n` (= `(hq n).1`), and Σ's `hpar`, `hscale` verbatim. Reason: stated inside the Σ block,
  the theorem trips `unusedSectionVars` for 15 included hypotheses (observed in the probe), a linter-gate failure.
  Probe (deleted) confirmed the verbatim §1.3 statement inside the verbatim Σ block (`DCA:258–307`, `εfar` variable)
  closes as `exists_capWindow_persistence_inputs_eventually (fun n => (hH n).1) (fun n => (hq n).1) hpar hscale`.
- Proof: `a₀` from `exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀` (`HamiltonIveyPinching.lean:666`);
  eventualities from `1/(n+1) → 0`; `qcan ≤ Cbirth·λ` from `λ ≥ (n+1)qcan` and `Cbirth(n+1) ≥ 1`;
  `1 ≤ a₀λ` from `λ ≥ (n+1)qcan ≥ n+1` and `a₀(n+1) ≥ 1`.
- Compile: exit 0, no warnings (36 s).

## Axioms (probe copies with `#print axioms`, deleted)
All four: `[propext, Classical.choice, Quot.sound]` (shared-olean caveat: only a fresh build certifies).

## Summary
| Brick | File | Lines | Status |
|---|---|---|---|
| P3 | `Perelman/StandardSolution/StandardCloseComparison.lean` | 59 | clean |
| P2 | `Surgery/Topology/CapWindowBallCapture.lean` | 50 | clean |
| P1s | `Surgery/Topology/CrossingPersistenceInputs.lean` | 73 | clean |
| X4-ev | `Surgery/Topology/SurvivorTraceScalar.lean` | 51 | clean |
Not registered in `DifferentialGeometry.lean` (lead's job). No committed file touched. Deferred merges: none.

## H15 revision (digest `Surgery/consult/H15-crossing-x4d-sigma-review-digest.md`)

### P3: unchanged (kept `1/2 ≤ R`), with evidence
- The proof does NOT take `R_Q ≥ 1` from `:20`. It uses the compiled library theorem
  `PartialStandardSolution.one_le_scalar (S) (t) (ht : t ∈ S.domain) (x) : 1 ≤ metricScalarAt (S.metric t) x`
  (`Perelman/StandardSolution/StandardScalarLower.lean:88`), valid for EVERY partial standard solution; `Q` is a
  universal input of P3, and `:20`'s `Q : StandardSolution` is the same type. The domain membership `τ ∈ Q.val.domain`
  comes from `uniformStandardLifetime_slab` (`T < 1 = uniformStandardLifetime`).
- So the normalization is not a bet: P3's axiom closure (which contains `one_le_scalar`) is
  `[propext, Classical.choice, Quot.sound]`. Replacing it by `c*/(1−τ)` would only weaken the constant
  (`λ·c*/2 ≤ R` instead of `λ/2 ≤ R`). If the lead still wants the `c*` form for uniformity, it is a corollary
  (`c* := 1`); I did not add it. `λ ≤ 2A'·Rₙ` in X4d-Σ therefore stands with the factor `2`.
- Constant order: P3's `Lc` depends only on `T` (used at `T = 1/2`), hence is independent of `D₂`; X4d-Σ fixes `Lc`
  first, then `r > 2·Dd·Lc·√(2A')`, then `D₂ = D₁ + 1 + r`.

### P2: generic theorem kept, composite corollary ADDED
- `ball_subset_image_capWindow_of_scaled_lower` is generic in `M` and the injective local diffeomorphism
  `Ξ : standardCapWindow D → M`; the ball is the intrinsic ball of `g` on the WHOLE `M`, and the first-exit argument on
  the compact cap sub-ball `closedBall_cap(z₀, r)` is inside `ball_subset_image_of_metric_lower_on_opens`
  (`Geometry/Comparison/OpenEmbeddingBallCapture.lean:52`). Hence no outside shortcut is possible provided `M` is the
  actual slice carrier.
- NEW `ObservedHistory.ball_subset_image_backwardSurvivor_capWindow` (same file): the instance on the composite
  `F = fun w => (Ξ w).val.val : standardCapWindow D → (H.stage last).Carrier`, for `:20`'s
  `Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G`, with local-diffeomorphism and
  injectivity from `CapWindowFlowPushforward.lean:72, 83`; `hlower` is stated on
  `localPullMetric (scaleMetric lam g) F`, which is `S.base.metric τ` by
  `window_metric_eq_localPullMetric_scaleMetric` (`CapWindowFlowPushforward.lean:229`) with `g := (G n).flow.base.metric v`.
  Conclusion: `riemannianBallOf g (F z₀) (r/(Lc√lam)) ⊆ F '' {‖u‖ ≤ ‖z₀‖ + r}` in the actual slice.
- Compile: exit 0, no warnings (43 s). Axioms `[propext, Classical.choice, Quot.sound]`.

### P1s: conclusion extended to all non-point binders of `:20`; per-point supply lemma added
- `exists_capWindow_persistence_inputs_eventually` now also takes Σ's `hrec`, the slab match
  `hGinit` (= `(hG n).2`), `hslabs` (= `(hslabs n).2.1`), `hbefore` (= `⟨(hbefore n).1, (hbefore n).2.2.1⟩`), and its
  eventual clause additionally returns: `0 < qcan n`, `IsCanonicalCutoffRecordFamily`, slab initial-metric match,
  `EventSlabsDerivative Ctime (qcan n) last`, and for every slice `time last < v ≤ t₀ n`: `v < s n` (target strictly
  inside the slab) and `(G n).DerivativeBoundBefore Ctime (qcan n) v` (current bound, threshold `qcan`, via
  `derivativeBoundBefore_mono`). Probe in the verbatim Σ block (deleted) elaborated the call
  `exists_capWindow_persistence_inputs_eventually (fun n => (hH n).1) hrec (fun n => (hG n).2)
  (fun n => (hslabs n).2.1) (fun n => ⟨(hbefore n).1, (hbefore n).2.2.1⟩) (fun n => (hq n).1) hpar hscale`.
- NEW `RetainedCoreHistory.CapWindowPoint.exists_standard_comparison_anchor` (same file, generic in `k`): a
  `CapWindowPoint records k y t Dcap θ` with `Dcap ≤ D`, `θ ≤ Θ` yields exactly `:20`'s point binders at `(D, θcap := Θ)`:
  a real `BackwardPointTrace` `A`, the birth-point equation `A.point j.succ … = ((records j).static b).window x`,
  the age `t − time j.succ ≤ Θ·scale⁻¹`, and `‖x‖ < D + 1`. Use `Θ = θcap = 1/2` LOCAL (never Σ's `θcap n → 1`).
- Binders NOT in P1s (supplied by X4d-Σ / P1 themselves): `Θ = 1/2`, `C = Ctime` (`hΘ`, `hΘ1` by `norm_num`);
  `D := D₂`, `ε, η > 0` and `N` (chosen constants: `η := η₃` from P3, `N := 2`); the CWP data of the rebase point `w`
  (through the lemma above, with `Dcap := D₁ ≤ D₂`); `k := Fin.last`, `Gk := G n`, `t := v`; `hl : j.succ ≤ k` from the CWP;
  `θcap ≤ Θ` is `le_rfl`; `0 < qcan` is in the eventual clause.
- Compile: exit 0, no warnings (52 s). Axioms of both theorems `[propext, Classical.choice, Quot.sound]`.

### X4-ev: unchanged.

### Line counts after revision
P3 59, P2 73, P1s 102, X4-ev 51.
