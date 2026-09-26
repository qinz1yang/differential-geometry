# SB12 — brick B12, fine cut necks on long terminal slabs (2026-09-26)

Worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf` @ a161fc07e). Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`. No git writes, no `lake build`.

## Progress
- start. Read AGENTS.md, NAMING §2–6, Skeleton/README, SFR log (G1), DESIGN_S_FACTORY §3/§6, suppliers
  BoundedCurvatureAtDistance (BCD), HornSeparationSliceTransfer (B10b), HornCentralSphereSeparation (B10),
  HornNeckCoordinates, HornNeckEssentiality, TerminalNeckNormalization:434, HistoryNoncollapsingToSlab:95,
  LocalPropagation:347/619, Contract/Terminal (presentation fields), SB9 log.
- Findings before writing:
  1. B10b's threshold `Q` (per `P c e`) is `2(max C 0 + 1)` with `C` a bound of the scalar on the WHOLE
     core `P.core c` (HornNeckCoordinates:217). It is not controlled by `Λ·r⁻²`, so B10b's headline cannot
     give `FineCutNecks` at a threshold `Kfine·max(Λ r⁻², max q 1)`. Repair (new file 1): the neck chart is
     preconnected and centred off the core, so it misses the core as soon as every FRONTIER point of the core
     has scalar `< (1 − 4323δ)·scale` (frontier scalar `≤ Λ r⁻²` by `frontier_scalar_le`). Re-run the
     B10/B10b chain with that hypothesis instead of `Q < N.scale`.
  2. Frontier distance `> 2A/√R_L(x)` (step 2) needs no horn depth: frontier points have `R_L ≤ Λ r⁻²`;
     at slices near `s`, `scalar_le_on_ball_of_gradient_bound` around the frontier point (gradient clause)
     bounds `R_τ ≤ 6M` on a ball of radius `ρ₀/√(2M)`, `M = max(Λ r⁻², max q 1)`; `R_τ(x) ≥ K M/2` forces
     the distance once `K ≥ 18A²/ρ₀²`.
  3. BCD's `εcone` is exported after `κ C1 C2 Ctime Cgrad phi`, while F*'s `εbar` is fixed before
     `C1 C2`: composition needs BCD's `∃ εcone` moved to the front (its value is numeric, BCD:171).
- File 1 `Topology/HornSeparationFrontierScalar.lean` compiles clean (`lake env lean`, no output):
  `neck_chart_notMem_core_of_frontier_scalar_lt`, `neckCentralDomain_subset_horn_of_frontier_scalar_lt`,
  `exists_neck_coordinates_in_horn_of_frontier_scalar_lt`,
  `exists_horn_centralSphere_side_points_of_frontier_scalar_lt`,
  `exists_strongNeck_threshold_of_horn_point_at_slice_of_frontier_scalar_lt` (B10b with `Q < N.scale`
  replaced by `∀ w ∈ frontier (P.core c), 2 R_L(w) < N.scale`; `eta` now universal, stated first).
  Next: file 2 `Contract/HornFineCutNecksLongSlab.lean` (B12 assembly).
- File 2 `Contract/HornFineCutNecksLongSlab.lean` written; first monolithic main proof hit the per-declaration
  heartbeat limit (`linarith` over the large context, `set a := H.time …` shadowing `G`); split into lemmas
  (no budget option). Compiles clean.

## Outcome: B12 (long slab) PROVED, sorry-free, steps (1)–(4) all closed

### Headline (file 2, ns `…Surgery.Topology.TerminalCorePresentation`)
```
theorem exists_fineCutNecks_of_long_terminal_slab :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ (C1 C2 : ℝ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ},
      Perelman.AdmissiblePinchingFunction phi →
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ εbar : ℝ, εbar ≤ εcone →
    ∀ {εc : ℝ}, 0 < εc → εc < 1 / 2 →
    ∃ K θ : ℝ, 1 ≤ K ∧ 0 < θ ∧
    ∀ {P₀} (H : RetainedCoreHistory P₀) (hend : H.time last = H.horizon) {s}
      (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
      (hG : G.flow.base.metric (H.time last) = H.initialMetric last) (q : ℝ),
      H.EventSlabsDerivative Ctime q last → G.DerivativeBoundBefore Ctime q s →
      G.GradientBoundBefore Cgrad q s → H.EventSlabsPinched phi →
      PhiAlmostNonnegative G.flow (Ico (H.time last) s) phi →
      G.SpatiallyCanonicalBefore εbar C1 C2 q s →
      (∀ t₀ ∈ Ioo (H.time last) s, H.TerminalNoncollapsedBefore hend G hG κ ρ t₀) →
      ∀ {ε Λ} (P : TerminalCorePresentation {stage := …, slab := G, terminal := L,
          singular := hsing, parameters := parameters} ε Λ), ε ≤ eta →
      ∀ Qc, K * max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) ≤ Qc →
        2 * θ ≤ Qc * (s - H.time last) → P.FineCutNecks εc Qc
```
Explicit constants: `K = 16 + 2Λb + 2Λb²/ρ² + 2Q₀ + 18A²/ρ₀²`, `θ = 2(Λb + θB)`, where `A Q₀ θB` are
B10b-variant's constants at `delta := εc/8`, `(Qb, Λb)` BCD's constants at `(εbar, 6A)`,
`ρ₀ = localPropagationRadius Cgrad`. The D literal is F*'s `let D` with arbitrary `parameters`, so F*'s
`D.withNeckRadius ρ hρ` is the instance `parameters := stepParameters.withNeckRadius ρ hρ` (defeq).

### Steps
1. Ball bound `R_L ≤ 2·Qb·R_L(x)` on `ball_L(x, 5A/√R_L(x))`:
   `RetainedCoreHistory.exists_terminal_scalar_bound_on_ball_of_final_slab` (BCD at slices `τ → s`, with
   `S := G.closedPrefix τ`, window `2Λb < R_L(x)(s − a)`, `R_τ(x) ∈ (0.9, 1.1)·R_L(x)`, limit of slice scalars).
2. Frontier distance `> 2A/√R_L(x)`: `IncomingSlab.TerminalLimitMetric.ofReal_lt_riemannianEDistOf_of_gradientBoundBefore`
   (no horn depth: frontier scalar `≤ Λ r⁻² ≤ M`, `scalar_le_on_ball_of_gradient_bound` around the frontier point at
   a slice, `18A²M ≤ ρ₀² R_L(x)`, `7M ≤ R_L(x)`).
3. Strong necks at slices: file 1's `exists_strongNeck_threshold_of_horn_point_at_slice_of_frontier_scalar_lt`
   (B10b with the frontier-scalar hypothesis), then `RetainedCoreHistory.eventually_strongNeck_of_terminal_window`
   (window, pinching, κ via `isKappaNoncollapsed_of_terminalNoncollapsedBefore`, long slab `4θB ≤ R_L(x)(s−a)`).
4. Terminal normalization: `IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_eventually_strongNeck`
   (sequence `τₙ → s⁻`, `TerminalNeckNormalization:434` at `eps = εc/8`, `δ = εc`, `k = ⌊εc⁻¹⌋₊ + 1`).

### Composition gaps with F* (for B14; nothing here is false, these are binder-order facts)
- (a) F*'s `εP` must satisfy `εP ≤ eta`; `eta = min (min eta_sep (1/8646)) (neckModelTolerance (1/504) / 2)`
  (universal; `eta_sep` from `exists_horn_neck_end_separation_tolerance`). F* exports `εP` without this bound.
- (b) F*'s `εbar` must satisfy `εbar ≤ εcone`. BCD (`BoundedCurvatureAtDistance:171`) states `∃ εcone` AFTER
  `κ C1 C2 Ctime Cgrad phi`, but F* fixes `εbar` before `C1 C2`. BCD's value is numeric
  (`min (neckModelTolerance (1/4000000/26000)) (1/4000000/26000/64) / 13000²`), so moving its `∃ εcone` to the
  front (then B12's `∃ εcone` likewise) closes it; F* must then pick `εbar ≤ εcone`.
- (c) Long slab `2θ ≤ Q(s − a)`: not supplied by S (DESIGN_S_FACTORY §0.1); B13 removes it.
- (d) B12 reads the gradient clause on `G` and `EventSlabsDerivative`/`EventSlabsPinched` (S has them); `ρ` is S's
  noncollapsing radius (`TerminalNoncollapsedBefore … κ ε t₀`, i.e. `ρ := ε`).

### Compile / checks
- File 1 standalone: `LEAN_NUM_THREADS=2 lake env lean …/HornSeparationFrontierScalar.lean`: no output.
- File 2 imports the uncommitted `Contract/HornFineCutNecks.lean` and file 1 (no oleans): scratch concatenation
  outside the repo (committed imports + a verbatim copy of the `FineCutNecks` definition + file 1 body + file 2 body),
  `lake env lean -Dweak.linter.mathlibStandardSet=true`: no diagnostics. `#lint`: only `docBlame` on the copied
  `FineCutNecks` (inapplicable). Axioms (scratch) of the headline and all public lemmas of both files:
  `[propext, Classical.choice, Quot.sound]`.
- Lines ≤ 100 (imports excepted), no comments/docstrings/sorry/nolint/budget options; only
  `set_option autoImplicit false`. New public names grepped unique. Not registered in the root aggregate.
  Line counts 372 + 386 = 758. No git writes, no `lake build`. Scratch removed.
