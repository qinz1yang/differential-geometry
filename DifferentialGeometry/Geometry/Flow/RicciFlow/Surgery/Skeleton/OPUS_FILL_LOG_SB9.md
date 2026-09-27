# SB9 — brick B9, deep-horn ball (2026-09-26)

Outcome: STOPPED, no Lean file written (README rule 8). Spatial-only target FALSE; brief's route gapped.

## Design text (DESIGN_S_FACTORY.md, no Lean signature is given for B9)
- §3 "Depth (KL 71.1)": `K` chosen so that `R_L(x) ≥ K·Λ·r⁻²` forces, for every horn point `x`:
  "The normalized ball `B_L(x, A·R_L(x)^{-1/2})` is compactly contained in `interior (hornRange c e)`",
  "On that ball, `R_L ≤ Cb(A)·R_L(x)`", "`√R_L(x)·dist_L(x, P.core c) ≥ A`"; `A := 3·D(εs)`,
  `D` = H's arm length. "Toward the singular end the bound needs the escape-radius contradiction (B9)."
- §6 row B9: "base side by the log estimate; tip side by the escape-radius contradiction
  (`TerminalCurvatureEscape:166,358`, `Perelman/CanonicalNeighborhood/TerminalScalarEscape`) with cone exclusion".

## Counterexample to the spatial formulation (horn data of `TerminalCorePresentation`, Contract/Terminal.lean:58)
- Horn end = cone `dr² + (σr)² g_{S²}`, `r ∈ (0, r₀]`, tip `r = 0` missing from `terminalRegularOpen`,
  `σ := ε̄²/100`. `R = 2(1−σ²)/(σr)²` → ∞ at the tip (`horn_scalar_diverges` holds).
- Normalized at any `x`: `u = √R(x)(r − r_x)`, cross-section radius `√2(1+σ'u)`, `σ' ≈ σ/√2`. Deviation
  from the round cylinder is a degree-2 polynomial in `u` with coefficients `≤ 2σ'`; on `|u| ≤ ε̄⁻¹` every
  `C^k` norm is `≤ 4σ'/ε̄ < ε̄`. So every horn point is the centre of a `NormalizedNeck` of precision `ε̄`,
  any order (`horn_spatial_neck` holds). Spatial κ-noncollapsing at curvature scale also holds.
- `√R(x)·dist(x, tip) = √(2(1−σ²))/σ` for EVERY `x`: scale-invariant, independent of depth.
  For `3D > √2/σ` the closed normalized ball of radius `3D` contains points converging to the tip:
  not compact, `R` unbounded on it. (a) and (b) fail at every depth, so no `L(D, ε̄)` exists.
- `D` = H's arm length (`exists_strongNeck_threshold_of_minimizing_arms`, HornNeckImprovement:249) must
  tend to ∞ as the target neck precision → 0, so `D ≫ ε̄⁻²` is the relevant regime.

## Why the brief's chain argument fails (Zeno)
- Per-step comparability `R(next) ≤ (1+cε̄)R(prev)` holds on this cone (ratio `1+2σ'ℓ`), but steps are in
  LOCAL units; in `x`-units the chain's total length is `Σ_k (1−σ'ℓ)^k ℓ ≈ 1/σ'`, finite. The chain
  reaches the tip within `x`-normalized distance `≈ √2/σ` after infinitely many steps. "Chain of length
  ≤ 3D" presupposes `R ≤ C·R(x)` on the ball, which is conclusion (b): circular.
- Self-consistent spatial bound exists only for `ε̄·D ≲ 1` (whole ball inside the `ε̄`-neck at `x`),
  useless since `D ≫ ε̄⁻¹`.
- Base side (log estimate toward `P.core c`) is fine; only the tip side is the problem.

## What a true B9 needs
- Flow input, not horn data: Perelman I 12.1 claim 2 / KL 70–71 bounded curvature at bounded distance
  for the terminal slice (derivative clause + pinching + κ on the slab, blow-up limit on a backward
  window, cone exclusion by the strong maximum principle).
- In-tree status: escape side exists (`exists_terminal_scalar_escape_radius_of_derivative_bounds`
  TerminalCurvatureEscape:166, `exists_terminal_minimizing_segments_at_scalar_escape_radius` :358,
  `exists_terminal_scalar_escape_spatial_necks` TerminalNeckEscape:27,
  `exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape` TerminalScalarRay:490); cone
  exclusion exists only abstractly (`ConeBlowupLimit.false`, Perelman/CanonicalNeighborhood/
  ConeBlowupLimitReduction:90). Its producer `ConeBlowupLimitRealization` (:105) is only reduced to
  `ParabolicConeUpgradeRealization` (ParabolicRescalingReduction:449), unproved. That producer for
  terminal slices of incoming slabs is the real B9 frontier; well beyond 1500 lines.
- Suggested restatement for the lead: B9 = terminal bounded-curvature-at-bounded-distance with explicit
  flow hypotheses (derivative clause, `PhiAlmostNonnegative`, κ on `[s−θ/Q, s)`), conclusion (a)+(b)
  with non-explicit `Cb(A)`; (c) separately from the coarse neck at `x` (one central sphere,
  `metricDistance_ge_of_separating_slices` NeckChainAxialArms:131) once (a)+(b) hold.

Compile: none (no file). Axioms: n/a. Git: no writes.
