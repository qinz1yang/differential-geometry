# OPUS fill log XA3 — brick X5 of DESIGN_CROSSING_ASSEMBLY.md

Worker: Opus 5.5, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf, HEAD e68bf6466), started 2026-09-26.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\xa3
Target file: Surgery/Topology/CrossingAncientLimit.lean (new).

## Status
- started: reading design §0/§2.8/§3, B13, B8, TimeControl:781, X5c, X5d.
- Scratch chain: X5c (`PointedLimitOrientation`) and X5d (`AncientPointedFlowLimitBaseScalar`) copied
  verbatim as scratch modules `XA3.*` (both compile clean, 24 s / 48 s); X5 developed as `XA3.CrossingAncientLimit`.
- §2.8 statement elaborated with a `sorry` body verbatim (only `declaration uses sorry`, 47 s).
- Constants (proof plan): `epsW` = B13's `epsW` (B13 = B11 + B6 on TimeControl:781);
  `Cw, τ₀` from B8 `exists_canonicalWitness_of_ancient_pointed_flow_limit` (τ₀ = δ⁻¹ + 1),
  `Cd` from B8 `eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit`; `C := max Cw Cd`.
  Leaf: `C1₀ = C2₀ = Cgrad₀ = C`, `Ctime₀ = max C Cs_start`, `τ₀` = X5's.

## X5 DONE (2026-09-26)
- File `Surgery/Topology/CrossingAncientLimit.lean` (241 lines, new, uncommitted, NOT wired into
  `DifferentialGeometry.lean`). Imports: B13 (`TracedRegionAncientLimitScalarBound`), B8
  (`AncientLimitCanonicalWitness`), `AncientPointedFlowLimitCurvature`, X5c
  (`Compactness/Limits/PointedLimitOrientation`, uncommitted), X5d (`AncientPointedFlowLimitBaseScalar`,
  uncommitted). Acceptance import order: X5c, X5d before this file.
- `ObservedHistory.exists_eventually_canonical_clauses_of_isTracedRegion`: §2.8 statement with ONE
  DEVIATION: the binder `(∀ n, t₀ n ≤ t n) →` (after `∀ {t₀}`) is dropped — unused (B13 needs only the
  sliver limit `R n (t n - t₀ n) → 0`); X7 simply does not pass it. Everything else verbatim
  (statement with the binder elaborated first with a `sorry` body; the final one is that text minus the binder).
- Constants: `epsW` = B13's; `Cw, τ₀` from B8:117 (`τ₀ = δ⁻¹ + 1`), `Cd` from B8:533, `C := max Cw Cd`
  (`1 ≤ C` from `1 ≤ Cw`). Leaf: `C1₀ = C2₀ = Cgrad₀ = C`, `Ctime₀ = max C Cs_start`, `τ₀` = X5's.
- Route: B13 gives W/h/blocks, f, P, F, completeness, connectedness, V/N/φ, G, ψ, hconv, κ/250 at every
  scale and the scalar bound. `hpinchW` re-derived from B13's block (a local `have` inside B13's proof,
  copied, uses `open private mem_Icc_of_mem_window`); Curvature:122 gives cone + completeness;
  X5d (`hW0` from B13's block at s = 0 plus `metricScalarAt_restrictOpen`, `hbase` from
  `metricScalarAt_scaleMetric` and the scalar hypothesis) gives base scalar 1; X5c with the stage
  orientations gives the limit orientation; Curvature:185 gives `IsAncientKappaSolution (κ/250/30³)`.
  B8 applied with `S n := closedPrefixAt`, `D n := closed (time activeStage) (t n)`, X explicit
  (passing `_` for X/D made the elaborator time out at whnf). Output subsequence `f ∘ ψ`.
  Age mode 1: B8:117's window `Icc (t - τ₀/R) t ⊆ Icc a t`, `Ioo ⊆ Ioo` holds for every n; witness
  enlarged `Cw → C`. Mode 2: the witness clause is vacuous (`closedPrefixAt` scalar at `t` is `R`,
  and `R (t - a) < τ₀`). Derivative and gradient clauses in both modes from B8:533, `Cd → C`.
- Compile: scratch module `XA3.CrossingAncientLimit` (same body; imports renamed to the scratch copies of
  X5c/X5d) with `-Dweak.linter.mathlibStandardSet=true`, `maxSynthPendingDepth=3`, 2 threads: zero
  output, 66–74 s. The in-tree file cannot be compiled read-only until X5c/X5d have oleans.
- Axioms: propext, Classical.choice, Quot.sound (no sorryAx). `#print` removed.
- Name unique library-wide.

## What X7 still needs to supply to X5 (on `K ∘ σ∞`, `Kₙ = extendAt`)
- `hR`, `hscal` (`metricScalarAt (stageMetric (activeStage τₙ) τₙ) ŷₙ = Rₙ`, via activeStage = last and
  HEq transport), `Tendsto R`, `hlt` (activeStage time < τₙ, from `hbad.1`), `hmode` (subsequence
  chosen BEFORE X2/X5), `htraced` (X2 infinite case), `κ ρ`, `hsliver` (`Rₙ(tₙ - t₀ₙ) → 0`, from Σ's
  `hsliver`: `R η ≤ 1/(n+1)`), `hnc` (TerminalNoncollapsedBefore through
  `noncollapsedBefore_closedPrefix_of_terminalNoncollapsedBefore`), `Phi`+`hpinch`, `qs ≤ Cs R`,
  `qcan ≤ Cq R` (Cq = 1), `hwit` (spatial witnesses before `t₀`, stage bridge), `hderiv` (B12).
- Then X6b per `i` with `C ≤ C1, C2, Ctime, Cgrad` and `τ₀ ≤ τmin`.
