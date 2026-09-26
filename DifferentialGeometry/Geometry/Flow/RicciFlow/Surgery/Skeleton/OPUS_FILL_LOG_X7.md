# OPUS fill log X7 — the Crossing leaf assembly `crossingContinuation_holds` (DESIGN_CROSSING_ASSEMBLY.md §2.10)

Worker: Fable 5.1, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf, HEAD e68bf6466 + lane files), started 2026-09-26 ~15:00 PDT.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\x7
(copied xp2b's `XP2B.*` scratch src/olean tree; own `deps.sh`/`cc.sh` with the same module prefix so the oleans are reusable;
uncommitted suppliers rebuilt only when their source differs from the copied one).
Target: `Surgery/Topology/CrossingContinuationLeaf.lean` (new), theorem `crossingContinuation_holds`.

## Status
- 15:00 read: DCA §0–§2, logs XA1–XA4, XP1–XP4, DESIGN_X4D §2, H14/H15/H19; the delivered statements of X0, X1, X1e, X1k,
  X2, X3p/X3, X3a's `hεX`, X4ext, X4 (statement; proof lane XP2′ still compiling at 15:00, `x4.log` empty), X5, X6b,
  `RetainedCoreHistoryExtendAtBefore` (hnc/hwit/hpinch supply), B12, F9's slab-start chain, the leaf's `CrossingContinuation`.
- Constants fixed (see "Constants" below). Writing the leaf now.

## Constants (leaf choices)
- `εbar := min coneAccuracy (min epsW (min crossingNeckAccuracy crossingWindowNeckAccuracy))` — X3a's `hεX` and X4's `hεX`
  replace the design's `windowFarAccuracy / 2` (X4 as delivered takes `ε ≤ crossingWindowNeckAccuracy`, not `hεfar`).
- `C, τ₀` from X5 at `ε`; `C1₀ = C2₀ := C`, `Cgrad₀ := ⟨C, _⟩`, `Ctime₀ := max ⟨C, _⟩ Cs_start` (`Cs_start` from
  `exists_slice_bounds_at_slab_start P₀ g₀`, F9).
- Negation tail instantiated per `n` with `Dₙ := max (n+1) Rs`, `θcapₙ := 1 - 1/(n+2)`, `q₀ₙ := max (n+1) qs_start`,
  `mcapₙ := max (n+2) ms`; after `qcanₙ`: `δmaxₙ := min (1/(n+1)) δs`, `εcapₙ := min (1/(n+1)) εs`,
  `ρmaxₙ := min (√(1/(2(n+1)qcanₙ))) ρs` (F8: `inv_two_mul_sq_lt_static_scale` then gives `hscale`).
- 15:20 lead: X4 DELIVERED (`CrossingWindowAnchorBound.lean`, 789 lines, XP2′). Built clean in my scratch chain (69 s) from
  the 789-line source; all 36 uncommitted suppliers now have `XP2B.*` oleans under `scratchpad\x7\olean` (two transient
  "failed to read Mathlib olean" failures on `PointedLimitOrientation`/`CrossingAncientLimit` re-run).
- Leaf draft written: private adapters `metricScalarAt_extendAt_eq` (X5's `hscal`, pattern of X3a's
  `scalar_ball_bound_extendAt_iff`), `le_static_scale_of_neckRadius_le` (F8 → Σ `hscale`), `exists_sliver_bad_point`
  (F9 chain `exists_derivativeBoundBefore_extend_of_slice` + X1 with `ζ = 1/(n+1)`, `ζ' = qcan/4`, `ς = 1/(n+2)`);
  main theorem: negation by `push_neg` on the whole tail, per-`n` package (event case through `prefixAt` + X1e +
  `capWindowPoint_of_prefixAt`; terminal case direct), then `choose` → the Σ context.

## X7 DONE (2026-09-26 ~15:45 PDT)
- File `Surgery/Topology/CrossingContinuationLeaf.lean` (392 lines, new, uncommitted, NOT wired into `DifferentialGeometry.lean`).
  Headline `crossingContinuation_holds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : CrossingContinuation P₀ g₀`,
  fully proved, unconditional (X4 consumed as delivered by XP2′).
- Compile (scratch chain `XP2B.*`, `lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`,
  4 threads): EXIT 0, zero output (no errors, no warnings, no linter output), 55 s. No `sorry`, no comments, no
  docstrings, no options/overrides, all non-import lines ≤ 100 characters, `git diff --check` clean.
- Axioms (scratch probe importing the leaf's scratch olean, `#print axioms`, probe deleted):
  `crossingContinuation_holds`: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
- Private adapters (all in namespace `RetainedCoreHistory`, no supplier edited):
  - `metricScalarAt_extendAt_eq`: X5's `hscal` (`metricScalarAt (stageMetric (activeStage τ) τ) ŷ = G.flow.scalar t y`).
  - `le_static_scale_of_neckRadius_le`: F8 → Σ `hscale` from `inv_two_mul_sq_lt_static_scale` with
    `ρbound ≤ ρmax ≤ √(1/(2X))`, `X = (n+1)·qcan` (`ρbound > 0` from `neckRadius_pos` and the family's radius bound).
  - `exists_sliver_bad_point`: F9 chain (`exists_derivativeBoundBefore_extend_of_slice` on the slab-start bounds of
    `exists_slice_bounds_at_slab_start`) + X1 with `ζ = 1/(n+1)`, `ζ' = qcan/4`, `ς = 1/(n+2)`; returns Σ's `hsliver`,
    `hbad` (6 clauses) and the negated three-clause conjunction.
- Route of the main proof (DCA §2.10 order): X5's `epsW, C, τ₀` and the slab-start `Cs_start` fix the leaf constants;
  `by_contra` + one `push Not` on the whole tail; per `n` the instantiation of §1 (`Dₙ, θcapₙ, q₀ₙ, mcapₙ`, then
  `δmaxₙ, ρmaxₙ, εcapₙ` after `qcanₙ`); event failures reduced to terminal form by `prefixAt` (X1e transports,
  `terminalNoncollapsedBefore_prefixAt`, `capWindowPoint_of_prefixAt` for the contrapositive of the bad predicate);
  `choose` → the Σ context (with the extra per-`n` clause negation `hclause`); `Rₙ → ∞`, `Rₙtₙ → ∞` (X0),
  `Rₙ(tₙ−t₀ₙ) → 0`; `Kₙ = extendAt`, `τₙ`, `ŷₙ` (cast, HEq); age split on a subsequence `σ₀` BEFORE the limit
  (`Filter.frequently_or_distrib` + `extraction_of_frequently_atTop`); X2 `exists_strictMono_maximal_depth` with
  `E σ T := DepthExtendable (K ∘ ·) τ ŷ R σ T` (`mono_depth`/`comp`/`congr`), base case X3; finite `T*`: X4 then X4ext
  give `E (σ ∘ ψ₂) (T* + 1/(32(Ctime+1)(M+1)))`, contradicting maximality with `χ := ψ₂`; infinite: X5 on `K ∘ σ`
  (`hderiv` via B12 at constants `(2Ctime, 2qcan)`, `Cq = 2`; `hnc`/`hwit`/`hpinch` from XA4's
  `RetainedCoreHistoryExtendAtBefore`), one index from the eventual clause, X6b `canonical_clauses_of_extendAt`
  (`C ≤ C1, C2, Ctime, Cgrad`, `τ₀ ≤ τmin`) contradicts `hclause`.
- Deviations from DCA: (1) `εbar = min coneAccuracy (min epsW (min crossingNeckAccuracy crossingWindowNeckAccuracy))`
  (no `windowFarAccuracy/2`: X4 as delivered takes `ε ≤ crossingWindowNeckAccuracy`); (2) `Cgrad₀ = ⟨C, _⟩`,
  `Ctime₀ = max ⟨C, _⟩ Cs_start` as ℝ≥0; (3) `ρmaxₙ = min √(1/(2(n+1)qcanₙ)) ρs` (F8 with the square root spelled
  out); (4) no supplier statement needed an adapter beyond the three private lemmas above. No supplier file touched,
  no private lemma copied, no deferred merge.

## Skeleton edit text (for the acceptance lane; I did not touch `PoincareEndgame.lean` or `DifferentialGeometry.lean`)
In `Surgery/Skeleton/PoincareEndgame.lean` add the import
```lean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
```
and replace lines 44–46
```lean
theorem crossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CrossingContinuation P₀ g₀ :=
  crossingContinuation_holds P₀ g₀
```
Root aggregate: register `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf`
and every uncommitted supplier below (36 modules; the order is a valid build order, produced by the scratch `deps.sh`):
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingBadPoint
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixInvariants
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialWindowScalarBound
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingBaseSliceBound
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingPersistenceInputs
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitShiftedConvergence
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalPointedFlowLimit
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionLocalLimitDepthSchedule
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroScalarBound
    import DifferentialGeometry.Topology.Sequences.NestedSubsequence
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTimeZeroBound
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingDepthExtension
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLimitOrientation
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitBaseScalar
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimit
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalWitnessTimeRestrict
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingClauseTransport
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowScalarBound
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowScalarBoundNeckAlternatives
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitWindowTransfer
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitWindowNeckAlternatives
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingMaximalWindow
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckAlternativesLocalPullCompact
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionNeckAlternativesCompact
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowBallCapture
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCloseComparison
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSliceComparison
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAnchor
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorTraceScalar
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalPointedFlowLimitNoncollapsing
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenClosedGluing
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingWindowAnchorBound
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
