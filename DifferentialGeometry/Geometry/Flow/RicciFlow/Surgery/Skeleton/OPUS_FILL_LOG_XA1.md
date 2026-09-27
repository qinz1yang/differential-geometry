# OPUS fill log XA1 — bricks X0, X2, X5c, X5d of DESIGN_CROSSING_ASSEMBLY.md

Worker: Opus 5.5, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf), started 2026-09-26.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\xa1

## Status
- X0: DONE (see below)
- X2: DONE
- X5c: DONE (one binder dropped, see below)
- X5d: DONE (binder list reconstructed, see below)

## X0 (2026-09-26, resumed after the killed predecessor)
- File `Surgery/Topology/InitialWindowScalarBound.lean` (141 lines; the predecessor's draft, finished).
- `RetainedCoreHistory.exists_scalar_le_before_initial_window`: statement verbatim from §2.1.
  Route: `exists_pos_le_singular_incoming_time_of_initialIdentification` (InitialCurvatureLifespan:31,
  a lower bound `aSing` on every singular time of an identified history) forces the slab index to be
  `0` when `t < η₀ := min aSing τ`; then `exists_uniform_initial_scalar_bound_of_isometry`
  (InitialScalarDerivativeBounds:191) bounds the scalar on `[0, τ]` through the identification map.
  This replaces the design's route (HistoryCurvatureTimeBound:61 + InitialSlabUniformBounds:21): same
  mathematics, but the delivered suppliers already work through `InitialIdentification`.
- Added corollaries (F2/F3 supply, sequence level, no Σ context needed):
  - `RetainedCoreHistory.tendsto_scalar_mul_time_atTop_of_inCutoffClass`: `R n → ∞` ⇒ `R n * t n → ∞`
    (M7(c)); hypotheses: class membership, terminal slab initial metric, `time last ≤ t n < s n`.
  - `RetainedCoreHistory.tendsto_scalar_mul_earlier_time_atTop_of_inCutoffClass`: adds
    `R n * (t n - t₀ n) ≤ C` and concludes `R n * t₀ n → ∞` (the `Λ ≤ R·t₀` supply for BS5/BS6;
    in Σ, `C = 1` from `hsliver` at `t' = t n`). X3's `tendsto_scalar_mul_time_atTop` is a one-liner.
- Compile: clean (standard linter set). Axioms of both headlines: propext, Classical.choice, Quot.sound.

## X2 (2026-09-26)
- Files:
  - `DifferentialGeometry/Topology/Sequences/NestedSubsequence.lean` (136 lines, namespace `DifferentialGeometry`,
    Mathlib-only imports): `exists_strictMono_forall_of_subseq_property`, `exists_strictMono_maximal_depth`
    (statements verbatim from §2.4) and a private helper `exists_strictMono_eq_comp_of_forall_ge`.
  - `Surgery/Topology/TracedRegionMaximalDepth.lean` (53 lines): `ObservedHistory.DepthExtendable` (def verbatim),
    `DepthExtendable.mono_depth`, `.comp`, `.congr` (verbatim).
- Route: enumerate ℚ (`exists_surjective_nat`), nested extractions `Φ (k+1) = Φ k ∘ χ_k` where `χ_k` is chosen
  iff some further subsequence reaches depth `q k`; diagonal `ψ i = Φ i i`. For `i ≥ k`, `ψ i = Φ k (ρ i)`
  with `ρ` strictly monotone on all of ℕ (`ρ i := i` below `k`; possible because `ρ i ≥ i`), which is where
  `htail` enters. Maximal depth: `S = {T > 0 | E (σ₀∘ψ) T}`; unbounded ⇒ left disjunct, bounded ⇒ `Tstar = sSup S`
  (`sSup` only on a bounded nonempty set; review G item 1 respected).
- Compile: both clean (standard linter set). Axioms of all five public declarations: propext, Classical.choice,
  Quot.sound. Names unique library-wide.
- No deviations.

## X5c (2026-09-26)
- File `Compactness/Limits/PointedLimitOrientation.lean` (101 lines), namespace `…Surgery.Topology`.
- `nonempty_tangentOrientationSection_of_pointedConvergence`: §2.8 statement with ONE DEVIATION:
  the binder `(hPc : MetricComplete P)` is dropped (unused; AGENTS "remove unused binders when
  compatible"; X5 simply does not pass it). `I3` spelled `ThreeModel` (`I3` is `abbrev I3 := ThreeModel`,
  FiniteHornGeometry:21, so the elaborated types agree up to reducible unfolding).
- Route (not the design's hand-made sign fixing): the library already has
  `Topology.Manifold.exists_subsequence_smoothOrientation_on_monotone_open_cover`
  (OrientationExhaustion.lean). Inputs: `V` monotone (radii), covering (`riemannianEDistOf_ne_top` on
  the connected `P.M`), preconnected (`isPathConnected_riemannianBallOf`), basepoint in every `V k`,
  and on `V k` the pullback `PartialDiffeomorph.pullbackSmoothOrientation (F.partialDiffeomorph (N k))`
  of any smooth orientation of `(X.obj (f (N k))).M` (from `o`). Conversions
  `TangentOrientationSection ↔ SmoothOrientation` via `ManifoldOrientation` with a `finrank = 3` cast
  (two private lemmas).
- Compile: clean (standard linter set). Axioms: propext, Classical.choice, Quot.sound.

## X5d (2026-09-26)
- File `Surgery/Topology/AncientPointedFlowLimitBaseScalar.lean` (93 lines), namespace `…Surgery.Topology`.
- `metricScalarAt_basepoint_eq_of_local_flow_limit`: §2.8 elides the binders ("B6b′'s F, V, hV, φ, hφF, G,
  hG0, ψ, hconv"); reconstructed verbatim from TimeControl:781's conclusion (`W`, `h`, `V`, `N`, `φ`, `hφ`
  implicit; `hconv` exactly TimeControl's shape against `(G t).restrictOpen (V k)`), then `hW0`, `c`,
  `hbase` as in §2.8. Two binders added that the design's elision does not show but TimeControl supplies:
  `(hf : StrictMono f)` and `(hψ : StrictMono ψ)` (needed to evaluate the eventual `hW0` at `f (ψ i)`).
  `hV` is used only for `basepoint ∈ V 0`.
- Route: `tendsto_metricScalarAt_of_metricDerivNormSupOn` (StandardWindowShiftConvergence:24) on `V 0`
  at the constant point `basepoint` (p = 2, t = 0); the pulled metric's scalar is `c` eventually by
  `metricScalarAt_localPull`, `hW0`, `hφF`, `F.basepoint_map`, `hbase`; limit side by
  `metricScalarAt_restrictOpen` and `hG0`. Local `SigmaCompactSpace` instance on opens copied from the Data
  file's private one (4 lines; deferred merge candidate).
- Compile: clean (standard linter set). Axioms: propext, Classical.choice, Quot.sound.

## Consumer probe (X5c + X5d against TimeControl:781)
- Scratch probe: obtained the full conclusion of
  `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before` and applied
  `nonempty_tangentOrientationSection_of_pointedConvergence F o hV hVF` and
  `metricScalarAt_basepoint_eq_of_local_flow_limit hf F hV hφF hG0 hψ hconv _ _ (c := 1)` directly to its
  components; elaborated (only the two `sorry`s for `hW0`/`hbase`, which are X5's supply). Probe deleted.

## Deliverables (all new files, uncommitted, not wired into DifferentialGeometry.lean)
- Surgery/Topology/InitialWindowScalarBound.lean (X0 + F2/F3 corollaries)
- Topology/Sequences/NestedSubsequence.lean and Surgery/Topology/TracedRegionMaximalDepth.lean (X2)
- Compactness/Limits/PointedLimitOrientation.lean (X5c)
- Surgery/Topology/AncientPointedFlowLimitBaseScalar.lean (X5d)
- Import order for the acceptance build: NestedSubsequence before TracedRegionMaximalDepth; the rest import
  only committed modules.
