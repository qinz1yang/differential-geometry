# Remaining proof work and preserved partial developments

Snapshot: `3b12c1abf575960b58f7adca8f73c54c7ea5049b`. No Lean source was changed after this commit.
The handoff intentionally stops before beginning further canonical-neighborhood or ancient-extension proofs.

## Actual blockers for arbitrary high-curvature blowup

Target:
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup`,
[HighCurvatureBlowup.lean:20](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureBlowup.lean#L20).
Its current transitive axioms are `propext`, **`sorryAx`**, `Classical.choice`, and `Quot.sound`.

Traversing the elaborated declaration dependencies, including both types and values, finds exactly
these declarations directly using `sorryAx` in the target's closure. All are in the namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn`.

| Declaration | Source | Missing mathematics |
|---|---|---|
| `bounded_curvature_at_distance` | [FiniteHornStructure.lean:1441](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean#L1441) | Uniform bounds for normalized source sequences on bounded terminal-distance balls, including every fixed curvature derivative order. |
| `terminal_limit_global_bound` | [AncientExtension.lean:208](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L208) | Produce the actual terminal limit with its global bound and all `TerminalLimit` fields from local terminal bounds. |
| `ancient_extension` | [AncientExtension.lean:424](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L424) | Extend a supplied backward slab to a compatible complete ancient flow, with the required convergence and global curvature bounds. |

The proof chain runs through `exists_high_curvature_model_approximations`, `closed_flow_models`, and
`no_selected_countersequence`. The latter consumes the three results above and `first_backward_slab`.
The slab theorem is now free of `sorryAx`. `WindowedModelWitness.exists_blowup_limit` supplies the final
subsequence assembly once the preceding inputs exist.

Nearby source gaps such as `buffered_canonical_pullback`, `good_point_buffered_canonical`,
`recentered_source_bound`, and `far_point_separating_neck` are genuine remaining debt, but they are
**not currently reachable** in this target's elaborated proof dependency graph. A different future
proof route may use them. Do not confuse imports or source proximity with transitive proof dependence.

## Recommended next theorem

Prove `bounded_curvature_at_distance` in its existing form:

```lean
theorem bounded_curvature_at_distance {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X
```

Read the actual definitions in
[BlowupConvergence.lean:35](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/BlowupConvergence.lean#L35).
`NormalizedSequence` consists of complete actual flows on `[-2 depthᵢ, 0]`, with escaping depths and
scales, base scalar curvature one, almost-nonnegative pinching, noncollapsing below the expanding
scale, and κ-model witnesses at points with scalar curvature at least two in `[-depthᵢ, 0]`.
Each source has a global curvature bound, but that bound can depend on `i`.

`BoundedAtDistance` requires, for each radius ρ > 0, one scalar upper bound uniform in **all source
indices** on the terminal ρ-ball. `TerminalDerivativeBounds` requires, for each radius and each
fixed order, a bound on that terminal ball uniform in all source indices. Constants may depend on
radius and derivative order; no single constant for all orders is promised.

The missing step is a genuine source estimate: turn higher-curvature model control, pinching, and
noncollapse into uniform bounds on buffered parabolic neighborhoods, with the needed containment
of terminal balls in controlled earlier-time balls. Then use local Shi estimates for each fixed
order. The regular intervals are open at zero; respect the terminal endpoint. A common positive-time
extension is not an available hypothesis.

The κ-solution curvature bounds are now proved and reusable for the models. The normalized sources
are not themselves ancient κ-solutions: they have finite domains and only almost-nonnegative pinching.
Any use of an ancient-model bound on a source requires the actual comparison and scale estimates.

## Reusable lemmas and unfinished interfaces to preserve

All paths in this section are under `DifferentialGeometry/Geometry/Flow/RicciFlow/`.
These conditional interfaces are useful proved reductions; they do not produce their own hypotheses.

| Source | Reusable interface and role |
|---|---|
| `Perelman/CanonicalNeighborhood/FiniteHornStructure.lean:1278` | `bounded_curvature_at_distance_of_terminalParabolicCurvatureControl` converts actual buffered control into both target estimates. |
| Same, `:1293`, `:1310` | `bounded_curvature_at_distance_of_terminalParabolicCurvatureBound` and `_of_terminalParabolicCurvatureBoundProducer` reduce the task to the missing uniform producer. |
| Same, `:1333`, `:1370` | `terminalParabolicCurvatureBound_iff_scale_windows` and `_of_scale_windows` separate curvature bounds from the ball-nesting estimate. |
| Same, `:1414` | `boundedAtDistance_of_recentered_scalar_bound` derives terminal scalar bounds from an eventual recentered estimate and handles finitely many exceptional source indices. |
| `Perelman/CanonicalNeighborhood/TerminalParabolicRmBallWindow.lean:35` | `terminalDerivativeBounds_of_terminalParabolicRmBallWindow` turns the correct buffered window into derivative bounds. |
| Same, `:81` | `terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds` separates order zero from positive orders. Further same-time/window reductions occur at `:126`, `:137`, `:166`; inspect their Ricci hypotheses before applying them. |
| `Perelman/CanonicalNeighborhood/AncientExtension.lean:84,100,216` | `good_point_derivatives`, `local_propagation`, `first_backward_slab` are proved with standard axioms only. |
| `Perelman/KappaSolutions/UniversalCurvatureBounds.lean:19` | `exists_universal_normalized_ancient_curvature_bounds`; also search for `ancientKappa_modelCurvatureBoundNearBase`. These concern genuine ancient models. |
| `Perelman/CanonicalNeighborhood/TerminalLimitConstruction.lean:24,70` | `terminal_limit_of_metric_compact_limit`, `terminal_limit_global_bound_of_frontier` assemble the terminal limit when actual compactness, global scalar bound, orientation, capture, domains, and noncollapse data are supplied. |
| `Perelman/CanonicalNeighborhood/AncientExtensionLimitInputs.lean:99` | `HalfLineAncientLimitFrontier` states the missing compatible half-line limit data. `ancientExtension_nonempty_of_halfLineAncientLimitFrontier` assembles the extension; a producer remains unproved. |
| `Perelman/CanonicalNeighborhood/AncientExtension.lean:313–409` | Half-line existence, flow, slice geometry, bounds, and `HalfLineAnalyticInputs` reductions remain available. They must not replace the mathematical construction. |

Preserve the proved forward uniqueness and symmetry infrastructure:

- `Uniqueness/Forward/NonnegativeRicci.lean:360`:
  `forward_unique_on_slab_of_ricci_nonnegative` derives the energy, metric, connection, density, and
  cutoff estimates for actual complete bounded flows with nonnegative initial Ricci curvature.
- `Uniqueness/Forward/Isometry.lean:57`:
  `ricci_flow_pullback_eq_on_slab_of_initial_isometry`.
- `Preservation/HarmonicGradient.lean`, `Preservation/Cylinder.lean`, and
  `DimensionThree/CylinderPreservation.lean`: harmonic height, constant gradient length,
  parallelness, and the resulting rank bound.
- `DimensionThree/AncientRankOne.lean:121`: global ancient rank-one persistence without κ or
  simple-connectedness assumptions.
- The lower-level Laplacian antisymmetry, cotangent norm, supported volume-integral estimates,
  smooth cutoffs, and exponential energy estimates remain in their topic homes.

There are no uncommitted unfinished edits. The useful unfinished work is the committed set of
conditional reductions above and the retained source gaps in the inventory below. The original
maximal-point attachment is a historical reference, with provenance in REFERENCES.md.

## Routes and pitfalls to avoid

1. Backward rank monotonicity does not prove forward rank preservation on an arbitrary interval.
   MSM144 labels `lbl445`–`lbl447` include initial short-interval constancy, not the missing global
   statement. This gap is now closed through uniqueness, reflections, and Bochner rigidity.
2. Do not require the surface factor to be compact or invoke κ-noncollapse in the original ancient
   splitting theorem. Cigar × line illustrates why a compact-factor argument would be inappropriate.
3. Do not reopen noncompact surface short-time existence merely to recover splitting. The completed
   symmetry argument already supplies the needed rank persistence.
4. Do not assume a normalized source is an ancient κ-solution or was selected at a past scalar
   maximum. The attachment's global scalar ≤ 1 shortcut concerns the special maximal-point problem,
   not arbitrary normalized sequences.
5. A single backward slab is not an ancient flow. One needs compatible subsequences, maps, and
   metrics on all slabs, on one manifold, with completeness at every past time.
6. Local spatial convergence alone does not prove all-time completeness. The attachment flags the
   Part I Corollary 3.18 correction discussed in MSM206. Recheck the actual compactness hypotheses.
7. Exhaustion of the limit manifold is not source-ball capture. Use the actual metric inverse-capture
   theorem and its reference-metric equality and completeness hypotheses.
8. `finite_horn_produces_cone` at `FiniteHornStructure.lean:1237` currently concludes
   `¬ Nonempty (ConeFlowLimit ...)`. It excludes a cone; it does not produce one.
   `finite_horn_smooth_cone_patch` at `:1217` is likewise an exclusion. Neither gives the missing
   contradiction without an actual cone producer. `finite_horn_construction_of_boundedAtDistance`
   uses an already bounded situation with incompatible finite-controlled-radius data; it cannot
   establish the missing boundedness theorem.
9. An `_of_frontier` theorem or a structure containing the required estimates only proves assembly.
   Do not count it as a construction of those estimates.
10. Some convenient ball-window reductions assume nonnegative source Ricci curvature. Almost-pinching
    does not supply that hypothesis. Use a justified lower bound or derive the required comparison.

## Fresh sorry inventory

**21 occurrences in 11 files**, all outside the κ-solution directory. The declaration line locates
the public statement; the `sorry` line locates the remaining proof hole. Paths are relative to
`DifferentialGeometry/`.

| Source | Declaration | Declaration line | `sorry` line |
|---|---|---:|---:|
| [`Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean#L914) | `rfs_csf_embedded_area` | 914 | 925 |
| [`Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean#L1230) | `rfs_csf_generic_curves` | 1230 | 1257 |
| [`Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution.lean#L1259) | `rfs_csf_immersed_area` | 1259 | 1275 |
| [`Geometry/Flow/RicciFlow/Extinction/CurveShortening/Continuation.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/CurveShortening/Continuation.lean#L106) | `rfs_csf_family_dependence` | 106 | 117 |
| [`Geometry/Flow/RicciFlow/Extinction/Families/Deformation.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Families/Deformation.lean#L26) | `rfs_uniform_ramp_alternative` | 26 | 43 |
| [`Geometry/Flow/RicciFlow/Extinction/Families/Deformation.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Families/Deformation.lean#L45) | `rfs_family_deformation` | 45 | 69 |
| [`Geometry/Flow/RicciFlow/Extinction/Families/Flow.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Families/Flow.lean#L26) | `rfs_prepared_family_flow` | 26 | 46 |
| [`Geometry/Flow/RicciFlow/Extinction/Families/Flow.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Families/Flow.lean#L48) | `rfs_ramp_uniform_bounds` | 48 | 74 |
| [`Geometry/Flow/RicciFlow/Extinction/Width/DiskVariation.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Width/DiskVariation.lean#L493) | `rfs_plateau_upper_comparison` | 493 | 530 |
| [`Geometry/Flow/RicciFlow/Extinction/Width/Plateau.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Width/Plateau.lean#L1221) | `conformal_disk_producer` | 1221 | 1232 |
| [`Geometry/Flow/RicciFlow/Extinction/Width/PlateauClassical.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Extinction/Width/PlateauClassical.lean#L250) | `classical_plateau_morrey_of_finite_lipschitz` | 250 | 275 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L178) | `good_point_buffered_canonical` | 178 | 206 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L208) | `terminal_limit_global_bound` | 208 | 213 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L226) | `recentered_source_bound` | 226 | 235 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L250) | `far_point_separating_neck` | 250 | 272 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/AncientExtension.lean#L424) | `ancient_extension` | 424 | 431 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean#L1018) | `finite_horn_barriers` | 1018 | 1024 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean#L1207) | `finite_horn_construction` | 1207 | 1215 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/FiniteHornStructure.lean#L1441) | `bounded_curvature_at_distance` | 1441 | 1446 |
| [`Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean`](../../../DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean#L498) | `buffered_canonical_pullback` | 498 | 508 |
| [`Geometry/MinimalSurface/Plateau/Existence.lean`](../../../DifferentialGeometry/Geometry/MinimalSurface/Plateau/Existence.lean#L32) | `exists_morrey_disk` | 32 | 38 |

Reproduce the inventory with:

```sh
rg -n '^\s*sorry\s*$' DifferentialGeometry | sort
rg -n -g '*.lean' '\bsorry\b' DifferentialGeometry
```

At this snapshot every actual proof hole is a standalone `sorry`. The broader search additionally
matches three comments in the vendored Schoenflies source; those are not proof holes. The root build's
21 declaration warnings agree with this inventory. The packaged dependency probe distinguishes
which of these holes are reachable from the blowup theorem.
