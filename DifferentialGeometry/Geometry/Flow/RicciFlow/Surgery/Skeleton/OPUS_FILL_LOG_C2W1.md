# Lane C2W1: wave-1 bricks G7′, TailG, SB1, SB2 of DESIGN_C2_ASSEMBLY.md

2026-09-26. Worker in `D:\differential-geometry-pc3`. Read-only compiles with
`LEAN_NUM_THREADS=2 lake env lean` plus the lakefile's leanOptions passed as `-D`
(`maxSynthPendingDepth=3`, `weak.linter.mathlibStandardSet=true`). No lake build, no git writes.

## G7′ `lintegral_paramDensity_mul_le_lintegral_image`

- File: `DifferentialGeometry/Analysis/Integration/Measure/Parametric/InjectiveAreaInequality.lean`
  (new; the lead's "new files only" rule; STRUCTURE.md does not forbid a one-theorem file, and the
  injective lower bound is a separate conclusion from G7's non-injective upper bound).
- Statement verbatim from design §5.1, namespace `DifferentialGeometry.Integral.Measure`, same
  private `borel` instances as G7.
- Proof: `withDensity` form (`lintegral_withDensity_eq_lintegral_mul_non_measurable₀`), push to the
  subtype `K` (`MeasurableEmbedding.subtype_coe`, `map_comap`), `ContinuousOn.measurableEmbedding`
  (Lusin–Souslin) for `K.domRestrict f`, then `MeasurableEmbedding.lintegral_map` and
  `map_withDensity_paramDensity`. No measurability of `φ`.
- Compile: 0 errors, 0 warnings. `#lint`: all passed. Axioms: `propext, Classical.choice,
  Quot.sound`.
- Tree convention: neighbouring files have no copyright header; the new file follows them.

## TailG `exists_uniform_tail_gaussian_metric`

- File: `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/Jacobian/MetricGaussianTail.lean`
  (new sibling of `SourceGaussianTail.lean`; imports only `GaussianTail`, `Chart/Density`,
  `PointwiseInner/DualMetric`, so the old file may import it).
- Primary theorem `exists_uniform_tail_gaussian_metric_of_finrank_eq {n} (hn : finrank ℝ E = n)`:
  any finite-dimensional normed `E` (no inner product needed), `R` chosen before
  `∀ {H : Type uH} {I} {X : Type u} [ChartedSpace H X] [IsManifold I ∞ X] (g) (x)`, exponent `n / 2`.
  Proof: `gaussianPosDef_uniform_tail` on the Gram matrix of `g.inner x` in `chartModelBasis`,
  transported by `toEuclidean` (`map_toEuclidean_modelHaar_eq_volume`); dimension 0 separately.
- Consumer statement `exists_uniform_tail_gaussian_metric` (universe `u` only): the design §5.1 text
  with `ThreeSpace`/`ThreeModel` spelled `EuclideanSpace ℝ (Fin 3)` / `𝓘(ℝ, EuclideanSpace ℝ (Fin 3))`
  (the abbrevs live in `Surgery/Topology/LoopModel.lean`; a Perelman file must not import Surgery).
  Corollary of the primary with `finrank_euclideanSpace_fin`.
- Probe (scratch, imports `Surgery/Topology/Background`): the verbatim design statement with
  `ThreeSpace`/`ThreeModel` is closed by `obtain ⟨R, hR, htail⟩ := exists_uniform_tail_gaussian_metric.{u} eps heps;
  exact ⟨R, hR, fun g x => htail g x⟩` — the §5.5 call shape works.
- Recast of `lSourceGaussian_uniform_tail` (NOT applied: existing file, new-files-only rule). Verified in
  the probe; the lead can replace its body (and add the import of `MetricGaussianTail`) with
  ```lean
    obtain ⟨R, hR, htail⟩ :=
      exists_uniform_tail_gaussian_metric_of_finrank_eq.{u, uH} (E := E) rfl eps heps
    refine ⟨R, hR, fun S T x => ?_⟩
    simp only [lSourceGaussian_eq_metric_norm]
    exact htail (S.base.metric T) x
  ```
  The private `metricGram_quadraticForm` duplicates `lSourceGram_quadraticForm` for a bare metric;
  after the recast the flow lemma could become a corollary of it too.
- Compile: 0 errors, 0 warnings. `#lint`: passed. Axioms (both): `propext, Classical.choice, Quot.sound`.

## SB1 + SB2 (one file)

- File: `Surgery/Topology/HistoryLGeometry/SeamBase.lean` (new; imports `Truncation`). SB1 and SB2 are
  one development — existence and uniqueness of history initial vectors when the base time is a
  seam `T = time last` — so they share a file instead of a MinDomain sibling and a Truncation sibling.
- Seam-base construction (H3a's "80-line note"): at `T = time last` we get `last = i.succ`,
  `first ≤ i.castSucc`, and the stage-`i.succ` piece is `{0}`. The window is `LWindow.exists_seam`
  with `a = 0`; `b` comes from continuity of the `i.castSucc` piece at `0` into the survivor source;
  then `exists_lift_…` and `existsUnique_eqOn_lRegularizedCurve_…` with `W.a = 0`. We cannot call H2b's
  seam headline, because it requires `u < √(T - time i.succ) = 0`.
- Public declarations:
  - `exists_hasHistoryLInitialVector_of_regularizedCost_eq_of_mem_Ico` (the Ico extension of H3a;
    `Ioo` case = H3a's theorem);
  - SB1 `exists_historyLExp_eq_of_mem_regularMinimizerEndpoints_of_mem_Ico` (design §5.2, verbatim);
  - `image_historyMinDomain_of_mem_Ico`, `setLIntegral_regularMinimizerEndpoints_eq_of_mem_Ico`
    (Ico siblings of the MinDomain lemmas; they are needed for the corollary);
  - `RetainedCoreHistory.exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico`
    (design §5.4, verbatim);
  - `HasHistoryLInitialVector.eq_of_eqOn_of_time_succ_eq`: uniqueness of the initial vector at a seam
    base, read off the `i.castSucc` piece and pushed through the crossing map
    (`eventually_regularCrossing_invFun`, `mfderiv_apply_mfderiv_eq_of_regularCrossing`);
  - SB2 `injOn_historyLExp_of_lt_of_mem_Ico` (design §5.2, verbatim).
- Duplication to refactor later (existing files untouched per the new-files rule):
  - the private `eqOn_of_truncate_eq` is the middle of `Truncation.injOn_historyLExp_of_lt`
    (splice `γ` plus `eqOn_of_eqOn_Ioi`), copied;
  - `injOn_historyLExp_of_lt`, `exists_historyLExp_eq_of_mem_regularMinimizerEndpoints`,
    `image_historyMinDomain`, `setLIntegral_…_eq` and the `Ioo` reduced-volume corollary are now
    special cases of the `_of_mem_Ico` versions and could become corollaries;
  - four small private helpers are copied (`mem_stageDomain_of_le_of_lt`, `bounds_…`,
    `lt_stageEndTime_of_lt'`, `setLIntegral_eq_zero_of_forall_mem`).
- Note on SB2's `hT`: only `time last ≤ T` is used, and for `T < time last` `historyMinDomain` is
  empty. So the hypothesis could be dropped; it is kept verbatim for the §5.5 call shape.
- Compile (`SeamBase.lean`, 720 lines): 0 errors, 0 warnings. A scratch copy with `#lint` passed
  (16 declarations). A scratch probe elaborates the design-verbatim SB1/SB2 signatures as `example`s
  closed by the new theorems (same explicit-argument order as the §5.5 calls). Axioms of all five
  public headlines: `propext, Classical.choice, Quot.sound`, no `sorryAx`.
- Compile-time note: during this lane a concurrent lake build was rebuilding the
  `MetricComparison.lean` dependents, so `lake env lean` failed with missing oleans for a while;
  I waited it out, and the final compiles ran against complete oleans.

## Summary

| Brick | File | Lines | Status |
|---|---|---|---|
| G7′ | `Analysis/Integration/Measure/Parametric/InjectiveAreaInequality.lean` | 62 | proved, verbatim |
| TailG | `Perelman/LGeometry/Jacobian/MetricGaussianTail.lean` | 176 | proved; `ThreeSpace` spelled `EuclideanSpace ℝ (Fin 3)`; general primary theorem added |
| SB1 + corollary | `Surgery/Topology/HistoryLGeometry/SeamBase.lean` | 720 (with SB2) | proved, verbatim |
| SB2 | same file | — | proved, verbatim |

To register in the root aggregate: the three new modules. Not registered (root aggregate is not mine to touch).
