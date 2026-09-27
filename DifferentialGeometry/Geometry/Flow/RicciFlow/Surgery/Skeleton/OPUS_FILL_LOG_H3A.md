# Lane H3a log: history L-geodesics and the history L-exponential map (DESIGN_22 §2, brick H3a)

- 2026-09-26 start. Target file `Surgery/Topology/HistoryLGeometry/Exponential.lean`.
  Inputs read: DESIGN_22 §0/§2/§7, H1 `Window.lean`, H2a `Regularity.lean`, G2
  `Perelman/LGeometry/Jacobian/Naturality.lean`, G3 `Geodesic/WindowSolutionMap.lean`, G1c log.
  H2b `Seam.lean` appeared (in progress, 03:34); not used, to stay independent of a moving file.
- Plan: uniqueness needs a window-to-window transfer (the two curves come with different windows):
  on `U = {y | W₂.f k y ∈ range (W₁.f k)}` the map `g = invFun (W₁.f k) ∘ W₂.f k` is a local
  diffeomorphism, `W₁.f j ∘ g = W₂.f j` for every common stage (crossing uniqueness both ways), the
  window metrics are `g`-related at every non-event time (metric clauses), hence at event times by
  continuity in `t` (`MetricFamilySmoothOn.coeff_cont`). Then G2's
  `IsLRegularizedGeodesicOn.comp_of_localPullMetric` moves the geodesic and
  `lRegularizedSolution_eqOn` gives agreement.
- Progress 1: compile route. The four uncommitted prerequisites (G2 `PartialDiffeomorph.lean`,
  G2 `Jacobian/Naturality.lean`, H1 `Window.lean`, H2a `Regularity.lean`) are copied outside the
  repo as modules `H3aPre.*` (imports renamed) and compiled with `lean --root=. -o`; the scratch
  copy of the new file imports `H3aPre.*`. Mirroring the real module names in a second search-path
  entry does not work: Lean resolves the package root in the first `LEAN_PATH` entry that has a
  `DifferentialGeometry` directory. Transfer layer (window-to-window map, metric identity through
  event times by continuity, geodesic transfer, left-to-right and base propagation) compiles.
- Progress 2: definitions `IsHistoryLGeodesicOn`, `HasHistoryLInitialVector`, `historyLExpDomain`,
  `historyLExp` and the uniqueness theorem compile with no sorry (scratch). The uniqueness is a
  sup argument over `A s := α = β on every piece below s`: base step from the two base windows
  (`exists_eq_of_initialVector`), local step from the two windows at `s` (stage `k` =
  `activeStage (T - s²)` has a left neighbourhood of `s` in its piece), end point `v` from the
  continuity clause. Next: regular minimizers are history L-geodesics (stage windows from H2a,
  seam windows from `LWindow.exists_seam` + H2a's lift).
- Final (2026-09-26): `Surgery/Topology/HistoryLGeometry/Exponential.lean`, 864 lines. No sorry,
  nolint, heartbeat or synth options; no comments or docstrings; lines ≤ 100; only
  `set_option autoImplicit false`. No other repo edits, no git writes, root aggregate not touched
  (register after `Seam`).
- Imports: H2b `HistoryLGeometry.Seam` (brings H2a `Regularity`, H1 `Window`, G2
  `Jacobian/Naturality`, `SurvivorChartMetric`, `ClosedSlabEndpoints`, `Geodesic/Congruence`) and
  `Topology/ThreeManifold/ConnectedSum/UnitFillingSmooth` (only for the general
  `DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_eventuallyEq`; it belongs in
  `Topology/Manifold`). G3 `WindowSolutionMap` is not needed: agreement is
  `lRegularizedSolution_eqOn` (`Geodesic/ExponentialMap.lean:184`), which G3 wraps.
- Compile: scratch modules `H3aPre.{PartialDiffeomorph,Naturality,Window,Regularity,Seam}` (repo
  copies, imports renamed, byte-identical bodies checked with `diff --strip-trailing-cr`) built with
  `lean --root=. -o`; the scratch copy of this file (imports renamed back, body identical) compiles
  clean: no errors, warnings or info. `linter.mathlibStandardSet` + `#lint`: only `docBlame` on the
  four defs (excluded by AGENTS.md). Axioms for all 9 public declarations: propext,
  Classical.choice, Quot.sound.
- Definitions (namespace `ObservedHistory`; `RetainedCoreHistory` uses them through `toHistory`):
  - `IsHistoryLGeodesicOn hle T v α` := `T - v^2 ∈ stageDomain first` ∧ `RegularCrossing` hand-off
    at every event of `[first, last]` ∧ `∀ s ∈ Ioo 0 v, ∃ lo hi (first ≤ lo) (hi ≤ last)
    (W : LWindow lo hi T), s ∈ Ioo W.a W.b ∧ W.b ≤ v ∧ ∃ γ, IsLRegularizedGeodesicOn W.S T γ
    (Ioo W.a W.b) ∧ ∀ j, EqOn (W.f j ∘ γ) (α ⟨j, _⟩) piece_j(W)` ∧
    `ContinuousWithinAt (α first) (Iio v) v` (the last clause pins the endpoint value; without it
    `α first v` is not determined by the geodesic clauses).
  - `HasHistoryLInitialVector T α p Z` := a base window `W : LWindow lo last T` (`first ≤ lo`) with
    `W.a = 0`, a point `x`, `Zx` with `W.f last x = p`, `mfderiv (W.f last) x Zx = Z`,
    `W.b ∈ lRegularizedDomain W.S T x Zx`, and `W.f j ∘ lRegularizedCurve W.S T x Zx = α j` on every
    base piece. Multi-stage base windows are allowed so that `T = time last` (base at a seam) is
    representable; single-stage ones are the H2a case.
  - `historyLExpDomain hle T v p : Set (TangentSpace ThreeModel p)` := `{Z | ∃ α, IsHistoryLGeodesicOn
    ∧ HasHistoryLInitialVector}`; `historyLExp hle T v p : historyLExpDomain … → (stage first)`
    (choice; subtype domain, since a stage carrier can be empty and there is no junk value).
- Theorems:
  - `IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector (hv : 0 < v) hα hβ hα₀ hβ₀ j :
    EqOn (α j) (β j) (Icc (regularizedStageStart T 0 j) (regularizedStageEnd T v j))` (full pieces,
    endpoints included). Same `first last v`.
  - `historyLExp_eq (hv) (Z) (hα) (hZ) : historyLExp hle T v p Z = α ⟨first, le_rfl, hle⟩ v`.
  - With section hypotheses `hle hfloor hα(AC) hcross hmin hfin` (exactly the
    `regularMinimizerEndpoints` witness plus H2a's `hfloor`, `hfin`):
    - `isHistoryLGeodesicOn_of_regularizedCost_eq (hv : 0 < v) : IsHistoryLGeodesicOn hle T v α`
      (no condition on `T`: stage windows from `LWindow.exists_stage_…`, seam windows from H2b's
      `LWindow.exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq` with `u = 0`);
    - `exists_hasHistoryLInitialVector_of_regularizedCost_eq (hv) (hT : T ∈ Ioo (time last)
      (stageEndTime last)) : ∃ Z, HasHistoryLInitialVector T α (α last 0) Z`;
    - `exists_historyLExp_eq_of_regularizedCost_eq (hv) (hT) : ∃ Z : historyLExpDomain hle T v
      (α last 0), historyLExp hle T v _ Z = α first v`.
- H4 row (§7): "H4 | `historyMinDomain`, surjectivity, density identity | `…/MinDomain` | history |
  800 | H2, H3a, H0". Surjectivity: unpack `q ∈ regularMinimizerEndpoints` to `α, hα, hp, hq,
  hcross, hmin`, `subst hp hq`, apply `exists_historyLExp_eq_of_regularizedCost_eq` (with `hfloor`
  from H0 and `hfin` from finiteness, or discard `cost = ⊤` where the density is 0).
- Gaps (honest limits):
  - The initial vector needs `time last < T < stageEndTime last`. `T = horizon` needs G1 (no flow
    past the closed end). `T = time last` needs a seam base window with `W.a = 0`: `exists_seam`
    accepts `a = 0` there, but H2b's headline requires `u < w`; about 80 lines, not done. The
    definitions already accept that window.
  - Uniqueness is stated for a common `(first, last, v)`; comparing different `v` goes through
    truncation (H5).
- Proof architecture (private): `transferSet/transferMap` (`g = choose` on
  `U = W₂.f k ⁻¹' range (W₁.f k)`, a local diffeomorphism via `localInverse`), `f_eq_of_f_eq`
  (crossing uniqueness propagates `W₁.f k ∘ g = W₂.f k` to every common stage), `inner_transferMap`
  (metric identity from both metric clauses), `transferIsometricAt_of_lt` (identity at event times
  by continuity from below, `MetricFamilySmoothOn.coeff_cont`, finite `range time`),
  `exists_isLRegularizedGeodesicOn_transfer` (restrict `W₂` to `U`, G2 naturality),
  `exists_eq_of_eq_left` / `exists_eq_of_initialVector` (propagation), `agree_base`/`agree_step`
  and a `sSup` argument.
- Duplicates dropped after H2b landed: my private seam-window construction and slab lemma were
  replaced by H2b's `exists_seam_isLRegularizedGeodesicOn_of_regularizedCost_eq` (the private
  slab copy is gone; `exists_incomingSlab_stageMetric` is H2b's).
