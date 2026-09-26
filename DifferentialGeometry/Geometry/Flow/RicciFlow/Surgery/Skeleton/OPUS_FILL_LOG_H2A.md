# Lane H2a log: regularity of history minimizers (DESIGN_22 §2, brick H2a)

- 2026-09-26: new file `Surgery/Topology/HistoryLGeometry/Regularity.lean`, 394 lines. No sorry,
  nolint, or heartbeat/synth options; no comments or docstrings; lines ≤ 100. No other edits, no
  git writes, root aggregate not touched (the lead must register this module after `Window`).
- Compile: `Window.lean` (H1) has no olean, so both files were concatenated in dependency order
  into a scratch file outside the repo (imports hoisted; `Window` import dropped; `end` closes
  Window's section). Ran `LEAN_NUM_THREADS=2 lake env lean <scratch>`, clean: no errors, warnings
  or info. `#lint` on the scratch copy reports only `docBlame` on H1's `LWindow` fields, `restrict`
  and `ofStage`. That linter is excluded by AGENTS.md.
- Axioms, checked on a scratch copy for all 10 public declarations: propext, Classical.choice,
  Quot.sound. No sorryAx.
- Single-flow regularity used:
  - `lMinCurve_regularity` (`Perelman/LGeometry/Action/Minimizer/EulerLagrangeRegularity.lean:30`).
    It takes a C¹-competitor minimizer with a chart-H¹ partition and gives the triple that defines
    `IsLRegularizedGeodesicOn` on `Ioo a b`. It needs only `∀ s ∈ Icc a b, T - s^2 ∈ D.regular`,
    which is `LWindow.regular`. The `_of_spatial_derivatives` variant is not needed.
  - The AC → H¹ bridge is `exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval`
    (`…/ChartPartition/Construction/Sobolev.lean:81`).
  - The initial vector uses `lMinCurve_c1` (`Minimizer/C1Regularity.lean:28`),
    `exists_lRegularizedExtOn` (`Minimizer/Extension.lean:214`) and `lRegularizedCurve_eqIcc` /
    `lRegularizedCurve_velocity_zero` (`Geodesic/ExponentialMap.lean:1673,1811`).
- Pitfall: putting `metrizableSpaceMetric` directly on `W.X` inside a window proof made elaboration
  time out or run out of memory, because the instance clashed with the projection `W.top`. The fix
  is to prove generic single-flow lemmas over an arbitrary `[SigmaCompactSpace M] [T2Space M]`
  manifold, with the metric built locally, and apply them to `W.S`.
- Delivered, generic single-flow (namespace `…Perelman`; they belong in
  `Perelman/LGeometry/Action/Minimizer/`, so promote them later):
  - `isLRegularizedGeodesicOn_of_lRegularizedAction_le`: AC plus an integrable Lagrangian plus
    minimality against C¹ competitors with the same endpoints give `IsLRegularizedGeodesicOn S T γ
    (Ioo a b)`.
  - `eq_of_eqOn_lRegularizedCurve`: if `T ∈ D.regular` and `0 < b`, and two `lRegularizedCurve`s
    from `x` agree on `Icc 0 b`, their initial vectors are equal.
  - `existsUnique_eqOn_lRegularizedCurve_of_lRegularizedAction_le`: under the same hypotheses on
    `[0, b]`, `∃! Z, b ∈ lRegularizedDomain S T (γ 0) Z ∧ EqOn (lRegularizedCurve S T (γ 0) Z) γ
    (Icc 0 b)`.
- Delivered, windows (namespace `ObservedHistory.LWindow`, for `W : H.LWindow lo hi T` inside
  `[first, last]` with `u ≤ W.a`, `W.b ≤ v`). The common hypotheses are those of
  `lRegularizedAction_le_of_regularizedCost_eq`: `hupper hlower hfloor α hα hnode hmin hfin`.
  - `intervalIntegrable_lRegularizedLagrangian_of_ne_top`
  - `isLRegularizedGeodesicOn_of_regularizedCost_eq`: `γ` continuous and AC with
    `W.f j ∘ γ = α` on the pieces gives `IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b)`. This works
    for any window, including seam windows from `exists_seam`, so H2b gets the glued-flow
    regularity from it directly.
  - `exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq`: given `hrange`, returns
    `∃ γ, Continuous γ ∧ AC ∧ (∀ j, EqOn (W.f j ∘ γ) (α ⟨j, _, _⟩) piece_j) ∧
    IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b)`.
  - `existsUnique_eqOn_lRegularizedCurve_of_regularizedCost_eq`: with `W.a = 0` and `u = 0`,
    returns `∃! Z : TangentSpace ThreeModel (γ 0), W.b ∈ lRegularizedDomain W.S T (γ 0) Z ∧
    EqOn (lRegularizedCurve W.S T (γ 0) Z) γ (Icc 0 W.b)`.
  - `exists_stage j (0 ≤ a) (a < b) (time j < T - b^2) (T - a^2 < stageEndTime j)`: returns
    `∃ W : H.LWindow j j T, W.a = a ∧ W.b = b ∧ ∀ k, range (W.f k) = univ`. It is `ofStage … ⊤`
    over the incoming flow, or over `finalSlab` for `last`.
  - `exists_stage_isLRegularizedGeodesicOn_of_regularizedCost_eq` (a stage-interior piece): for
    `j : StageInterval first last` and `u ≤ a < b ≤ v` strictly inside the stage, returns
    `∃ W : H.LWindow j j T, W.a = a ∧ W.b = b ∧ (∀ k, range (W.f k) = univ) ∧ ∃ γ, Continuous γ ∧
    EqOn (W.f ⟨j, le_rfl, le_rfl⟩ ∘ γ) (α j) (Icc a b) ∧ IsLRegularizedGeodesicOn W.S T γ (Ioo a b)`.
  - `exists_stage_initialVector_of_regularizedCost_eq` (the base): with `u = 0`, `0 < b ≤ v`,
    `time last < T - b^2` and `T < stageEndTime last`, returns the same package on
    `W : H.LWindow last last T` with `W.a = 0`, plus the `∃! Z` of the base. Here
    `γ 0 = α last 0 = p` through `W.f = val`.
- Deviations from the brief:
  - `hfin : regularizedExtendedAction … ≠ ⊤` is an explicit hypothesis. `regularMinimizerEndpoints`
    does not exclude `cost = ⊤`, and the tree has no finiteness lemma. H4 must supply it, or
    discard the `⊤` case, where the density is 0.
  - Crossings enter as `hnode` (only `∃ z, z.1.1 = α_old ∧ oldOutput z = α_new`). This is weaker
    than `RegularCrossing`. Get it from `RegularCrossing` by `fun i hf hl => let ⟨z, _, h1, h2⟩ :=
    hcross i hf hl; ⟨z, h1, h2⟩`.
  - The base theorem needs `T < stageEndTime last` and `time last < T`. When `T = horizon` or `T`
    is an event time, it needs a G1 or seam window with `W.a = 0`. The window-level theorem
    `existsUnique_eqOn_lRegularizedCurve_of_regularizedCost_eq` already accepts any window with
    `W.a = 0`, since `W.regular` supplies `T ∈ D.regular`.
  - The results are stated for the window flow `W.S`, which is the stage flow restricted to `⊤`.
    Transfer to the stage flow itself is the G2 naturality brick.
- §7 rows these must match:
  - "H2a | Regular minimizers: stage-interior L-geodesic and initial vector | `…/Regularity` |
    history | 1200 | H1"
  - "H3a | `IsHistoryLGeodesicOn`, `historyLExpDomain`, `historyLExp`, uniqueness | `…/Exponential` |
    history | 900 | H1, G3"
  - "H4 | `historyMinDomain`, surjectivity, density identity | `…/MinDomain` | history | 800 | H2,
    H3a, H0"
- Shapes H3a and H4 consume:
  - H3a's `IsHistoryLGeodesicOn` clause, per H1's indexing, is `∃ lo hi (first ≤ lo) (hi ≤ last)
    (W : H.LWindow lo hi T), s ∈ Ioo W.a W.b ∧ ∃ γ, IsLRegularizedGeodesicOn W.S T γ (Ioo W.a
    W.b) ∧ ∀ j, EqOn (W.f j ∘ γ) (α ⟨j, _, _⟩) piece_j`.
  - `exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq` gives exactly that for any
    window. Stage-interior `s` go through `exists_stage…`, and seam `s` through `exists_seam` plus
    the lift theorem.
  - H4 surjectivity needs the initial `Z` from `exists_stage_initialVector_of_regularizedCost_eq`
    and H3a uniqueness.
