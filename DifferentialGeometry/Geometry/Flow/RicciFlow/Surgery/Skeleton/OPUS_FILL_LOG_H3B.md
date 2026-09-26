# Lane H3b log: openness of the history L-exponential domain and smoothness in Z (DESIGN_22 §2)

- 2026-09-26 start. Target `Surgery/Topology/HistoryLGeometry/ExponentialSmooth.lean`.
  Read: AGENTS.md, NAMING.md §2–6, DESIGN_22 §0/§2/§7 (row H3b), logs H3A/H4/G3/G1C, H3a
  `Exponential.lean`, H1 `Window.lean` (`LWindow`, `restrict`, `ofStage`, `exists_seam`), H2a
  `Regularity.lean` (`LWindow.exists_stage`), H2b `Seam.lean` (`exists_incomingSlab_stageMetric`,
  `LWindow.isLRegularizedGeodesicOn_comp`), G3 `WindowSolutionMap.lean`, G2
  `Jacobian/Naturality.lean` (`IsLRegularizedGeodesicOn.of_comp_localPullMetric`), single-flow
  `ExponentialMap.lean` / `Family.lean` (all family lemmas fix the base point `x`), G7
  `AreaInequality.lean`.
- Compile route: reuse the H3a/H4 scratch build (`scratchpad\h3a`, modules `H3aPre.*`); checked
  `H3aPre.{Exponential,Seam,Window,Regularity}` bodies identical to the repo files. G3's
  `WindowSolutionMap` has a current repo olean (04:31 > source 03:20).
- Finding (endpoint): `IsHistoryLGeodesicOn` pins the endpoint only by `ContinuousWithinAt (α first)
  (Iio v) v`; no clause gives the velocity at `v⁻`. Openness at `Z₀` needs the reference curve to
  continue past `v` (G1c's convergence issue; a Gronwall bound for general geodesics is not in the
  tree). So openness is proved for the domain of initial vectors whose history geodesic continues
  past `v` inside a window (`historyLExpExtDomain`), which is what H8 needs (minimizers continue:
  H2a's `lMinCurve_c1` + `exists_lRegularizedExtOn`).
- Plan: (G) generic single-flow family extension along a reference geodesic (parameter space any
  normed space, base point varying — the tree only has fixed-`x` families); (T) transfer of a family
  between two windows through the stage flow of the stage active at a non-event parameter;
  (P) prefix induction `P(c)` over non-event parameters `c`, base case from the base window, step
  through a window at `c`, sup argument over `[0, v]` using the witness windows and the end window.
- Progress 1 (05:40): scratch `h3b/` (parts assembled by `asm.py`, compiled with `h3b/chk.sh` =
  `LEAN_NUM_THREADS=2 lean` with `LEAN_PATH=<h3a olean>;$(lake env printenv LEAN_PATH)`; file
  imports `H3aPre.Exponential` in scratch, the real `HistoryLGeometry.Exponential` in the repo copy).
  Compiled clean so far: (G) `exists_lRegularizedGeodesicFamily_along` (generic: any parameter
  normed space `P`, family `β₀` on `V₀ ×ˢ K₀` of geodesics agreeing with a reference geodesic `γ` on
  `K₀`, extended to `V ×ˢ K ∋ b` for `uIcc c b ⊆ J`; Good-set argument with G3's
  `exists_lPhaseFlow_of_regular` (variable start) and `eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn`);
  (T) private `exists_transfer_family` (window to window through the stage flow of the stage `k`
  that is open near `c`: `invFun (W₂.f k) ∘ W₁.f k`, geodesic by G2's `of_comp_localPullMetric`
  against `exists_incomingSlab_stageMetric`'s flow, H2b's `LWindow.isLRegularizedGeodesicOn_comp`).
- Finding: `T − v²` interior to stage `first` is implied by an end window with `v ∈ Ioo W.a W.b`
  (its `lower`/`upper`), so the openness theorem needs no separate event-time hypothesis.
- Progress 2 (06:05): transfer, prefix invariant, step, base case, sup argument, openness,
  smoothness and the minimizer inclusion all compile clean in scratch.
- Final (2026-09-26 ~06:10): `Surgery/Topology/HistoryLGeometry/ExponentialSmooth.lean`, 1116 lines,
  LF. No sorry/admit/axiom, no nolint/heartbeat/synth options, no comments or docstrings, only
  `set_option autoImplicit false`, lines ≤ 100 chars (imports excepted). No other repo edits, no git
  writes, root aggregate not touched (register after `MinDomain`/`Truncation`).
  Imports: H4 `HistoryLGeometry.MinDomain` (for `historyMinDomain`; brings H3a `Exponential`, H2b
  `Seam`, H2a `Regularity`, H1 `Window`) and G3 `Perelman/LGeometry/Geodesic/WindowSolutionMap`.
- Compile: scratch `h3b/Full.lean` = repo file with only the first import renamed to
  `H3aPre.MinDomain` (checked `diff --strip-trailing-cr`, body identical), via `h3b/chk.sh`
  (`LEAN_NUM_THREADS=2 lean`, `LEAN_PATH=<h3a olean>;$(lake env printenv LEAN_PATH)`): no errors,
  warnings or infos (42 s). Rebuilt `H3aPre.MinDomain` in `h3a/olean` from the identical source (it
  already existed from H5). `linter.mathlibStandardSet` + `#lint`: only `docBlame` on
  `historyLExpOpenDomain` (excluded by AGENTS.md). Axioms of all 9 public declarations: propext,
  Classical.choice, Quot.sound. Public names grep-unique library-wide.
- Public API.
  - (G, namespace `Perelman`, generic single flow) `exists_lRegularizedGeodesicFamily_along S hS T
    (hJ : IsOpen J) (hγ : IsLRegularizedGeodesicOn S T γ J) (hV₀ : IsOpen V₀) (hp₀ : p₀ ∈ V₀)
    (hK₀ : IsOpen K₀) (hK₀c : IsPreconnected K₀) (hK₀J : K₀ ⊆ J) (hβ₀ : ContMDiffOn (𝓘(ℝ,P).prod
    𝓘(ℝ,ℝ)) I ∞ β₀ (V₀ ×ˢ K₀)) (hgeo₀ : ∀ p ∈ V₀, IsLRegularizedGeodesicOn S T (β₀ (p, ·)) K₀)
    (href₀ : ∀ s ∈ K₀, β₀ (p₀, s) = γ s) (hc : c ∈ K₀) (hcb : uIcc c b ⊆ J) : ∃ V, IsOpen V ∧
    p₀ ∈ V ∧ V ⊆ V₀ ∧ ∃ K, IsOpen K ∧ IsPreconnected K ∧ K₀ ⊆ K ∧ b ∈ K ∧ K ⊆ J ∧ ∃ β, (C^∞ on
    V ×ˢ K) ∧ (geodesics on K) ∧ (β (p₀, ·) = γ on K) ∧ (β = β₀ on V ×ˢ K₀)`. Any normed parameter
    space `P`, base point varying (every family lemma in the tree fixes the base point `x`).
  - (namespace `Perelman`) `exists_isLRegularizedGeodesicOn_extension_of_lRegularizedAction_le
    [NeZero (finrank ℝ E)] [SigmaCompactSpace M] S hS (hab : a < b) (hreg : ∀ s ∈ Icc a b,
    T - s ^ 2 ∈ D.regular) γ hγc hγ hint hmin : ∃ α, EqOn α γ (Icc a b) ∧ ∃ e > 0,
    IsLRegularizedGeodesicOn S T α (Ioo (a - e) (b + e))` (chart partition, `lMinCurve_c1`,
    `lMinCurve_regularity`, `exists_lRegularizedExtOn`).
  - `historyLExpOpenDomain hle T v p : Set (TangentSpace ThreeModel p)` := `{Z | ∃ α,
    IsHistoryLGeodesicOn hle T v α ∧ HasHistoryLInitialVector T α p Z ∧ ∃ W : LWindow first first
    T, v ∈ Ioo W.a W.b ∧ ∃ γ, IsLRegularizedGeodesicOn W.S T γ (Ioo W.a W.b) ∧
    EqOn (W.f ⟨first, _, _⟩ ∘ γ) (α ⟨first, _, hle⟩) (Ioc W.a v)}`: the geodesic continues past `v`
    in stage `first` (this forces `T − v² ∈ Ioo (time first) (stageEndTime first)`).
  - `historyLExpOpenDomain_subset_historyLExpDomain`.
  - (1)+(2) `exists_nhds_contMDiffOn_historyLExp (hv : 0 < v) (hZ₀ : Z₀ ∈ historyLExpOpenDomain
    hle T v p) : ∃ V : Set ThreeSpace, IsOpen V ∧ Z₀ ∈ V ∧ V ⊆ historyLExpOpenDomain hle T v p ∧
    ∃ g : ThreeSpace → (stage first).Carrier, ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ g V ∧
    ∀ Z ∈ V, ∀ hZ : Z ∈ historyLExpDomain hle T v p, historyLExp hle T v p ⟨Z, hZ⟩ = g Z`.
    No condition on `T` beyond the witness (a base at a seam is allowed).
  - `isOpen_historyLExpOpenDomain (hv)`; `exists_contMDiffOn_historyLExp (hv) (q) : ∃ f :
    ThreeSpace → (stage first).Carrier, ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ f
    (historyLExpOpenDomain …) ∧ ∀ Z (hZ : Z ∈ historyLExpDomain …), f Z = historyLExp … ⟨Z, hZ⟩`
    (`f` is `historyLExp` extended by `q`; `q` only because a stage carrier may be empty).
  - (3) `historyMinDomain_subset_historyLExpOpenDomain (hv) (hend : T - v ^ 2 ∈ Ioo (time first)
    (stageEndTime first)) (hfloor : ∀ j, ∀ t ∈ stageDomain j, ∀ x, -B ≤ metricScalarAt
    (stageMetric j t) x) : historyMinDomain hle T B v p ⊆ historyLExpOpenDomain hle T v p`
    (stage window `[v-δ, v+δ]` from `LWindow.exists_stage`, restricted to `[v-δ, v]`; H2a's
    `exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq`, window minimality, then the
    extension lemma; end window = the same window restricted to `[v-δ, v+ρ]`), and the G7 package
    `exists_isOpen_superset_historyMinDomain_contMDiffOn_historyLExp (hv) (hend) (hfloor) (q) :
    ∃ U : Set ThreeSpace, IsOpen U ∧ historyMinDomain hle T B v p ⊆ U ∧ ∃ f : ThreeSpace →
    (stage first).Carrier, ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel 1 f U ∧ ∀ Z (hZ : Z ∈
    historyLExpDomain hle T v p), f Z = historyLExp hle T v p ⟨Z, hZ⟩`.
    G7 (`Analysis/Integration/Measure/Parametric/AreaInequality.lean:116`):
    `lintegral_image_le_lintegral_paramDensity_mul (g : SmoothRiemannianMetric I M) {f : E → M}
    {U K : Set E} (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U) (hf : ContMDiffOn 𝓘(ℝ, E) I 1
    f U) (φ : M → ℝ≥0∞) : ∫⁻ y in f '' K, φ y ∂vol_g ≤ ∫⁻ x in K, ofReal (paramDensity g f x) *
    φ (f x) ∂modelHaar`. Take `E := ThreeSpace`, `K := historyMinDomain hle T B v p` (a subset of
    `TangentSpace ThreeModel p = ThreeSpace`; H4's `val ⁻¹' Ω̄` in the subtype is the same set) and
    `f` from the package; `f '' K = historyLExp '' (val ⁻¹' K)` by the agreement clause.
    `MeasurableSet K` is still queue entry 26.
- Proof architecture (private): `contDiffAt_familySeed`, `continuousAt_lPhaseState`,
  `exists_family_step` (closure step: G3's variable-start flow at `(r, state γ r)`, seed at a nearby
  good `r'`, glue by `if s ∈ K`), Good-set over `uIcc c b`; `exists_transfer_family` (window to
  window through the stage `k` open near `c`: `invFun (W₂.f k) ∘ W₁.f k`, C^∞ by an ∞ version of
  H1's `contMDiffOn_invFun`, geodesic by G2's `of_comp_localPullMetric` against the stage flow of
  `exists_incomingSlab_stageMetric`); prefix invariant `HasPrefixFamily … Z₀ c` (open `V ∋ Z₀`,
  curves `A Z` with `IsHistoryLGeodesicPrefix (A Z) Z c` = crossings for seams `< c`, windows for
  `s ∈ (0, c)` with `W.b ≤ c`, base window with `W.b ≤ c`; a reference window at `c` and a C^∞
  family near `c` with `A Z k = W.f k ∘ β` on `(c-η, c]`); `exists_hasPrefixFamily_base` (base
  window of the witness, `lRegularizedFamily_extend`, parameter `Z ↦ (mfderiv f x)⁻¹ Z`);
  `hasPrefixFamily_step` (transfer + (G) + redefine `A` beyond `c`; seams in `(c, c')` from the
  new window's `crossing`; windows at `s ∈ [c, c')` = `W'.restrict` to `[c - η₁/2, c']`);
  `hasPrefixFamily_end` (sup over `{c ≤ v | HasPrefixFamily c}`: witness window at the sup if it is
  `< v`, end window at `v`). Partition points are non-event (`exists_mem_Ioo_not_mem_range`).
- (2') Curve-level smoothness is not stated separately. For a non-event `s ∈ (0, v)`, H5's
  `isHistoryLGeodesicOn_truncate` / `HasHistoryLInitialVector.truncate` (first := stage of `T − s²`)
  put the truncated curve in `historyLExpOpenDomain … s` (end window: the `v`-curve's witness window
  at `s`, `LWindow.restrict`ed to one stage around `s`), and `exists_nhds_contMDiffOn_historyLExp`
  at `v := s` gives `Z ↦ α_Z k s` C^∞ near `Z₀`. Joint smoothness in `(Z, s)` on each open stage
  piece is the chain's family `β` (C^∞ on `V ×ˢ Ioo (c-η) (c+η)`); a packaged statement needs the
  invariant to keep all families or the H5 composition above. H7a should state what it needs.
- (4) `T − v²` an event time (`= time first`, post-surgery convention): NOT delivered. What changes:
  no `LWindow` with stages in `[first, last]` contains `v` in its interior (the only flow regular at
  `time first` is the seam flow, whose old stage `first − 1` is outside the history), so
  `historyLExpOpenDomain` is empty there. Exact remaining statement:
  `exists_nhds_contMDiffOn_historyLExp_of_closedStart (hv) (hevent : T - v ^ 2 = time first)
  (α₀ witness of Z₀ ∈ historyLExpDomain) {ξ : TangentBundle ThreeModel (stage first).Carrier}
  (hlim : Tendsto (fun s => (α₀ first s, lVelocity (α₀ first) s)) (𝓝[<] v) (𝓝 ξ)) :
  ∃ V ∈ 𝓝 Z₀, V ⊆ historyLExpDomain hle T v p ∧ ∃ g C^∞ on V, historyLExp = g on V`.
  Route: the present chain up to a non-event `c < v` in stage `first`'s open piece; transfer into
  the stage carrier (`exists_incomingSlab_stageMetric first`, regular on the open piece); (G) up to
  `c'` near `v`; last step with G1b's `exists_lPhaseFlow_of_start` at `(v, state ξ)` (`hmetric`
  from `G.smoothUpTo`) and a one-sided copy of `exists_family_step` (geodesic only for `s < v`, the
  glued family C^∞ on `V ×ˢ Ioo (v-ε) (v+ε)` from `Ψ`); `α_Z first v := β (Z, v)` (the history
  clause only asks continuity from the left). This is G1c's `exists_lRegularizedFamily_of_start`
  with a varying base point. Missing: (i) the one-sided step (~120 lines); (ii) for H8 the limit
  `hlim` for minimizers at a closed start: `lMinCurve_c1` needs `D.regular` at the endpoint, so a
  closed-end C¹ regularity for minimizers (G1-type brick) is needed; without it H8 at an event-time
  `v₂` has no open `U ⊇ K`.
- Duplicates to merge later (private copies): `mem_regularizedStage_Icc/Ioo`,
  `mem_range_of_mem_Icc` (H3a `Exponential`), `contMDiffOn_invFun_smooth` (∞ version of H1's
  order-1 `LWindow.contMDiffOn_invFun`), `contDiffAt_familySeed` (generalizes `ExponentialMap`'s
  private `lPhaseSeed_smooth`), `continuousAt_lPhaseState` (cf. H2b's private
  `continuousAt_chartPhase`). The two generic `Perelman` theorems belong in
  `Perelman/LGeometry/Geodesic/` (Family / Minimizer) on integration.
