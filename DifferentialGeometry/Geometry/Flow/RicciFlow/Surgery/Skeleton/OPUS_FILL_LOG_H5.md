# Lane H5 log: truncation, nesting and injectivity of the history L-exponential (DESIGN_22 §3, brick H5)

- 2026-09-26 start. Target file `Surgery/Topology/HistoryLGeometry/Truncation.lean`.
  Inputs read: AGENTS.md, DESIGN_22 §0/§2/§3/§5/§7, OPUS_FILL_LOG_H4/H3A, H4 `MinDomain.lean`,
  H3a `Exponential.lean`, H1 `Window.lean` (`exists_splice`, split at parameter, `restrict`,
  `exists_lift`), H2a `Regularity.lean` (`exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq`),
  `HistoryAction/AbsoluteContinuity.lean` (split at event, dynamic programming).
- Compile route: reuse the H3a/H4 scratch build (`scratchpad\h3a`, modules `H3aPre.*`); built
  `H3aPre.MinDomain` from the repo `MinDomain.lean` (only the first import renamed) with
  `lean --root=. -o` (37 s, clean). The scratch copy of the new file imports `H3aPre.MinDomain`.
- Plan. (1) Truncation by the parameter split `mem_regularizedActionValues_split_at_parameter`
  at `c = v₁`, stage `k` with `T - v₁² ∈ stageDomain k` (this covers `T - v₁²` an event time: the
  post convention puts `k` on the new stage, the old stage and that crossing are dropped). A cheaper
  competitor `A'` plus the finite lower piece is a competitor at `v₂` below the cost. Geodesic and
  initial vector: H3a's `isHistoryLGeodesicOn_of_regularizedCost_eq` on the truncation, initial
  window restricted by `LWindow.restrict` to `b ≤ v₁`. (2) `historyLExp_eq` + `eqOn_historyLCurve`.
  (3) Corner argument without a first-variation lemma: the splice (β on `r ≤ v₁`, α on `r ≥ v₁`) is
  again a finite-cost minimizer at `v₂`, so it is window-wise an L-geodesic; backward continuation
  from `r > v₁` down to `0` uses α's window at `s` and lifts the splice into a restriction of the
  same window (H2a's lift lemma), then single-flow `lRegularizedSolution_eqOn`; the initial vector
  is `½` of the one-sided derivative of the last-stage piece at `0` (needs `time last < T`).
- Progress 2: backward continuation, initial-vector uniqueness and the splice compile clean.
- Final (2026-09-26): `Surgery/Topology/HistoryLGeometry/Truncation.lean`, 798 lines, LF, single
  import `HistoryLGeometry.MinDomain` (H4). No sorry/nolint/heartbeat/synth options, no comments or
  docstrings, lines ≤ 100 chars, only `set_option autoImplicit false`. No other repo edits, no git
  writes, root aggregate not touched (register after `MinDomain`).
- Compile: scratch `h3a/src/H5Test.lean` (import renamed to `H3aPre.MinDomain`, body identical by
  `diff --strip-trailing-cr`) via `LEAN_NUM_THREADS=2 lean` with the scratch olean dir first on
  `LEAN_PATH`: no errors, warnings or infos (34 s). Probe `H5Lint.lean` with
  `linter.mathlibStandardSet` + `#lint`: "All linting checks passed" (24 declarations, 14 linters).
  Axioms of all 12 public theorems: propext, Classical.choice, Quot.sound.
- Public API (namespace `ObservedHistory`; `hfloor : ∀ j, ∀ t ∈ stageDomain j, ∀ x, -B ≤ R` as in H4;
  `k` = any stage with `hk : T - v₁² ∈ stageDomain k`, e.g. `activeStage (T - v₁²)` via
  `activeStage_mem`; at an event time `T - v₁²` this is the new stage, the old stage and that
  crossing are dropped — no restriction needed):
  - `first_le_of_mem_stageDomain (hv₁ : 0 ≤ v₁) (h12 : v₁ ≤ v₂) (hlower) (hk) : first ≤ k`.
  - `regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁ h12 hk hfloor α hα hnode
    hmin hfin`: the truncation `fun j : StageInterval k last => α ⟨j, _, _⟩` has action =
    `regularizedCost k last hkl T B 0 v₁ (α last 0) (α k v₁)` and ≠ ⊤ (dynamic programming:
    `mem_regularizedActionValues_split_at_parameter` at `c = v₁`, `WithTop.add_le_add_iff_right`).
  - `truncate_mem_regularMinimizerEndpoints` (DESIGN §3 first display, with the finite-cost
    hypothesis `hfin`, which the splice argument needs): `α k v₁ ∈ regularMinimizerEndpoints k last
    hkl T B v₁ (α last 0)` and its cost ≠ ⊤.
  - `HasHistoryLInitialVector.truncate (hv₁ : 0 < v₁) hfk hk h`, `isHistoryLGeodesicOn_truncate`.
  - `mem_historyMinDomain_of_le hfloor hkl hv₁ h12 hk : Z ∈ historyMinDomain hle T B v₂ p →
    Z ∈ historyMinDomain hkl T B v₁ p`; `historyMinDomain_subset_of_le` (nesting, §3).
  - `historyLExp_eq_historyLCurve_of_le hfloor hfk hkl hv₁ h12 hk Z hZ Z' (hZZ' : Z'.1 = Z.1) :
    historyLExp hkl T v₁ p Z' = historyLCurve hle T v₂ p Z ⟨k, hfk, hkl⟩ v₁` (item 2).
  - `image_historyMinDomain_subset_of_le : historyLExp hkl T v₁ p '' (val ⁻¹' Ω̄_{v₂}) ⊆
    regularMinimizerEndpoints k last hkl T B v₁ p ∩ {q | cost ≠ ⊤}` (the last step of §5's chain).
  - `IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi hfloor hα hαac hβac hβcross hβmin hβfin hv (hs₀ : s₀ < v)
    hA j`: a history L-geodesic α and a finite-cost regular minimizer β that agree for parameters
    `> s₀` agree on every closed piece (backward uniqueness; inf argument; step: α's window at `s`,
    β lifted into `W.restrict` by H2a's lift lemma, `lRegularizedSolution_eqOn`; at `r = s` pieces
    ending at `s` are handled by `regularCrossing_right_unique`).
  - `HasHistoryLInitialVector.eq_of_eqOn hle (hT : time last < T) hα hβ hη (h : EqOn (α last)
    (β last) (Icc 0 η)) : Z = Z'` (`mfderivWithin` on `Icc 0 e'` = `2 • Z`).
  - `injOn_historyLExp_of_lt hkl hfloor (hT : time last < T) (hv₁ : 0 < v₁) (h12 : v₁ < v₂) hk :
    InjOn (historyLExp hkl T v₁ p) (Subtype.val ⁻¹' historyMinDomain hle T B v₂ p)` (item 3).
    Proof: splice γ = β on `r ≤ v₁` / α on `r ≥ v₁` (stage `k` by `piecewise (Iic v₁)`); equal
    truncated costs give action γ = action α = cost, crossings of γ are those of β (below `k`) or α;
    backward uniqueness α = γ on all pieces; hence α last = β last on `[0, min v₁ …]`, so `Z₁ = Z₂`.
    No corner/first-variation lemma is needed: H2a's minimizer ⇒ window-geodesic regularity plays
    its role.
- Honest limits. (i) `hT : time last < T` in injectivity (and `eq_of_eqOn`): at `T = time last` the
  last-stage piece is `{0}` and the initial vector is not read off the last stage; same restriction
  as H4's surjectivity (`T ∈ Ioo (time last) (stageEndTime last)`). (ii) `not_conjugate_of_lt`
  (DESIGN §3 last display) is not in this brick: it needs H6's index form.
- What H8 consumes (§5): "`= ∫_{f_{v₁} '' K} dens(v₁)` (injective, `injOn_historyLExp_of_lt`,
  `lintegral_image_eq_lintegral_paramDensity_mul`) `≤ Ṽ(v₁)` (`f_{v₁} '' K ⊆
  regularMinimizerEndpoints(v₁)` by truncation, §3)". Shapes: `K` at `v₂` is `val ⁻¹' Ω̄_{v₂}` in
  `historyLExpDomain hle T v₂ p`, while `f_{v₁} = historyLExp hkl T v₁ p` has domain
  `historyLExpDomain hkl T v₁ p`; both are subtypes of `TangentSpace ThreeModel p` and
  `mem_historyMinDomain_of_le` + `historyMinDomain_subset_historyLExpDomain` move `K` across.
  The pointwise `ℓJ(v₂) ≤ ℓJ(v₁)` (§4) evaluates `historyLExp` at `v₁` through
  `historyLExp_eq_historyLCurve_of_le` (the `v₂`-curve at parameter `v₁`). §7 row: "H5 |
  Truncation, nesting, injectivity at `v₁ < v₂` | `…/Truncation` | history | 1400 | H4".
