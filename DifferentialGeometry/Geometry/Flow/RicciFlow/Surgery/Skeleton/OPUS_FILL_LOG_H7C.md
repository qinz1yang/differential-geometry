# Lane H7c log: limit of the history reduced Jacobian at v → 0 (DESIGN_22 §4, row H7c)

- 2026-09-26 13:50 UTC start. Worktree head 0798da941 (brief said a161fc07e; H7a/H3b' files
  `Jacobian`, `ExponentialFamily`, `JacobianUnconditional` still uncommitted). Target
  `Surgery/Topology/HistoryLGeometry/JacobianLimit.lean`. Compile route: scratch
  `scratchpad\h3a` (`H3aPre.*` modules; bodies checked identical to the repo files modulo import
  names and CRLF), read-only `lean` via `h3a/chk.sh`, no `lake build`.
- Read: AGENTS.md, DESIGN_22 §1/§4, H7A and H3B2 logs, `Jacobian.lean`, `Exponential.lean`
  (`IsHistoryLGeodesicOn`, `HasHistoryLInitialVector`), `MinDomain.lean`, `ExponentialSmooth.lean`
  (base family), `ShortTime/{JacobianLimit,ReducedLengthLimit,ReducedJacobianLimit}.lean`.
- Findings before coding:
  - The single-flow limit is `π^{-n/2} exp(-g_T(Z,Z))`, not 1 (`tendsto_lReducedJacobian_at_zero_of_bdd`).
  - `lReducedJacobian` uses `redLength = lCost/(2√τ)`, a global infimum over the whole manifold of
    the flow. On a base window `W.X` it is not the history action unless the geodesic minimizes in
    `W.X`. So the identity is stated with the local normalization (`lExpJacobian` and the window
    geodesic's own action), and the limit is proved from the local single-flow limits
    `tendsto_normalized_lExpDensity_at_zero` and `tendsto_lRegularizedAction_div_at_zero`
    (neither needs minimality).
  - `LWindow.metric` pins the window metric only on the open parameter range, so `s = 0` (time
    `T`) needs a separate left-continuity argument on both sides (`coeff_cont`).
- ~14:45 UTC progress: scratch `h7c/JL5.lean` compiles clean (private layer): left-continuity of
  `stageMetric` inner products at a stage time (`coeff_cont` of the incoming/final slab flow), the
  base-window metric identity at `T` itself (`W.S.base.metric T = localPullMetric …`, limit
  uniqueness from the left), the base-window curve `W.f ∘ lRegularizedCurve W.S T x Zx` as a
  history geodesic with initial vector on `(0, min W.b √(T − time last))`, the action identity
  `historyLAction = lRegularizedAction W.S T (lRegularizedCurve …) 0 v`, and the density ratio
  `historyLJacobianDensity/historyLSourceDensity = paramDensity(W metric, Z ↦ curve(Z, v))(Zx) /
  √det(W metric at T, x)` (via `paramDensity_comp`, `paramDensity_comp_of_inner_eq`,
  `BilinForm.toMatrix_comp`). Built `ParamDensityComposition` (committed repo file, unbuilt in
  pc3's .lake) as scratch module `H3aPre.ParamDensityComposition` (import renamed back in repo).
  Next: public identity, the limit, the antitone corollary.
- Final (~15:40 UTC). `Surgery/Topology/HistoryLGeometry/JacobianLimit.lean`, 749 lines, LF. Imports
  `HistoryLGeometry.{Jacobian,Truncation}`, `Analysis/Integration/Measure/ParamDensityComposition`
  (in the root aggregate but not yet built in pc3's `.lake`), `ShortTime.ReducedJacobianLimit`.
  No sorry/admit/axiom, no nolint/heartbeat/synth options, no comments/docstrings, only
  `set_option autoImplicit false`, lines ≤ 100 (imports excepted). No other repo edits, no git
  writes, root aggregate not touched (register after `Jacobian`, `Truncation`).
- Compile: repo file with the three history/measure imports renamed to `H3aPre.*` (diff otherwise
  identical), `lean` read-only via `h7c/chk.sh` (LEAN_PATH = private snapshot `h7c/olean/H3aPre`
  + pc3 `.lake`): no errors, warnings or infos. `linter.mathlibStandardSet` + `#lint`: all passed
  (25 declarations). Axioms of the 5 public theorems: propext, Classical.choice, Quot.sound. Public
  names grep-unique library-wide.
- Environment note: at 07:37 PDT someone created an empty `h3a/olean/DifferentialGeometry/` in the
  shared scratch; it shadows the whole `DifferentialGeometry` package for every `h3a/chk.sh` user
  (error "object file …/olean/DifferentialGeometry/Analysis/… does not exist"). I did not touch it;
  I switched to a private snapshot `h7c/olean`. Whoever owns it should delete it.
- Public API (namespace `ObservedHistory`, all for `first = last`, `hle = le_refl last`,
  `hT : H.time last < T`):
  1. `exists_lWindow_historyReducedJacobian_eq hT (Z₀ : historyLExpDomain (le_refl last) T v₀ p)`:
     ∃ base window `W : LWindow last last T`, `x`, `Zx` with `W.a = 0`, `W.f x = p`,
     `mfderiv (W.f) x Zx = Z₀`, `W.S.base.metric T = localPullMetric (stageMetric last T) W.f _`,
     and `δ > 0` such that for all `v ∈ (0, δ)`: `Z₀ ∈ historyLExpDomain … v p` and
     `historyReducedJacobian … v p ⟨Z₀, _⟩ = paramDensity (W.S.base.metric (T − v²))
     (Z ↦ lRegularizedCurve W.S T x Z v) Zx / √det(W.S.base.metric T at x) *
     exp(−lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v/(2v) − (3/2)log v² −
     (3/2)log 4π)`, i.e. `lExpJacobian W.S T x Zx (v²)` times the window geodesic's own weight.
  2. `tendsto_historyReducedJacobian_nhdsGT_zero hT Z₀`: `v ↦ (if h : Z₀ ∈ historyLExpDomain … v p
     then historyReducedJacobian … v p ⟨Z₀, h⟩ else 0)` tends to
     `(π^(3/2))⁻¹ * exp(−(stageMetric last T).inner p Z₀ Z₀)` along `𝓝[>] 0`.
  3. `le_gaussian_of_antitoneOn_of_eventuallyEq_historyReducedJacobian hT Z₀ (hF : AntitoneOn F
     (Ioc 0 v₂)) (hbase : ∀ᶠ v in 𝓝[>] 0, ∀ h, F v = historyReducedJacobian … v p ⟨Z₀, h⟩)
     (hv : v ∈ Ioc 0 v₂) : F v ≤ Gaussian` (the shape H8 uses with `F v = historyReducedJacobian
     (first v) …` once H7b lands); `historyReducedJacobian_le_gaussian_of_antitoneOn` is its
     specialization to the base-window function.
  4. `exists_pos_historyReducedJacobian_le_gaussian hT hfloor (hv₂ : 0 < v₂)
     (hZ₀ : Z₀ ∈ historyMinDomain (le_refl last) T B v₂ p)`: ∃ δ > 0, ∀ v ∈ (0, δ), ∀ h,
     `historyReducedJacobian … v p ⟨Z₀, h⟩ ≤ Gaussian`. Unconditional: history minimality is
     transported to `(Zx, c²) ∈ lMinDomain W.S T x` plus the `BddBelow` competitor bound
     (`LWindow.lRegularizedAction_le_of_regularizedCost_eq` on the restricted window and a global
     C^∞ competitor built with a `ContDiffBump` reparametrization), then the single-flow
     `lReducedJacobian_le_gaussian_of_bdd`, `lRedJac_mul_src_of_nonconj`, `lMinDomain_down_of_bdd`.
- Honest limits: (a) the identity uses `lExpJacobian` and the window geodesic's action, not
  `lReducedJacobian`'s global `lCost` of `W.X`; equality with `lReducedJacobian` holds exactly where
  the geodesic minimizes in `W.X`, which item 4 proves for history minimizers. (b) `δ` depends on
  the window supplied by `HasHistoryLInitialVector` (`δ = min W.b √(T − time last)`), so items 1
  and 4 cover `v < δ`, not the whole base window `v < √(T − time last)`; the whole base window
  needs a single stage-wide window (G1 at `T = horizon`). The limit and item 3 need only small `v`.
  (c) `T = time last` (base time an event time, glued seam window) is excluded by `hT`.
