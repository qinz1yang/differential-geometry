# Lane H4 log: history minimizing domain, surjectivity, density identity (DESIGN_22 §2, brick H4)

- 2026-09-26 start. Target file `Surgery/Topology/HistoryLGeometry/MinDomain.lean`.
  Inputs read: AGENTS.md, DESIGN_22 §0/§2/§5/§7, OPUS_FILL_LOG_H3A/H2A, H3a `Exponential.lean`,
  H0 `HistoryScalarFloor.lean`, `ReducedVolumeTruncation.lean`, `NoncollapsingThroughSurgeryLeaves.lean`,
  `HistoryReducedDensity.lean`, `HistoryAction/AbsoluteContinuity.lean`.
- Compile route: reuse the H3a scratch build (`scratchpad\h3a`, modules `H3aPre.*`). Checked that
  `H3aPre.{PartialDiffeomorph,Naturality,Window,Regularity,Seam}` bodies are identical to the repo
  files (`diff --strip-trailing-cr`, imports stripped); built `H3aPre.Exponential` from the current
  repo `Exponential.lean` (body identical) with `lean --root=. -o` (40 s, clean).
- Plan: `historyMinDomain : Set (TangentSpace ThreeModel p)` = initial vectors `Z` with a witness `α`
  that is the history L-geodesic of `Z` (`IsHistoryLGeodesicOn` + `HasHistoryLInitialVector`) and
  a finite-cost regular minimizer (AC, `α last 0 = p`, action = cost ≠ ⊤). `⊤`-cost endpoints are
  excluded from the image and carry density 0 (`regularizedDensity_eq_zero_of_regularizedCost_eq_top`),
  so the set lintegral over `regularMinimizerEndpoints` equals the one over the image (no
  measurability needed: a function vanishing on `s` has zero lintegral against `μ.restrict s`).
- Final (2026-09-26): `Surgery/Topology/HistoryLGeometry/MinDomain.lean`, 284 lines, LF. No sorry,
  nolint, heartbeat or synth options; no comments or docstrings; lines ≤ 100 (chars); only
  `set_option autoImplicit false`. Imports: H3a `HistoryLGeometry.Exponential` and H0
  `HistoryScalarFloor` (brings `ReducedVolumeTruncation`, `NoncollapsingThroughSurgeryLeaves`).
  No other repo edits, no git writes, root aggregate not touched (register after `Exponential`).
- Compile: scratch copy `h3a/src/H4Test.lean` (first import `H3aPre.Exponential`, body identical,
  checked with `diff --strip-trailing-cr`) via `LEAN_NUM_THREADS=2 lean` with
  `LEAN_PATH=<scratch olean>;$(lake env printenv LEAN_PATH)`: clean, no errors/warnings/info (45 s).
  `linter.mathlibStandardSet` + `#lint`: only `docBlame` on the three defs (excluded by AGENTS.md).
  Axioms of all 19 public ObservedHistory declarations and the RetainedCoreHistory corollary:
  propext, Classical.choice, Quot.sound.
- Definitions (namespace `ObservedHistory`):
  - `historyLCurve hle T v p Z` := the chosen history L-geodesic of `Z : historyLExpDomain`
    (`historyLExp Z = historyLCurve Z first v` by `rfl`).
  - `historyLAction hle T v p Z : ℝ` := `∑ j, stageRegularizedAction j T (historyLCurve Z j)
    (regularizedStageStart T 0 j) (regularizedStageEnd T v j)` (the real L-length; no `B`).
  - `historyMinDomain hle T B v p : Set (TangentSpace ThreeModel p)` (= Ω̄_v of §0 item 1, closed:
    minimizing up to `v` itself) := `{Z | ∃ α, IsHistoryLGeodesicOn hle T v α ∧
    HasHistoryLInitialVector T α p Z ∧ (∀ j, AC (α j) on its piece) ∧ α last 0 = p ∧
    regularizedExtendedAction … α = regularizedCost … p (α first v) ∧ regularizedExtendedAction … α ≠ ⊤}`,
    i.e. the geodesic of `Z` is itself a finite-cost witness of `α first v ∈ regularMinimizerEndpoints`.
- Theorems (implicit `first last hle T B v p`):
  - `historyMinDomain_subset_historyLExpDomain`; `eqOn_historyLCurve` (chosen curve = any geodesic
    with the same initial vector on every closed piece); `regularizedExtendedAction_historyLCurve_eq`.
  - `historyLExp_mem_regularMinimizerEndpoints (hv) Z (hZ : Z.1 ∈ historyMinDomain …)`,
    `regularizedCost_historyLExp_ne_top`, `image_historyMinDomain_subset (hv) : historyLExp '' (val ⁻¹' Ω̄)
    ⊆ regularMinimizerEndpoints ∩ {q | cost p q ≠ ⊤}` (no `hT`, no floor).
  - With `hfloor : ∀ j, ∀ t ∈ stageDomain j, ∀ x, -B ≤ R` (H0 floor `b` plus `b ≤ B`):
    - `exists_historyLExp_eq_of_mem_regularMinimizerEndpoints (hv) (hT : T ∈ Ioo (time last)
      (stageEndTime last)) (hq) (hfin : cost p q ≠ ⊤) : ∃ Z, Z.1 ∈ Ω̄ ∧ historyLExp Z = q`
      (unpack, `subst hp hq`, H3a's `isHistoryLGeodesicOn_of_regularizedCost_eq` and
      `exists_hasHistoryLInitialVector_of_regularizedCost_eq`; `hfin` for H2a from `hmin ▸ hfin`).
    - `image_historyMinDomain (hv) (hT) : historyLExp '' (val ⁻¹' Ω̄) = regularMinimizerEndpoints ∩
      {q | cost p q ≠ ⊤}` — the precise surjectivity.
    - Cost `⊤`: `regularizedDensity_eq_zero_of_mem_diff_image (hv) (hT)`: density 0 on
      `regularMinimizerEndpoints \ image`; `setLIntegral_regularMinimizerEndpoints_eq (hv) (hT) μ`:
      `∫⁻ q in regularMinimizerEndpoints, dens ∂μ = ∫⁻ q in historyLExp '' (val ⁻¹' Ω̄), dens ∂μ` for any
      measure, no measurability (private helper: `f = 0` on `s` ⇒ `∫⁻ in s, f = 0`, simple-function
      proof; generic, worth promoting to `Analysis/` later).
    - `regularizedExtendedAction_historyLCurve_eq_historyLAction`, `regularizedCost_historyLExp_eq :
      cost p (historyLExp Z) = ↑(historyLAction Z)` and the density identity
      `regularizedDensity_historyLExp_eq (hv) Z hZ : regularizedDensity … B v p (historyLExp Z) =
      ENNReal.ofReal (Real.exp (-historyLAction Z / (2 * v) - (3/2) * Real.log (v ^ 2) -
      (3/2) * Real.log (4 * Real.pi)))` — exactly §2's displayed shape with `historyAction … Z v`
      realised as `historyLAction Z`.
  - `RetainedCoreHistory.exists_reducedVolume_eq_lintegral_image_historyMinDomain : ∃ b, ∀ B₀ ≥ b,
    ∀ k p T v hle, 0 < v → T ∈ Ioo (time k) (stageEndTime k) → reducedVolume k p T v =
    ∫⁻ q in historyLExp hle T v p '' (val ⁻¹' historyMinDomain hle T B₀ v p), dens ∂vol_first(T - v²)`
    (class-free: H0 floor for `hfloor`, `exists_reducedVolume_eq_lintegral` for the limsup).
- What H8 consumes (§5): "`Ṽ(v₂) = ∫_{regularMinimizerEndpoints(v₂)} dens` … `≤ ∫_{f_{v₂} '' K} dens`
  (surjectivity, §2; `Measure.restrict_mono` needs no measurability) … `≤ ∫_K ℓJ(v₂)` (area
  inequality with multiplicity, G7, plus the density identity of §2)". H4 gives the first step as an
  equality (`setLIntegral_regularMinimizerEndpoints_eq`, or the RetainedCoreHistory corollary at
  `B₀ ≥ b`), and the pointwise `φ (f Z) = ofReal (exp (-historyLAction Z/(2v) - …))` for G7's
  `hφ : ∀ x ∈ K, φ (f x) ≤ h x`. §7 row: "H4 | `historyMinDomain`, surjectivity, density identity |
  `…/MinDomain` | history | 800 | H2, H3a, H0".
- Interface notes for H5/H8: `historyLExp` has a subtype domain, so `K` in H8 is `Subtype.val ⁻¹' Ω̄`
  inside `historyLExpDomain`; G7 wants `f : E → M` total on an open `U ⊇ K`, which is H3b's job
  (openness + a total extension). `historyMinDomain` is not shown measurable (entry 26).
- Base-time restriction (honest limits): surjectivity (and everything using it) is proved only for
  `T ∈ Ioo (time last) (stageEndTime last)`, inherited from H3a's initial-vector theorem. Closed
  cases open: `T = time last` (base at a seam: needs a seam base window with `W.a = 0`, ~80 lines in
  H2b/H3a) and `T = stageEndTime last` (= horizon for `last = Fin.last`, or the next event time,
  where `T ∉ stageDomain`-interior: needs G1). The image ⊆ direction, the density identity and
  `cost ≠ ⊤` hold for every `T` (they only use `hv`, and `hfloor` for the identity).
