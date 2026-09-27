# Lane H7a log: history weighted Jacobian (DESIGN_22 §4, row H7a)

- 2026-09-26 start. Target `Surgery/Topology/HistoryLGeometry/Jacobian.lean`.
  Read: AGENTS.md, NAMING.md §2–6, DESIGN_22 §1/§4/§7, H3b log + `ExponentialSmooth.lean`,
  H3a `Exponential.lean`, H4 `MinDomain.lean`, H5 `Truncation.lean`, H2b `Seam.lean`, G2
  `Jacobian/Naturality.lean`, `Jacobian/Basic.lean` (`lGram` :53, `lGramDeriv` :60,
  `lJacobianDensity` :72, `lJacobianDen_hasDeriv` :96), G5 `Jacobian/GramIndexBound.lean:366`,
  `Parametric/Defs.lean` (`paramGramMatrix`, `paramDensity`).
- Compile route: scratch `scratchpad\h3a` (modules `H3aPre.*`, bodies checked identical to the repo
  files for Exponential/Seam/Window/Regularity/MinDomain/Truncation/Naturality). Added
  `H3aPre.ExponentialSmooth` built from the repo file (only import renamed), 36 s, clean.
- Finding (supplier gap): H3b exports only endpoint smoothness in `Z` at fixed `v`
  (`exists_nhds_contMDiffOn_historyLExp`). The joint C^∞ window family `β` on `V ×ˢ (c-η, c+η)`
  lives in the private invariant `HasPrefixFamily`; it cannot be reached from another module.
  Joint smoothness does not follow from separate smoothness. Plan: state the window family as
  explicit hypotheses (window `W`, open `V ∋ Z₀`, open `K`, `β` C^∞ on `V ×ˢ K`, geodesics,
  representation `historyLCurve Z j r = W.f j (β (Z, r))` on `K ∩ piece j`) and prove (1)–(3) from
  them. Discharging needs an export from `ExponentialSmooth` (see final entry).
- Progress 1 (~07:10): `Jacobian.lean` 466 lines compiles clean in scratch (`h3a/h7a.sh`: repo file
  with the import renamed to `H3aPre.ExponentialSmooth`, `LEAN_NUM_THREADS=2 lean`). Delivered:
  definitions (`historyLCurveMap`, `historyLJacobiField`, `historyLGram`, `historyLJacobianDensity`,
  `historyLSourceDensity`, `historyReducedJacobian`), generic single-flow Jacobi lemma
  `isLRegularizedJacobi_mfderiv_of_contMDiffOn`, window Gram identity, τ-derivative, window
  continuity, one-sided seam limits, `paramDensity` relation, density identity.
- Final (2026-09-26 ~07:45): `Surgery/Topology/HistoryLGeometry/Jacobian.lean`, 496 lines, LF,
  single import `HistoryLGeometry.ExponentialSmooth`. No sorry/admit/axiom, no nolint/heartbeat/
  synth options, no comments/docstrings, only `set_option autoImplicit false`, lines ≤ 100 (import
  excepted). Compile: `h3a/h7a.sh` (repo file, import renamed to `H3aPre.ExponentialSmooth`,
  `LEAN_NUM_THREADS=2 lean`): no errors, warnings or infos. `linter.mathlibStandardSet` + `#lint`:
  only `docBlame` on the 6 defs (excluded by AGENTS.md). Axioms of all 29 public declarations:
  propext, Classical.choice, Quot.sound. Public names grep-unique library-wide. No other repo
  edits, no git writes, root aggregate not touched (register after `ExponentialSmooth`).
- Definitions (namespace `ObservedHistory`): `historyLCurveMap hle T v p Z₀ j s : ThreeSpace →
  stage j` (`Z ↦ historyLCurve ⟨Z, _⟩ j s`, default `historyLCurve Z₀ j s` off the domain);
  `historyLJacobiField … Z₀ j i s := mfderiv (historyLCurveMap … j s) Z₀ (chartModelBasis i)`;
  `historyLGram … Z₀ j s := paramGramMatrix (stageMetric j (T - s²)) (historyLCurveMap … j s) Z₀`;
  `historyLJacobianDensity := paramDensity (same)` (= √det historyLGram, rfl);
  `historyLSourceDensity T p := √det (⟨e_i, e_k⟩_{stageMetric last T, p})`;
  `historyReducedJacobian hle T v p Z₀ := historyLJacobianDensity … ⟨first,_,_⟩ v /
  historyLSourceDensity T p * exp(-historyLAction/(2v) - (3/2) log v² - (3/2) log 4π)`
  (single-flow normalization `lReducedJacobian = exp(log(lExpDensity/lSourceDensity) - lCost/(2√τ)
  - (n/2) log τ - (n/2) log 4π)` at τ = v², and exactly H4's `regularizedDensity_historyLExp_eq`).
- Window theorems take the window family as explicit hypotheses (W, V ∋ Z₀ open ⊆ domain, K open ⊆
  Ioo W.a W.b, β C^∞ on V ×ˢ K, geodesics, `historyLCurve ⟨Z,_⟩ (lift j) r = W.f j (β (Z, r))` on
  `K ∩ Ioo piece_j`). Discharging them needs an export from ExponentialSmooth's private chain.
- Not delivered: (a) the family export; (b) seam value at `s = w` itself (only both one-sided
  limits, equal to the window value); (c) continuity of the action factor in `s`; (d) truncation of
  non-minimizing history geodesics (needed so that `v ↦ historyReducedJacobian (first v) … v` is
  the v₂-curve density: H5's `historyLExp_eq_historyLCurve_of_le` needs `Z ∈ historyMinDomain`,
  which is not a neighbourhood).
