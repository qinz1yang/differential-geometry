# G1c fill log

2026-09-26. Curve-level closed START. One new file, unwired:
`Perelman/LGeometry/Geodesic/ClosedStartCurve.lean` (358 lines).

- `exists_lRegularizedFamily_of_start`: `IsSolutionOn S`, `hmetric` on `Ico a c`, `a < c`, `0 < v`,
  `T - v^2 = a`, `Ico 0 v ⊆ lRegularizedDomain S T x Z0`, and the tangent lift
  `s ↦ ⟨γ s, lVelocity γ s⟩` of `γ = lRegularizedCurve S T x Z0` tending to some `ξ` in `TM` as
  `s → v⁻`. It gives `V ∋ Z0` open, `δ > 0`, `β` `C^∞` on `V ×ˢ Ioo (v-δ) (v+δ)`, and for `Z ∈ V`:
  `Ico 0 v ⊆ lRegularizedDomain S T x Z` and `β (Z, ·) = lRegularizedCurve S T x Z` on `Ioo (v-δ) v`.
  Route: `exists_lPhaseFlow_of_start` at `(v, chart state of ξ)`; `s₁ < v` close to `v`;
  `lRegularizedFamily_extend` at `s₁`; `lRegularizedFamily_step_of` with the window
  `Ioo (2s₁-v) v` (domain part); `lRegularizedSolution_eqOn` against the flow curve (equality part).
  `D` is arbitrary; only `T - s^2`, `s < v`, enter `D.regular`, so the metric below `a` never enters.
- `tendsto_lVelocity_lift_of_family`: a curve that agrees on `Ioo (v-δ) v` with a curve `C^∞` on
  `Ioo (v-δ) (v+δ)` has tangent lift converging to that curve's lift at `v` (item 1).
- `isOpen_setOf_tendsto_lRegularizedCurve_of_start`: the set of `Z` with `Ico 0 v` in the domain
  and convergent tangent lift at `v⁻` is open (item 3, the one-sided domain form for H3b/G3).
- Item 4 (gluing) is not a new lemma: `lRegularizedFamily_step_of` already glues.
- Why convergence is a hypothesis: it is not derivable. Counterexample: static flat metric on
  `ℝ³ \ {p}`, `p = x + 2vZ`; the curve exists on `[0, v)` and leaves every compact set. With
  compactness it would need a Gronwall bound on `|X|`, which is not built. Consumers (the history
  L-geodesic on a closed window) have the curve on the closed window, so they have the limit.
- G1b check: both G1b files compile WITHOUT `-DmaxSynthPendingDepth=3` (scratch concatenation,
  plain `lake env lean`). No defect.
- Duplicates to merge later: private `contDiffAt_chartSeed` = private `lPhaseSeed_smooth`
  (ExponentialMap); private `isLRegularizedGeodesicOn_lPhaseCurve` = inline blocks of
  `exists_lRegularizedFamily` / `lRegularizedFamily_step_of`.
- Compile: scratch concatenation outside the repo (G1b file 1, G1b file 2, this file), then
  `LEAN_NUM_THREADS=2 lake env lean`, no `-D`: clean. `#lint`: passed (17 declarations).
  With `linter.mathlibStandardSet`: clean. Axioms (3 public theorems): propext, Classical.choice,
  Quot.sound.
- Later (G1d): `isLRegularizedGeodesicOn_lPhaseCurve` made public (G1d imports it). Rechecked clean.
