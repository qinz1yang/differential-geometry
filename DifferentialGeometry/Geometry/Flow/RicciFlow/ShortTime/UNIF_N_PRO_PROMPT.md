# GPT Pro consult prompt — black box (N) uniformization route ruling (2026-07-22)

Send in a fresh chat of the ChatGPT project "Lean Pro Consult Handoff".

---

I am working in a large Lean 4/mathlib project. Do not write code first. This is a ROUTE/DESIGN review for a uniformization frontier: diagnose the obstruction, rule on the route, and give a small lemma frontier.

Target theorem:
`ricci_flow_unif_existence` — the only `sorry` of `DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean` ("black box (N)"): for a fixed background metric `gBase` on a closed manifold, for every `Λ ≥ 1` there is a UNIFORM time `τ₀(gBase, Λ, S) > 0` such that every smooth `g₀` that is `Λ`-comparable to `gBase` and has `MetricCovDerivOrderBoundOn` jets of order `a ≤ 3` bounded by `Λ` admits a Ricci flow on `[0, τ₀)` with interior C∞ chart-Gram, C⁰ up to `t = 0`, and the flow PDE. This is the last `sorryAx` source of the `extends_of_rmBounded` route.

Relevant definitions / audited facts (Stage-0 audit is LOCAL-ONLY, distilled here; the Lean files below are on the pushed branch):
- Per-datum existence is PROVED sorry-free: `deturck_ricci_flow_parabolic_short_time_existence` (`ShortTime/DeTurckInitialDataExistence.lean`) assembling the engine `quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence` (`ShortTime/QuasilinearAbstractShortTimeExistence.lean`) at Sobolev order `N₀ = 4·finrank + 10` on the `g₀`-intrinsic spectral scale (`tensorHs g₀`).
- The engine's abstract time is explicit: `T₀ = min 1 (min (1/(64(C₂+1)²)) ((1/(16(C₁+1))/(2(‖Nfun 0‖+1)))²))` at `Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:701`, with `C₂ = K·Csym1`, `C₁ = K·Csym1·Csym2·(1+1/R₀)` (decomposition at `Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.lean:3322`; `Csym1/Csym2` symmetrization `H^s` op-norm constants from a norm-equivalence `Classical.choose` at `:2727`; `R₀` ellipticity/embedding radius `:2346→:2175`; `K` ball-Lipschitz `:2050`; `‖Nfun 0‖ ≈ ‖−2·Ric(g₀)‖_{H^a_{g₀}}` at `:2783`). All are `Classical.choose`s of `g₀`-intrinsic Sobolev-scale facts; there is NO explicit `Λ`-formula and NO cross-metric (class-uniform) Sobolev comparison layer anywhere in the codebase.
- Worse, the engine RETURNS `T₁ = min(T₀, d/2, d₂, d₂F)`, not `T₀`, from `maxreg_solution_jointly_smooth_representative_of_nemytskii` (`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean:957`, witness `:1141`) — a bare `∃ T₁, 0 < T₁`, where `d` is a δ extracted from a QUALITATIVE `ContinuousWithinAt` of the solution at `t = 0` (`:1138`) and `d₂, d₂F` are existential bootstrap horizons. None has a quantitative floor.
- Input side is clean: `A(n) = 4·finrank + 12` jets (in the `g₀`-spectral `H^a` norm) suffice for the data-norm bound, and the Lemma-3.11/Shi producers (`HCGCompactness/AllTimesBounds.lean:691,773,793,4415`) are order-generic, so raising (N)'s hypothesis `a ≤ 3 → a ≤ A(n)` is available on the producer side. It is necessary but NOT sufficient.

What was tried:
- Stage-0 constant-provenance audit only (no Lean written). The naive plan "thread `Λ` through the existing per-datum producers" was refuted: the constants are non-explicit chooses on a `g₀`-dependent scale, and the returned time has qualitative components.

Route options on the table:
- (R1′) Build the uniformization lane on top of the existing engine: (i) a class-uniform cross-metric `H^{A(n)}` comparison layer — `‖·‖_{H^s_{g₀}} ≍_{Λ,n,s} ‖·‖_{H^s_{gBase}}` for `Λ`-comparable metrics with jet bounds, then transfer `Csym1/Csym2/R₀/K/‖Nfun 0‖` from the FIXED `gBase` scale with `Λ`-controlled loss; and (ii) a quantitative time-floor layer: replace the qualitative `t = 0` δ and the bootstrap horizons by explicit floors from the same class constants (e.g. a maximal-regularity a-priori modulus of continuity at `0`). Estimated multi-week.
- (R1″) Re-derive the maximal-regularity engine on the FIXED `gBase` Sobolev scale (cross-metric problem dissolves; large rework; risks duplicating the sorry-free engine).
- (R2) Park (N); the branch's separate low-regularity Koch–Lamm lane (honest `C³` hypotheses; Euclidean heat/Duhamel machinery, key checkpoint `heatD2Past_l2` ≈ 45%) would eventually subsume it. Months.

GitHub reference to inspect before answering:
- Branch: https://github.com/liao9yuan/differential-geometry/tree/codex/analytic-producers-e87b (tip `922dbc4ac` = the audited state; the Stage-0 audit `.md` itself is local-only and distilled above)
- Relevant files:
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/QuasilinearAbstractShortTimeExistence.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/SobolevNonlinearityExistence.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean
  - https://github.com/liao9yuan/differential-geometry/blob/codex/analytic-producers-e87b/DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/AllTimesBounds.lean

Constraints:
- Preserve public APIs unless a statement is mathematically wrong; the per-datum engine is sorry-free and must not be destructively rewritten.
- Prefer small helper lemmas. Avoid broad refactors. Do not suggest blind automation as the main plan.
- The (N) hypothesis upgrade `a ≤ 3 → a ≤ A(n)` is pre-cleared on the producer side and may be assumed acceptable.
- Give a prompt for only the next implementation step.

Tasks:
1. Classify the obstruction: local proof search, missing lemma, wrong statement, coercion issue, typeclass issue, or design issue — and RULE between R1′, R1″, R2 (or a better hybrid).
2. State the smallest useful helper lemmas for the chosen route. In particular: is the cross-metric `H^s` comparison the right first brick, and what is the cleanest quantitative replacement for the qualitative `t = 0` δ (a-priori maximal-regularity modulus? restating the representative lemma with an explicit floor? a different decomposition that avoids `T₁` entirely)?
3. Give the proof strategy in Lean terms.
4. Tell me what to implement next.
5. Tell me what failure signal should make the agent stop.
