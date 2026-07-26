# MapConvergence.lean — F7 convergence-of-maps + AA-for-maps engine (2026-06-11)

## 2026-07-15 compatibility split

The generic convergence definitions and elementary projections moved to
`Analysis/Calculus/MapConvergence.lean`. This file keeps the established import
path and the HCG-specific Arzelà--Ascoli extraction. Public namespaces and
declaration names are unchanged, and narrow verification passed.

MSM135 Ch4 subsection *Compactness of maps*: the Euclidean `C^p`/`C^∞` convergence
definitions for maps (`lbl373`) and the Arzelà–Ascoli-for-maps engine the isometry
corollary `lbl374` consumes. **Now fully sorry-free and axiom-clean** (the former
engine `sorry` in `exists_cInf_subseq` is PROVED; `#print axioms` shows only
`propext, Classical.choice, Quot.sound` for `exists_cInf_subseq` and both
`IsometryCompactness` consumers).

## What's here

**F7 definitions (sorry-free).** For maps between real normed spaces, `∇` = the
iterated Fréchet derivative `iteratedFDeriv ℝ r` (Euclidean gradient):
- `mapDerivNorm r Φk Φinf x = ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖`.
- `MapCPConvOn K p Φ Φinf` — `C^p` convergence on the compact `K` (direct
  `∀ r ≤ p, ∀ x ∈ K, ‖…‖ ≤ ε` form; equivalent to the book's displayed `sup ≤ ε`,
  avoids `sSup`).
- `MapCInfConvOnCompacts U Φ Φinf` — `C^∞` uniformly on compacts (`lbl373`).
- Parallel to `PointedConvergence.lean`'s `MetricCPConvOn`/`MetricCInfConvOnCompacts`.

**Order/subset/subsequence API (sorry-free).** `mapDerivNorm_nonneg`,
`MapCPConvOn.mono_order`, `.mono_set`, `MapCInfConvOnCompacts.cPConvOn`,
`MapCPConvOn.comp_subseq`, `MapCInfConvOnCompacts.comp_subseq`.

**Bridges (sorry-free).** `mapCPConvOn_of_tendstoUniformly`,
`tendstoUniformlyOn_of_cPConv`, `tendsto_of_cInf`.

**AA-for-maps engine (sorry-free, this pass).**
- `cmm_finiteDimensional` — `FiniteDimensional ℝ (E[×r]→L[ℝ] F)` for fin-dim `E, F`.
  Genuine Mathlib gap; curry induction via `continuousMultilinearCurryLeftEquiv`
  (base: `continuousMultilinearCurryFin0`), step instance
  `ContinuousLinearMap.instModuleFinite`.  Stated as a theorem, used via `haveI`
  (no new global instance per project rules).
- `equicont_iteratedFDeriv` (private) — order-`(r+1)` bound on `closedBall x₀ 1` ⇒
  `{∇ʳΦₖ}ₖ` uniformly Lipschitz there (MVT
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, derivative supplied by the
  `HasFTaylorSeriesUpTo.fderiv` field, norm via
  `ContinuousMultilinearMap.curryLeft_norm`) ⇒ `Equicontinuous` via
  `Metric.equicontinuousAt_iff`.
- `exists_cInf_subseq` — the engine, signature unchanged.

## Proof route actually used (deviations from the planned route)

1. Equicontinuity: as planned (MVT on unit closed balls), but the fderiv of
   `∇ʳΦ` comes from the **Taylor-series field** `(contDiff_infty.mp hΦ
   (r+1)).ftaylorSeries.fderiv r`, not `fderiv_iteratedFDeriv` — avoids all
   curry-equiv rewriting, and the cast `(r : WithTop ℕ∞) < r+1` is Nat-only
   (`exact_mod_cast lt_add_one r`).
2. Vector AA: NOT componentwise scalar AA.  Mathlib's general
   `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` specialized to a proper
   normed target (`ArzelaAscoli.lean:arzelaAscoli_isCompact_closure`), with
   `cmm_finiteDimensional` + `FiniteDimensional.proper_real` for the
   `ContinuousMultilinearMap` targets.
3. NO explicit diagonal over orders: the all-order derivative tuple sequence
   `k ↦ (r ↦ ∇ʳΦₖ)` lives in `Π r, closure (range (Fb r))` — a countable product
   of compact (AA) metrizable (sigma-compact domain) fibers — so ONE
   `IsCompact.tendsto_subseq` extracts a subsequence converging at every order
   simultaneously (same pattern as `DiagonalSubseq.exists_subseq_tendsto_pi`).
4. Derivative-of-limit: per order, `hasFDerivAt_of_tendstoUniformlyOn` on
   `Metric.ball x₀ 1` (uniform convergence on the closed ball, `.mono` to the open
   ball; curried family via
   `(continuousMultilinearCurryLeftEquiv …).isometry.uniformContinuous.comp_tendstoUniformlyOn`).
   Then — instead of an induction on `ContDiff n` — the limits `G r` directly form
   `HasFTaylorSeriesUpTo ⊤ (fun y => (G 0 y).curry0) (fun y r => G r y)` (fields:
   `rfl` / `hGderiv` / `(G m).continuous`), and `HasFTaylorSeriesUpTo.contDiff` +
   `HasFTaylorSeriesUpTo.eq_iteratedFDeriv` give smoothness and `∇ʳΦ_∞ = G r` in
   one shot.  Both lemmas exist in Mathlib — no iterated induction needed.
5. Wrap-up via `mapCPConvOn_of_tendstoUniformly`, rewriting `⇑(G r)` to
   `fun y => iteratedFDeriv ℝ r Φ_∞ y` with a `funext` of `eq_iteratedFDeriv`.

## Lean gotchas
- ContDiff smoothness exponent: write `ContDiff ℝ (⊤ : ℕ∞)` (repo idiom); bare `∞`
  is not in scope.  `contDiff_infty.mp h n` is the clean way to get every finite
  level from it (avoids `WithTop ℕ∞` coercion friction); `(… : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)`
  is `by exact_mod_cast le_top` (established Bundle-files pattern).
- `norm_image_sub_le_of_norm_hasFDerivWithin_le` lives in the `Convex` namespace
  (declared via dot-notation receiver as 3rd explicit arg).
- `hasFDerivAt_of_tendstoUniformlyOn` takes the point membership `hx : x ∈ s` as
  its last arg with `x` implicit.
- `iteratedFDeriv_sub_apply` needs `ContDiffAt`, reduce from `ContDiff … |>.contDiffAt.of_le`.
- `FiniteDimensional` needs `import Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `HasFTaylorSeriesUpTo` zero field is `(p x 0).curry0 = f x` (`curry0` is the
  *forward* evaluation `E[×0]→L F → F` in current Mathlib; `uncurry0` is `F → …`).
- `ftaylorSeries`/`ContinuousMap.mk` coercions all unify definitionally with the
  raw `iteratedFDeriv` lambdas — no `show`/`simp only` massage was needed.

## Verification
Focused check passed (no warnings); targeted builds of `MapConvergence` and
`IsometryCompactness` green; axiom audit clean (no `sorryAx`, no honest-input
axioms) for `exists_cInf_subseq`, `cmm_finiteDimensional`,
`arzelaAscoli_isCompact_closure`, `arzelaAscoli_subseq_vec`, `isometry_seq_cInf`,
`isometry_seq_diffeo`.

## Localized engine `exists_cInf_subseq_on` (B-loc, 2026-06-13)

Planner-authorized addition for MSM135 Ch4 Step B (the Step B maps live only on nested
Euclidean balls, not `Set.univ`). Two new declarations in the `MapArzelaAscoli` section,
both **axiom-clean** (`[propext, Classical.choice, Quot.sound]`), no edits to existing
theorems:

- `equicontOn_iteratedFDerivWithin` (private) — localized equicontinuity: the order-`r`
  within-derivative family is equicontinuous **as maps on the metric subspace `↥U`**.
  Same MVT as `equicont_iteratedFDeriv` but the ball is shrunk inside `U`
  (`closedBall x₀ (ρ/2) ⊆ U` from openness), the derivative comes from the *within*
  Taylor series `ContDiffOn.ftaylorSeriesWithin`, and `↥U`'s metric (`Subtype.dist_eq`)
  lets `Metric.equicontinuousAt_iff` apply directly — no `EquicontinuousWithinAt` API.
- `exists_cInf_subseq_on` — the localized extraction: `IsOpen U`, `ContDiffOn ℝ ⊤ (Φ k) U`,
  bounds on compacts ⊆ `U` ⇒ subsequence + `ContDiffOn ℝ ⊤ Φinf U` +
  `MapCInfConvOnCompacts U`.

### Route (what differs from the global proof)
- The bundled maps `Fb r k : C(↥U, …)` use `iteratedFDerivWithin ℝ r (Φ k) U` and are
  continuous on `↥U` (`ContDiffOn.continuousOn_iteratedFDerivWithin` + subtype val).
  `↥U` is locally compact (`IsOpen.locallyCompactSpace`) and second-countable hence
  sigma-compact, so the same product-compactness `tendsto_subseq` trick extracts one
  subsequence for all orders.
- The global `hbdd` (`iteratedFDeriv`) is converted to within-bounds by the
  **unconditional** `iteratedFDerivWithin_of_isOpen` (`EqOn (iteratedFDerivWithin ℝ n f U)
  (iteratedFDeriv ℝ n f) U` for any `f`) — the single bridge used throughout.
- Limits `G r : C(↥U, …)` are extended to `Gext r : E → …` by `dite (· ∈ U)`; subtype
  uniform convergence transfers to `U`-compacts via `Subtype.isCompact_iff` +
  `Subtype.image_preimage_coe` and `Metric.tendstoUniformlyOn_iff`.
- Derivative-of-limit: `hasFDerivAt_of_tendstoUniformlyOn` on an **open ball ⊆ U**
  (`HasFDerivWithinAt.hasFDerivAt` since the ball is open), assembled into
  `HasFTaylorSeriesUpToOn ⊤ Φinf (Gext ·) U`; `.contDiffOn` and
  `.eq_iteratedFDerivWithin_of_uniqueDiffOn` give `ContDiffOn` and `∇ᵤʳΦinf = Gext r`.
- Final `MapCInfConvOnCompacts U`: `iteratedFDerivWithin_sub_apply` + the open-set bridge
  turn the global `mapDerivNorm` into `‖∇ᵤʳ(Φₖ) − Gext r‖` on `K ⊆ U`.

### Lean gotchas (this pass)
- A line starting with `.isometry.uniformContinuous` (leading-dot after a newline) is a
  parse error ("must be atomic"); keep the dot chain attached to the closing paren.
  Naming the curry equiv in a `have` hides it from the `simpa [Function.comp_def]` that
  rewrites `continuousMultilinearCurryLeftEquiv … c` to `c.curryLeft` — keep it inline.
- `Subtype.image_preimage_coe` gives `t ∩ s` = `U ∩ K` (not `K ∩ U`); use
  `Set.inter_eq_right.mpr hKU`.
- `Metric.equicontinuousAt_iff`'s pair is `dist (F x₀) (F x)` and
  `Metric.tendstoUniformlyOn_iff`'s is `dist (limit) (Fₙ)` — both needed `norm_sub_rev`
  / `dist_comm` against the natural orientation.
