# Lane H6 log: history index form, second variation, nonnegativity, non-conjugacy (DESIGN_22 §4, brick H6)

- 2026-09-26 start. Target file `Surgery/Topology/HistoryLGeometry/Index.lean` (one new file).
  Inputs read: AGENTS.md, NAMING.md §2–6, DESIGN_22 §0–§4/§7 (row H6), H1 `Window.lean`
  (`LWindow`, `restrict`, `exists_splice`, `lRegularizedAction_le_of_regularizedCost_eq`,
  split at parameter), H2b `Seam.lean`, H3a `Exponential.lean` (`IsHistoryLGeodesicOn`,
  `HasHistoryLInitialVector`), H5 log/`Truncation.lean`, G4 `Index/JacobiMinimality.lean`,
  G5 `Jacobian/GramIndexBound.lean`, `Index/{Regularized,Algebra,MinimizerNonnegativity,
  PiecewiseNonnegativity}.lean`, `Variation/Field/{Realization,PairRealization}.lean`.
- G5's abstract axioms (quoted, `trace_inv_gram_mul_boundary_le_sum_index`,
  `half_trace_inv_gram_mul_gramDeriv_le_sum_index`), for `Q : V → V → ℝ`, `A : Submodule ℝ V`,
  `eva : V →ₗ[ℝ] Fa`, `evb : V →ₗ[ℝ] F`:
  (α) `hadd : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Q (x + y) z = Q x z + Q y z`,
      `hsmul : ∀ c : ℝ, ∀ x ∈ A, ∀ z ∈ A, Q (c • x) z = c * Q x z`,
      `hsymm : ∀ x ∈ A, ∀ y ∈ A, Q x y = Q y x`;
  (β) `hbdry : ∀ i, ∀ x ∈ A, Q (J i) x = (1 / 2) * (Nb i (evb x) - Na i (eva x))`;
  (γ) `hnonneg : ∀ x ∈ A, eva x = 0 → evb x = 0 → 0 ≤ Q x x`.
- DESIGN_22 §7 rows quoted: "H6 | History index form; second variation; nonnegativity;
  non-conjugacy | `…/Index` | history | 1500 | H1, H5, G4"; "H7a | `historyReducedJacobian`; seam
  continuity | `…/Jacobian` | history | 900 | H3b, G2"; "H7b | Window derivative inequality;
  `historyReducedJacobian_antitoneOn` | `…/JacobianMonotone` | history | 1400 | H6, H7a, G5".
- Compile route: reuse the H3a/H4/H5 scratch build (`scratchpad\h3a`, modules `H3aPre.*`); the
  scratch copies of Window/Regularity/Seam/Exponential/MinDomain are identical to the repo files
  up to renamed imports (checked by diff); `H3aPre.Truncation` is built from the repo
  `Truncation.lean` with only its import renamed.
- Progress 1 (scratch `h6/Index.lean`, compiles clean): design decision — the history index is
  defined for a FIXED window chain along `α` (DESIGN allows it; cover-independence not proved).
  `LWindowChain T v α` (ℕ-indexed): breakpoints `0 = c 0 < … < c n = v`, windows `W k` with lifts
  `γ k` (globally smooth, `IsLRegularizedGeodesicOn` on an open interval around the closed piece,
  `W k).f j ∘ γ k = α j` on the stage pieces), a stage `stage m` at every breakpoint
  (`stage 0 = last`, `stage n = first`), interior breakpoints in the OPEN stage pieces of both
  neighbouring windows (so the window metrics there are `localPullMetric`s of one stage metric).
  Fields along the chain: `Field := (k : ℕ) → (s : ℝ) → TangentSpace ThreeModel (γ k s)`;
  `IsGlued` = stage differentials agree at interior breakpoints; `IsHistoryLJacobi` = Jacobi on each
  piece + values and covariant derivatives glued. Proved: `historyLIndex_symm/_smul/_add` (α),
  `historyLIndex_eq_half_boundary` (β: interior boundary terms cancel by `localPullMetric_inner`),
  span closure lemmas, and `trace_inv_gram_mul_boundaryForm_le_sum_historyLIndex` = G5's abstract
  theorem instantiated with `Q = historyLIndex`, `eva = evalAt 0 0`, `evb = evalAt (n-1) v`,
  `hnonneg` required only on `span (range J ∪ range Y)`. Two single-flow span helpers are private
  in `GramIndexBound.lean`; copied privately (follow-up: make them public there).
- Progress 2 (scratch, compiles clean, ~880 lines): the history second variation.
  Chain refactor: `stage m` at every breakpoint with `stage 0 = last`, `stage n = first`; derived
  `stage_succ_le`, window pieces restricted to `[c k, c (k+1)]` (`restrictPiece`). Proved:
  `sum_mem_regularizedActionValues` (window pieces of C¹ curves matching at the breakpoints form
  a history competitor, induction with `mem_regularizedActionValues_split_at_parameter`),
  `regularizedExtendedAction_eq_sum` (history action of α = Σ window actions of the lifts, induction
  with `regularizedExtendedAction_eq_add_at_parameter` + `regularizedExtendedAction_eq_coe`),
  HEq transports to `first`/`last`/`0`/`v`, `boundaryAccel_node` (the moving-endpoint boundary
  terms ⟨∇_u∂_u f, γ'⟩ cancel at interior breakpoints: `mfderiv_covDerivAlong_of_isLocalDiffeomorph`
  + `covDerivAlong_congr_curve` + `localPullMetric_inner`), and
  `historyLIndex_nonneg_of_variation`: for a regular minimizer α (hmin), window-wise smooth
  variations `f k` of the lifts that match through the stage maps at the breakpoints for small `u`
  and fix both ends, `0 ≤ historyLIndex V V` with `V = ∂_u f|₀`
  (sum of `lRegularizedAction_second_variation_moving_endpoints`, `second_deriv_nonneg_of_isLocalMin`).
  Next: realization — construct such matching variations for any smooth glued field (chart
  correction of `exists_var_pair` near the breakpoints).
- Progress 3 (scratch, compiles clean, ~1290 lines): (3) nonnegativity proved unconditionally for
  C⁸ glued fields. Realization of matching variations: generic chart-correction lemma
  `Variation.exists_isSmoothVariation_eq_curve` (modify a smooth variation near `s = c` inside one
  extended chart with bumps `ρ(s)ψ(u)` so that its `c`-curve becomes a prescribed smooth curve with
  the same initial point/velocity, keeping `f 0` and the variation field), then per window:
  `exists_var_pair` + correction at the left breakpoint to the lift
  `invFun F₂ ∘ F₁ ∘ f_{k}(·, c)` of the previous window's breakpoint curve
  (`exists_first_variation`, `exists_next_variation`, induction `exists_glued_variation`).
  Headline `LWindowChain.historyLIndex_nonneg`: regular minimizer α (hmin), chain on `[0, v]`,
  V glued, C⁸ on each piece, `V 0 0 = 0`, `V (n-1) v = 0` ⇒ `0 ≤ historyLIndex V V`.
- Owner directive received (no line cap, more files allowed, deliver all four unconditionally).
- Progress 4 (scratch, compiles clean, ~1790 lines): (4) non-conjugacy proved.
  Refactor: `GluedAt` (one breakpoint), partial boundary identity
  `sum_range_lRegularizedIndex_eq_half_boundary` (any `m ≤ n`), full (β) derived from it.
  `exists_testField` (smooth glued test field supported on the two pieces around a breakpoint,
  prescribed value `P` there; from `exists_contMDiff_vectorFieldAlong_zero_endpoints` and the
  inverse stage differential), `covDerivField_eq_zero_of_conjugate` (broken field `X = J` on pieces
  `≤ k₀`, `0` after; `I(X,X) = 0`, `I(X,W) = ½|∇J(v₁)|²`, nonnegativity of `I(X+εW, X+εW)` for all
  ε forces `∇J(v₁) = 0`), `exists_eqOn_zero_of_isLRegularizedJacobi` (ODE uniqueness
  `lRegularizedJacobi_unique` on an open interval), `eqOn_zero_of_conjugate`: a smooth glued history
  L-Jacobi field on pieces `≤ k₀` with `J 0 0 = 0`, `J k₀ (c (k₀+1)) = 0` vanishes on all those
  pieces, when α minimizes on the whole chain `[0, v]` and `k₀ + 1 < n` (so `v₁ = c (k₀+1) < v`).
  Next: chain existence along a regular minimizer (the cover "attached to the geodesic").
- Progress 5 (scratch, both files compile clean): chain existence in a second file
  `HistoryLGeometry/IndexChain.lean` (owner allowed more files). `exists_lWindowChain`: for a
  history L-geodesic α on `(0, v₂)` with initial vector (H3a data), `T ∈ stageDomain last`,
  `0 < v < v₂` with `T - v²` interior to a stage `fst ≥ first`, and a prescribed non-seam
  `w ∈ (0, v)`, there is an `LWindowChain` on `[0, v]` along the truncation of α with `w` among the
  breakpoints. Proof: Lebesgue number of the cover by window ranges (initial window at 0), a
  partition with mesh below it avoiding the finite seam set and containing `w`
  (`exists_segment_partition`, `exists_partition_of_cover`), per piece the window restricted to a
  slightly larger interval with stages from `activeStage`, the lift replaced by a globally smooth
  curve equal to it near the piece (`exists_contMDiff_eqOn`, bump reparametrisation).
  Corollaries for regular minimizers up to `v₂` and any chain on `[0, v]`, `v ≤ v₂` (H5 truncation):
  `LWindowChain.historyLIndex_nonneg_of_minimizer`, `LWindowChain.eqOn_zero_of_conjugate_of_minimizer`.
- Final (2026-09-26): `Surgery/Topology/HistoryLGeometry/Index.lean` (1792 lines) and
  `Surgery/Topology/HistoryLGeometry/IndexChain.lean` (609 lines). Neither contains sorry, nolint,
  heartbeat or synth overrides, comments or docstrings. Lines are ≤ 100 characters (imports
  excepted), and the only option set is `set_option autoImplicit false`. No other repo edits, no git
  writes. The files are NOT registered in the root aggregate: register `Index` and then `IndexChain`
  after `Truncation`.
- Compile: the scratch copies are identical to the repo files except for renamed imports
  (`H3aPre.Truncation`, `H3aPre.Index`; checked by diff). Both compile with
  `LEAN_NUM_THREADS=2 lean` against the `scratchpad\h3a` oleans and give no errors, warnings or
  infos. `linter.mathlibStandardSet` plus `#lint`:
  - `IndexChain`: all checks pass.
  - `Index`: only `docBlame`, on 21 defs. Per AGENTS that linter does not apply here, because the
    repo forbids declaration docstrings.
  Every headline depends only on propext, Classical.choice and Quot.sound.
- Open or not proved:
  - The index is not proved independent of the chosen window chain.
  - Chain breakpoints (and the chain end `v`) must be at non-seam parameters. So non-conjugacy is
    proved at non-seam `v₁` only.
  - Existence needs `T ∈ stageDomain last`.
  - The single-flow span helpers were copied privately; making them public in `GramIndexBound.lean`
    is a follow-up.
