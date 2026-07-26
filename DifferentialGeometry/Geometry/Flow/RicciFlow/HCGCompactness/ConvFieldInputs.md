# ConvFieldInputs.lean — Brick 7a of the P4 conv engine

**Goal.** Produce, verbatim, the five cited inputs carried by Bricks 4–5
(`ConvFieldAssembly.lean` / `ConvFieldMain.lean`) from honest THEOREM-LEVEL inputs stated
against general comparison maps `Φ : PointedCGHMaps X L subseq` (ruling 5b; instantiate
`Φ := pointedCGHMaps_of_atZero X L subseq rmaps` at 7b).

**Status: DONE (2026-07-04).** Targeted build green (3916 jobs); all six checked endpoints
(`hbound_of_equiv`, `covTail_of_bounds`, `lipTail_of_src`, `lipSrc_of_soln`, `conv0_of_cp`,
`covNorm_self_succ`) axiom-clean `[propext, Classical.choice, Quot.sound]`, no sorries.
**Verbatim-pluggability was elaboration-checked**: a temporary example instantiated
`convOut` with all four producers (with `cLow := (Crel·Bmax)⁻¹`) and `gInf_zero_eq` with
`conv0_of_cp`'s output — both elaborated, then the example section was removed.

## The five producers and their theorem-level inputs

1. **`hbound_of_equiv`** (→ `hbound` of `hlow_gSeqExt`/`convOut`, with
   `cLow := (Crel * Bmax)⁻¹`). Inputs:
   - `hequivT` — per-`k` window equivalence `MetricUniformEquivalentOnWindow (Φ.target k)
     β ψ (gRefT k) (fun _ t => g_k(t)) B` on the k-th manifolds with ONE majorant `B`
     (+ `hBmax : B t ≤ Bmax`). This is the book's eq-(3.3)-side citation (whole-manifold,
     restricted to the target by `mono` at 7b); at 7b take `gRefT k := g_k(0)`.
   - `hrel` — ONE constant `Crel ≥ 1` with `MetricUniformEquivalentOn univ (refRes k)
     (tgtRefSrc k) Crel` per `k`, where `tgtRefSrc` (new def) = restrict-then-pullback of
     `gRefT k` mirroring `sourceFlow`. The "reference relation" the plan anticipated.
   Route: `metricUniformEquivalentOnWindow_restrictOpen` ∘ `_pullback` (constants
   unchanged; the pulled-back sequence is DEFEQ to `srcMetric` — no bridge lemma needed)
   ∘ new `equivOn_trans` (constants multiply). `hcLow : 0 < (Crel*Bmax)⁻¹` is
   `inv_pos.2 (by nlinarith)` at the call site.

2. **`covTail_of_bounds`** (→ `hcovTail` of `hbdd_gSeqExt`/`convOut`). Input:
   - `hcovSrc` — for every order `j`, one constant bounding
     `metricCovDerivNorm j (srcMetric k t) (refRes k)` over all `k`, all window
     times, and source-domain points lying over `bf.grow k`.
   Route: `BumpFamily.chi_one` supplies an open neighborhood on which the bump
   extension is exactly the source metric.  Restriction locality transfers the
   covariant tower with the same constant.  No bump-derivative estimate or
   collar split remains.

3. **`lipTail_of_src`** (→ `hlipTail` of `hgLip_gSeqExt`/`convOut`). Input:
   - `hlipG` — ∀ budget `p` ONE constant `Lt` with the source-granularity window
     Lipschitz bound `metricDerivNorm a (srcMetric k s) (srcMetric k t) (refRes k) y ≤
     Lt·|s−t|` (`a ≤ p`) over ALL `k` and all source-domain points over `bf.grow k`
     (the agreement diagonal).
   Route: pure locality with the SAME constant — `metricDerivNorm_restrictOpen` twice
   (L.M → SourceDomain → the `chi_one` sub-open `O`), swap both slots at once with the
   NEW `derivNorm_congr_diff` (the seminorm depends on the pair only through the
   difference of `metricTensorField`s; on `O` the bump is 1 so the differences agree),
   restrict back.

4. **`lipSrc_of_soln`** (→ `hlipSrc` of `hgLip_gSeqExt`/`convOut`). **Fully produced —
   no Lipschitz citation.** Inputs: `hβψ`, `hwin : Icc β ψ ⊆ X.D.regular`, the
   equivalence inputs (`hequivT`/`hrel` + `hBmax1`), and
   - `hShiT` — ∀ budget `N` ∃ `KShi ≥ 0` with the target-side `MovingShiBoundOn
     (Φ.target k) β ψ … N KShi` for all `k` (the book's Shi citation; ONE constant per
     order budget).
   Route per `k`: `hgLip0Sol` + `hgLipFinSol` on `sourceFlow Φ k` (Brick 2), with:
   equivalence = `srcEquivOn` (window form on `univ`); Shi = `srcShi`
   (`movingShiBoundOn_restrictOpen` ∘ `_pullback`, constants unchanged); swap =
   `solnTowerSwap_reg` on `sourceFlow`'s own `IsSolutionOn` (`hDreg` free from
   `RealTimeInterval.regular_isOpen`); the `SolLipData` pack per order `a` from
   `covOrderBound_of_soln` on nested compact-closure neighborhoods
   `C ⊆ U₁ ⊆ closure U₁ ⊆ U₂ ⊆ closure U₂` (Mathlib
   `exists_isOpen_superset_and_isCompact_closure`, `LocallyCompactSpace` via the
   `ChartedSpace.locallyCompactSpace` idiom), with per-`k` initial covariant bounds at
   `t0 := β` from `metricCovDerivNorm_bddOn` on `closure U₂`.

5. **`conv0_of_cp`** (→ `hconv0` of `gInf_zero_eq`). Input:
   - `hcp` — `MetricSourceCPConvOn`-shaped time-0 convergence at order 0 against the
     canonical slots: `∀ K compact ∀ ε>0 ∃k0 ∀k≥k0, K ⊆ Φ.source k ∧
     metricDerivNormSupOn (sourceCompactSet Φ k K) 0 (srcMetric k 0) (resSrc g0)
     (refRes k) < ε` (7b discharger: `mc.convergence`).
   Route: singleton compact `{x}` (`sourceCompactSet Φ k {x} = {⟨x,hx⟩}` by
   `Subtype.ext`), `derivNorm_le_sup_sing` on the source domain, then
   `metricInnerApply_diff_le` with the `refRes`/`resSrc` inner values reduced to
   `R`/`g0` by `rfl`; the ε-arithmetic mirrors `gInf_zero_eq`'s T1 block
   (`n := finrank ℝ E`; the source-domain finrank bridges by `norm_cast` defeq).

## New reusable prelims (general fixed manifold)

- `equivOn_trans` — `MetricUniformEquivalentOn` transitivity, constants multiply.
- `covNorm_le_add` — reverse triangle `|∇^a g| ≤ |∇^a h| + |∇^a(g−h)|`
  (via `sqrtNormSq0S_add_le` + `sub_add_cancel`).
- `covNorm0_le` — EXPLICIT-constant order-0 bound `|h|_gRef ≤ C·√(finrank ℝ E)` from a
  pointwise two-sided pair (covZeroBdd's proof, constant exposed).
- `covDeriv_self_one`/`covDeriv_self_succ`/`covNorm_self_succ` — **metric compatibility
  at the `covDerivOfField` level**: `metricCovDeriv g g (a+1) = 0` and its norm form.
  Built from `Tensor0SBundle.nabla_metric_zero` +
  `leviCivitaConnectionOfMetric_isMetricCompatible` + `metricCovDeriv_one_apply_section`
  (first step; slot-realization via `ContMDiffSection.exists_eq_at_gen` +
  `Fin.cons_self_tail`) and `metricCovDerivStep_smul` at `c := 0` (higher steps).
  These + `derivNorm_congr_diff` are relocation candidates for
  `MetricCovDerivLinear.lean` / `PointedConvergence.lean`; kept here per the mid-phase
  import-freeze convention (same reasoning as ConvFieldMain's congr lemmas).
- `derivNorm_congr_diff` — the seminorm depends on `(g₁,g₂)` only through
  `mtf g₁ − mtf g₂` (via `covDerivOfField_sub`).
- `mtf_eq_mt0S` (private) — pointwise `metricTensorField = metricTensor0S`.

## Honesty ledger (what remains cited, and why)

- **`hequivT`, `hShiT`**: the book-cited eq-(3.3) window equivalence and Shi bounds for
  the sequence flows, with uniform constants — exactly the plan's intended citations.
- **`hrel`**: uniform whole-source-domain comparability of the transported per-`k`
  reference with `refRes`. With `gRefT k := g_k(0)`, `R := mc.limit` metric this is
  "the time-0 pullbacks are uniformly comparable to the limit metric on their whole
  source domains". `mc.convergence` gives this only per-compact-eventually; the
  whole-domain uniform version is a genuine extra citation (Thm 3.9's construction
  provides it morally — the comparison maps are built from convergent normal-coordinate
  data — but the formalized 3.9 conclusion does not carry an equivalence field).
- **`hcovSrc`, `hlipG`**: uniform-in-`k` source-side covariant/Lipschitz bounds on the
  `bf.grow` agreement diagonal. NOT producible from the in-tree per-`k` machinery:
  `covOrderBound_of_soln`/`hgLipFinSol` hide their constants behind `∃`/`Classical.choose`
  (verified — `hgLip_orderN_of_solutions` exposes no constant), so per-`k` runs cannot
  yield ONE constant over the exhausting diagonal. The uniform statements are the
  eq-(3.4)-side citations with uniform inputs; `lipSrc_of_soln` demonstrates the same
  shape IS produced per-`k`.  The constants-first replacement is now stated as
  `SrcCovLipData` / `srcCovLip_of_soln` in `SourceCovLip.lean`.
- **`hchi` (resolved 2026-07-18)**: the carried bump-tower input was artificial.
  `hcovTail` and its consumer now work directly on `bf.grow k`, where the bump
  is one on an open neighborhood.  The collar estimate and `hchi` were deleted.
- **`hcp`**: `mc.convergence`-shaped. CAUTION for 7b: `MetricCGConvergenceData.domain`
  is an ABSTRACT `MetricSourceData` field of the (sorry'd) Thm 3.9 conclusion; the
  discharge needs the noted "atZero field-defeq identification" — i.e. 3.9's statement
  may need pinning to `ofRestrictPullback` data for the identification to be `rfl`-like.
- Window bookkeeping inputs: `hβψ`, `hwin : Icc β ψ ⊆ X.D.regular`, `hBmax`, `hCrel1`,
  `hBmax1` (`hDreg` was NOT needed — `RealTimeInterval.regular_isOpen` supplies it).

## Route notes / gotchas

- The transported window equivalence lands on `srcMetric` **definitionally** (both are
  `pullbackMetric ((g_k t).restrictOpen targetOpen) sourceTargetDiff` — Brick 2's
  `sourceFlow_metric_eq` is `rfl`), so no slot-bridge lemma was needed anywhere; `exact`
  crossed the defeq under the file-wide `respectTransparency false`.
- Instance discipline: every per-`k` hypothesis/conclusion carries its own letI preamble;
  `MovingShiBoundOn` needs `SigmaCompactSpace` in scope (first-compile failure),
  `MetricUniformEquivalentOn` does not. The `SourceDomain Φ k` vs `↥(sourceOpen Φ k)`
  gap is handled by registering both spellings (the Brick-4 idiom); `refRes`/`resSrc`
  inner values reduce by `rfl`.
- `Fin`-vs-real lemma renames: `inv_le_inv_of_le` is gone — use
  `simpa [one_div] using one_div_le_one_div_of_le` (the `metricUniformEquivalentOn_of_le`
  idiom).
- The `nlinarith` convex-combination goals need the two product hints
  `(1−χ)·r·(1−C⁻¹) ≥ 0` / `(1−χ)·r·(C−1) ≥ 0` spelled out.
- The `show`-tactic style lint fires on goal-changing `show`s — use `change`.
- `maxHeartbeats` raised (1.0–1.6M) on `extEquivOn`/`covTail_of_bounds`/`lipSrc_of_soln`
  (deep instance terms; comfortable margins at 6 threads).
- Verification protocol followed: temporary `#print axioms` written BOM-safely (python
  io, not PS5.1 `-Encoding utf8`), read from the BUILD output (`lake env lean` suppresses
  them), removed, rebuilt green.

## 7b handoff

- Instantiate `Φ := pointedCGHMaps_of_atZero X L subseq rmaps` after `cases hL0`;
  all five producers are stated for general `Φ`, defeq-instantiable.
- `convOut` call shape (elaboration-tested): `cLow := (Crel*Bmax)⁻¹`,
  `hcLow := inv_pos.2 (by nlinarith)`, then the four producers verbatim;
  `gInf_zero_eq` takes `conv0_of_cp` verbatim.
- `covTail_of_bounds` is wired directly from the grow-local source bound; there
  is no `hchi` argument or bump-collar frontier.

## 2026-07-17 exact-refresh repair

- Focused verification and the exact named module refresh both pass.
- Three obsolete `simp only` normalizations in `lipTail_of_src` and
  `covTail_of_bounds` had become no-ops after the tensor-metric normal form
  refresh.  Each was replaced by an explicit `change` to the corresponding
  metric-inner equation before applying the existing `gSeqExt_inner_*` rewrite.
- No theorem statement, hypothesis, API, or mathematical route changed.  The
  six producer endpoints remain complete; this was verification maintenance,
  so the theorem and whole-project progress estimates are unchanged.

## 2026-07-18 grow-local `covTail_of_bounds`

`covTail_of_bounds` now consumes a source-flow covariant bound only on
`bf.grow k` and proves the matching grow-local bound for `gSeqExt`. On the
open neighborhood supplied by `BumpFamily.chi_one`, the two metric tensor
fields agree, so restriction locality transfers the whole covariant tower with
the same constant. The whole-source collar split, uniform bump-derivative
input, and `hchi` frontier were deleted. Focused verification and the exact
module refresh pass.
