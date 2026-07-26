# DeTurckVectorFieldL2JetBound.lean — DLb top-separated producer (in-flight)

## Goal (this dispatch)

The DLb sibling of the DLa half of the deTurckLie coefficient: a **top-separated realizedFam
jetL2** producer, per-order window `Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²) + Kc i·(1+∑_{j<i+3}…)`,
summed over `i<a+1` with both windows `a+3` (via `jetL2_sum_lowShift a 2 3`), mirroring
`deTurckLieDLaCoeffField_realizedFam_jetL2_{perOrder,summed}_topSeparated`
(`DeTurckLieKernelL2JetBound.lean:5680/5966`).

## STRUCTURAL FINDING (planner ruling needed) — endpoint location

The named target `deTurckLieDLbCoeffField_realizedFam_jetL2_*_topSeparated` **cannot be stated in
this file.**  `deTurckLieDLbCoeffField` is defined in `DeTurckLieKernelL2JetBound.lean:60`, which
is a **sibling** of this file (neither imports the other; confirmed by import DAG).  The (2,2)
field↔(1,1)insert **slotInsert bridge** `deTurckLieDLbCoeffField_eq_slotInsert_sum` lives even
further downstream in `DeTurckLieCoeffL2JetBound.lean:47`, which imports BOTH.

Consequently the DLb split is asymmetric to DLa (whose field bound lives in the def file):

- **In THIS file (editable):** the INSERT-level producer
  `deTurckLieWEndoInsert_realizedFam_jetL2_{perOrder,summed}_topSeparated` — the analytic heart,
  upgrading `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform` (:3041).  This is the
  DLb analogue of "kernel-level top separation".
- **Downstream (NOT editable this session), `DeTurckLieCoeffL2JetBound.lean`:** the FIELD lift
  `deTurckLieDLbCoeffField_realizedFam_jetL2_*_topSeparated` — a THIN wrapper, exactly mirroring
  the existing ball-uniform field wrapper `deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_
  ballUniform` (:244): split via `deTurckLieDLbCoeffField_eq_slotInsert_sum` into two
  slotInsert/reindex pieces, each `≤ finrank · ‖∇^i deTurckLieWEndoInsert‖²`
  (`rfns_iteratedCovGrad_dlbSlotZero_le`/`dlbSlotOne_le` + `sq_le_two_add`).  Bounded factor
  `finrank` (g₀-level, R-free) ⟹ field `Ktop = 4·finrank·(insert Ktop)`, still R-free.  ~40–80
  lines, one focused check.  slotInsert/reindex add trivial slots & permute; the top window
  `∇^{i+2}T` is unchanged.

The planner's acceptance №15 located "the DLb sibling producer (`DeTurckVectorFieldL2JetBound.lean`,
near :3041)" — i.e. the INSERT level — but named it `deTurckLieDLbCoeffField_…`.  Resolution: build
the insert-level producer here; the field lift is a separate downstream sibling of the ball-uniform
:244 wrapper.

## DLb tower map + where the top `∇^{i+2}T` enters

`deTurckLieWEndoInsert = slotInsertEndoCc 0 (deTurckLieWEndoSection g₁ g_bg)` (:47), a (1,1) tensor.
`norm_iCG_wEndoInsert_eq_wAlpha` (:2915): `‖∇^i wEndoInsert‖ = ‖∇^i wAlpha‖` (a (0,2) tensor).

`wAlpha = wAlphaA + wAlphaB` (:77):
- **`wAlphaA = domDomCongr(covGrad(wOmega))`** (:64).  `norm_iCG_wAlphaA_eq_succ_wOmega` (:2683):
  `‖∇^i wAlphaA‖ = ‖∇^{i+1} wOmega‖`.  **THIS IS THE TOP ARM** — one covGrad shifts the order up.
- `wAlphaB = appCc(wCA)(wOmega)` (:73).  A two-arm product → all sub-top → Kc.

`wOmega = appCc(cometricCastG0)(wXi)` (:60).  Top cell of `∇^n wOmega` (appCc Leibniz) =
`cometricCastG0(∇⁰) · ∇^n wXi`; `cometricCastG0` order-0 rfns is R-free.

`wXi = connDiffLoweredCc g₁ - connDiffLoweredCc g_bg` (:57).  `connDiffLoweredCc g_bg` is
**T-INDEPENDENT** (fixed metrics) ⟹ its jet is a T-free constant → Kc.  Only `connDiffLoweredCc g₁`
carries T.  `norm_iCG_connDiffLoweredCc_eq_connDiffSection` (:2211): its jet = connDiffSection jet.

`connDiffSection g₁ g₀`: `∇^j` top ~ `∇^{j+1}T` via the top-sep engine (below).

**Top chain (order counts):** wEndoInsert(i) = wAlpha(i) ⊇ wAlphaA(i) = wOmega(i+1) top-cell =
cometricCastG0(0)·wXi(i+1) = connDiffSection(i+1) top ~ `∇^{i+2}T`.  Everything else is sub-top → Kc.
Top window offset `p=2` (∇^{i+2}), matching DLa/arm0.

## Engines / integrator / currency — ALL PUBLIC & REACHABLE (de-risked; no missing API)

- **Head engine** `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
  (`CurvatureCoefficientDifferenceJetTower.lean:1823`): pointwise, separates the leading
  `appCcRS(∇^j raisedKoszul)(sharpFlatEndoCc)` (top ≤ `Ktop·rfns(∇^{j+1}T)`) from the connDiffSection
  remainder (`Kc·∑_k rfns(∇^{j-k}T)·antidiagonalTupleGrid b (k+1)`).  Reachable via
  RemainderCoeffL2JetMoser → RicciArmOrder1KoszulTameEnvelope → JetTower.
- **Data-weighted integrator** `antidiagonalTupleGrid_integral_ballUniform_tameWindow` (JetTower:8556):
  integrand `∑_{n≤i}∑_{e∈antidiagonalTuple n i}∏rfns(∇^{e m}P)` = `antidiagonalTupleGrid (P-rfns) i`
  (def `AntidiagonalTupleProductGrid.lean:13`), bound `≤ K i·(1+∑_{j<i+1}‖∇^jP‖²)`.  This is the
  data-weighted twin of the opaque DLb integrator `diagonalProductGrid_rfns_integral_ballUniform_succ`
  (:951) — SAME integrand, R only in K.  Reachable.  **Key de-risk: the DLb remainder currency IS
  `antidiagonalTupleGrid`, so the SAME currency+integrator as DLa applies.**
- **Public grid API** (`AntidiagonalTupleProductGrid.lean`, low module, in cone):
  `antidiagonalTupleGridWindow b w = ∑_{k<w} antidiagonalTupleGrid b k` (:263, public `dLaGridWin`);
  `single_factor_mul_antidiagonalTupleGrid_le` (:43, `b q·grid b k ≤ grid b (k+q)`, q≥1);
  `antidiagonalTupleGrid_mul_le` (:197); `antidiagonalTupleGrid_le_window` (:276);
  `antidiagonalTupleGridWindow_mono` (:270).  (DLa re-derived these privately as `_dla`; use PUBLIC.)
- **appCc Leibniz grid** `appCc_iteratedCovGrad_diagonalProductGrid_le` (already used at :2781/:2838):
  `rfns(∇^i appCc(S)(T)) ≤ appCcGdiag i · ∑_{n≤i} rfns(∇^n S)·∑_{l≤i-n} rfns(∇^l T)` (two-arm).
- Norm bridges: `norm_iCG_wAlphaA_eq_succ_wOmega`, `norm_iCG_connDiffLoweredCc_eq_connDiffSection`,
  `rfns_iCG_wCA_eq_connDiffSection` (:2624), `norm_iCG_wEndoInsert_eq_wAlpha` (:2915) — all present.
- Summation helpers `sum_shift_le` + `jetL2_sum_lowShift` (private in every sibling; re-derive here,
  pure Finset combinatorics; copy from `DeTurckLieKernelL2JetBound.lean:5627/5645`).

## Route (REVISED — ball-uniform-remainder; the wOmega grid-currency route is NOT needed)

**Key simplification.**  `jetL2_sum_lowShift`'s per-order remainder is `Kc i·(1+∑low)`.  The `Kc i·1`
slot absorbs ANY per-order **ball-uniform (R-dependent opaque) constant** — R is allowed in Kc.  So
the ENTIRE sub-top remainder can be integrated ball-uniformly and dumped into `Kc·1`; only the single
top `∇^{i+2}P` term needs R-free separation.  This AVOIDS the `boundedFactorGridWindow` currency, the
private cometricCastG0 grid bound (`rfns_iteratedCovGrad_cometricCastG0_gridWindow_le`, PRIVATE in
`CurvatureArm1KoszulTopSeparation.lean:35`), and any data-weighted two-arm integrator (none exists).
Everything stays in-file / in the existing ball-uniform machinery.

Work at the **L2 (integrated) level**, carrying `‖∇^{·}·‖²` and one separated top `‖∇^{n+?}P‖²`:

1. `exists_rfns_connDiff_topsep` [BATCH 1, WRITTEN] — connDiffSection POINTWISE top-sep:
   `rfns(∇^j connDiff) ≤ 2Kt0·rfns(∇^{j+1}P) + Kc·antidiagonalTupleGridWindow (bP) (j+2)`.
   Integrate → connDiffSection L2 top-sep: `‖∇^n connDiff‖² ≤ 2Kt0·‖∇^{n+1}P‖² + Ccd n`, with
   `Ccd n = Kc n·∑_{k<n+2}∫antidiagonalTupleGrid` **ball-uniform** via the in-file opaque integrator
   `diagonalProductGrid_rfns_integral_ballUniform_succ` (:951).
2. wXi L2 top-sep — `‖∇^n wXi‖² ≤ 2·2Kt0·‖∇^{n+1}P‖² + Cxi n` (norm-eq `norm_iCG_connDiffLoweredCc_
   eq_connDiffSection`; g_bg part = T-free const; sub-additive triangle).  Cxi ball-uniform.
3. wOmega L2 top-sep — `wOmega = appCc(cometricCastG0)(wXi)`.  `rfns(∇^n wOmega) ≤ appCcGdiag n·G`,
   `G` = the two-arm grid (`appCc_iteratedCovGrad_diagonalProductGrid_le`, :2546).  `∫G = ∫cell(0,n) +
   ∫rest`; `∫cell(0,n) ≤ cΦ0·‖∇^n wXi‖²` (cΦ0 = R-free order-0 cometricCastG0 bound, `cometricCastG0_
   rfns_lowOrder_le` at n=0); `∫rest ≤ ∫G ≤ Crest` **ball-uniform** via the existing two-arm integrator
   `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le` (:2523).  ⟹
   `‖∇^n wOmega‖² ≤ appCcGdiag n·cΦ0·‖∇^n wXi‖² + appCcGdiag n·Crest`.
4. wAlpha L2 top-sep — wAlphaA: `‖∇^i wAlphaA‖² = ‖∇^{i+1}wOmega‖²` (`norm_iCG_wAlphaA_eq_succ_wOmega`)
   ⟹ top `‖∇^{i+2}P‖²`; wAlphaB: `‖∇^i wAlphaB‖² ≤ F_B i` (existing ball-uniform, the wAlphaB arm of
   `wAlpha_order0_jetL2_generic`); `wAlpha = wAlphaA+wAlphaB` triangle (2·+2·).  Then wEndoInsert via
   `norm_iCG_wEndoInsert_eq_wAlpha` (:2915).
5. `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated` — realizedFam wrapper (clone the
   :3041 htie/hPball/hδP plumbing, Pc=convexPerturbation), split top `‖∇^{i+2}Pc‖² ≤ ‖∇^{i+2}T‖²+
   ‖∇^{i+2}T'‖²` (`hwin`), absorb the whole ball-uniform remainder into `Kc i·1` (`Kc i ≥ Crest_i`,
   `1 ≤ 1+∑low`).  Fix `appCcGdiag (i+1) ≤ appCcGdiag (a+1)` (monotone) for a single Ktop.
6. `deTurckLieWEndoInsert_realizedFam_jetL2_summed_topSeparated` — `jetL2_sum_lowShift a 2 3`.

## Constant plan (STRICT: Ktop R-free)

Ktop = `2` (wAlpha) · appCcGdiag(a+1) · cΦ0 · `2` (wXi) · `2Kt0` (connDiff engine head).  All
`(g₀,g_bg,hδ₀,a)`-level: Kt0 (engine, R-free), cΦ0 (cometricCastG0 order-0, R-free since the Λw² power
vanishes at index 0 — same as DLa `CPT0`), finrank via appCcGdiag.  **R-FREE, no top-norm products.**
R lives only in Kc (the ball-uniform Crest/F_B/Ccd constants + integrator K).  Field lift (downstream)
× `4·finrank`, still R-free.

## Honest assessment / status

Route DE-RISKED and SIMPLIFIED (ball-uniform-remainder ⟹ no private arm1 `boundedFactorGridWindow`
machinery, no cometricCastG0 grid bound, no new integrator — all in-file / existing ball-uniform).
No math frontier.  Size now ≈ 300–500 lines (5 L2-chaining lemmas + wrapper + summed), materially
smaller than the grid-currency route.  Batch 1 (connDiff pointwise top-sep + helpers) WRITTEN; pending
first focused check (foreign lean lanes busy at recon time).

`(N) ricci_flow_unif_existence` remains **0%** (DLb half of one of 2 genuinely-missing C₀
constituents; DLa half done).  Field endpoints are the downstream thin wrapper (separate session).

## Batch 2–6 implementation cheat-sheet (exact lemmas; turnkey)

L2-integration idiom (each layer): `normSq_le_integral_of_pointwise_fiberNormSq_le_rs`
(`MetricArmCoeffJetTower.lean:82`) turns a pointwise `rfns(∇^n C) ≤ F x` (F integrable) into
`‖∇^n C‖² ≤ ∫F`.  Then split `∫F` with `MeasureTheory.integral_add`/`integral_const_mul`/
`integral_finset_sum` (all used already in-file at :724/:916/:1106).  `∫rfns(∇^k P) = ‖∇^k P‖²` via
`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs` (:46 same file, inside
`SmoothCcTensor.norm_def`).  Integrability of `rfns(∇^k C)`: `integrable_riemannianFiberNormSq_
toSection` (`L2/MultiplicationOperator.lean:124`).

`connDiff_L2_topsep` (batch 2): integrate `exists_rfns_connDiff_topsep` (batch 1).
- Grid remainder currency: `antidiagonalTupleGridWindow (bP x) (n+2)` = `∑_{k<n+2} antidiagonalTupleGrid
  (bP x) k` (def :263), `bP x l = rfns(∇^l P) x`.
- Integrate each `antidiagonalTupleGrid (bP x) k` via `antidiagonalTupleGrid_integral_ballUniform_
  tameWindow` (JetTower:8556).  **DEFEQ BRIDGE**: `:8556`'s integrand is the explicit
  `∑ n∈range(k+1), ∑ e∈antidiagonalTuple n k, ∏ m, rfns(∇^{e m}P)`, which is DEFEQ to
  `Combinatorics.antidiagonalTupleGrid (bP x) k` (grid def + bP β-reduction).  `exact`/`le_trans`
  bridges it (grid is a semireducible `def`); if unification is slow, `show`/`simp only
  [Combinatorics.antidiagonalTupleGrid]` first.
- `:8556` bound `≤ K k·(1+∑_{j<k+1}‖∇^jP‖²)`; convert to ball-uniform `≤ K k·(1+(k+1)R²)` via
  `∑_{j<k+1}‖∇^jP‖² ≤ (k+1)R²` (each `‖∇^jP‖²≤R²` from hPball for `j≤k≤a+2`, `nlinarith`).  So
  `C n = Kc_pt n·∑_{k<n+2} K k·(1+(k+1)R²)`.  Index OK: `n≤a+1 ⟹ k≤n+1≤a+2` (hPball reach).
- Ktop = Ktop_pt (= 2Kt0), R-free.

`wXi_L2_topsep` (batch 2b): `‖∇^n wXi‖² ≤ 2‖∇^n connDiffLoweredCc g₁‖² + 2‖∇^n connDiffLoweredCc g_bg‖²`
(`iteratedCovGrad_sub` + `norm_sub_le` squared, `nlinarith`).  `‖∇^n connDiffLoweredCc g₁‖² =
‖∇^n connDiffSection g₁ g₀‖²` (`norm_iCG_connDiffLoweredCc_eq_connDiffSection` :2211) → connDiff_L2_topsep.
g_bg term: T-free const via `exists_bound_riemannianFiberNormSq_smoothCcTensor` / its norm² (as in
`wXi_lowOrder_jetL2_succ_generic` :2254 FBg).  Ktop = 2·(connDiff Ktop).

`wOmega_L2_topsep` (batch 3): `‖∇^n wOmega‖² ≤ ∫ appCcGdiag n·G` (`normSq_le_integral...` +
`appCc_iteratedCovGrad_diagonalProductGrid_le` :2546, `integral_const_mul`).  `∫G = ∫cell(0,n) + ∫rest`
where cell(0,n)=`rfns(∇⁰cometricCastG0)·rfns(∇^n wXi)`.  `∫cell ≤ cΦ0·‖∇^n wXi‖²` (cΦ0 = R-free
order-0 `cometricCastG0_rfns_lowOrder_le` :2331 at n=0 — R-free since Gw's Λw²-power vanishes at 0,
same as `wAlpha_order0_jetL2_generic` uses ΛO 0).  `∫rest ≤ ∫G ≤ Crest` ball-uniform via the two-arm
integrator `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
(`RemainderCoeffPerOrderJetEnvelopes.lean:870`, the `hCT` of :2523; ΛS'=ΛCsup for cometricCastG0,
ΛT'=√(ΛX 0) for wXi — mirror :2587).  Then `‖∇^n wXi‖²` → wXi_L2_topsep.  Ktop = appCcGdiag·cΦ0·(wXi Ktop).

`wAlpha_L2_topsep` (batch 4): `‖∇^i wAlphaA‖² = ‖∇^{i+1}wOmega‖²` (`norm_iCG_wAlphaA_eq_succ_wOmega`
:2683) → wOmega_L2_topsep at n=i+1, top `‖∇^{i+2}P‖²`; `‖∇^i wAlphaB‖² ≤ F_B i` — reuse the wAlphaB
arm of `wAlpha_order0_jetL2_generic` (:2804 `hBsum`); `wAlpha=wAlphaA+wAlphaB` triangle (`2·+2·`,
`nlinarith` as :2895).  wEndoInsert via `norm_iCG_wEndoInsert_eq_wAlpha` (:2915).

Endpoint (batch 5/6): mirror the ball-uniform `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_
ballUniform` (:3041) htie/hδP/hPball/hwin plumbing; split top `‖∇^{i+2}Pc‖²≤‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²`
(`hwin`); absorb ball-uniform C into `Kc i·1`; fix `appCcGdiag(i+1)≤appCcGdiag(a+1)` for single Ktop;
`jetL2_sum_lowShift a 2 3`.

## CORRECTION to the ball-uniform route (wOmega layer needs a GENUINE top-cell extraction)

The "absorb the whole sub-top remainder into `Kc·1`" idea is right for the ball-uniform *remainder*,
but the wOmega top itself must still be peeled EXACTLY.  Reason: if the wOmega two-arm rest is bounded
by the FULL-grid ball-uniform integrator (which includes the top cell), then `∫G = ∫cell + ∫rest`
with `∫rest ≤ ∫G ≤ Crest` collapses to `∫G ≤ Crest` (Ktop = 0) — a spurious separation.  For a
POSITIVE `R`-free Ktop the rest must bound only the cells EXCLUDING the `(i'=0,l=n)` top cell.  So
wOmega needs the DLa-style corner peel, not an over-count.

**wOmega recipe (refined).** Use the argCorner covariant-Leibniz decomposition
`iteratedCovGrad_appCcRS_eq_argCorner_add_lower` (`OperatorFieldFibreNormJet.lean:1410`):
`∇^i(appCcRS Θ X) = appCcRS(appCcLeibnizPsi Θ i i)(∇^i X) + ∑_{k<i}appCcRS(appCcLeibnizPsi Θ i k)(∇^k X)`
— the CORNER term carries `∇^i X` (X fully differentiated = the top), the lower sum has `∇^k X`, k<i
(sub-top).  For `wOmega = appCc(cometricCastG0)(wXi)`: corner op norm on the coefficient is R-free
order-0 (`cometricCastG0_rfns_lowOrder_le` at 0), corner arg `∇^n wXi` → `wXi_L2_topsep` (top
`‖∇^{n+1}P‖²`); the lower sum bounds ball-uniformly via `rfns_iteratedCovGrad_appCc_coeffLower_le`
(`OperatorFieldFibreNormJet.lean:1372`) + the existing cometricCastG0/wXi ball-uniform jet bounds,
then integrate → `Crest` (ball-uniform, TOP-FREE).  [First check the `appCc`↔`appCcRS` bridge for
wOmega's exact `appCc g₀ 3 1` shape; the DLa piece-4 `gridSplit_dla`/`appCcGrid_le_dla`
(`DeTurckLieKernelL2JetBound.lean`, private) is the appCcRS template.]  Ktop = appCcGdiag(a+1)·cΦ0·
(wXi Ktop), keep `appCcGdiag n` explicit in the statement and collapse `appCcGdiag n ≤ appCcGdiag(a+1)`
at the wrapper.

## Progress log
- 2026-07-24 recon complete; route de-risked + SIMPLIFIED (ball-uniform remainder), then CORRECTED
  (wOmega needs genuine corner peel — see above).  **VERIFIED GREEN (3 of ~6 tower layers):**
  batch 1 `exists_rfns_connDiff_topsep` (+ `engineRem_le_grid`, `sum_shift_le`, `jetL2_sum_lowShift`),
  batch 2 `connDiff_L2_topsep` (connDiffSection L2 top-sep; the crux L2-integration idiom PROVEN —
  `normSq_le_integral_...` + tame-window integrator + `hPball` (k+1)R² conversion), batch 2b
  `wXi_L2_topsep`.  All in `section DLbTopSeparated`; whole-file `lake env lean` EXIT=0, zero errors,
  zero new warnings (live check — pre-existing warnings still emitted, so not cached-stale).  Fixes
  in this session: `Nat.cast_add/cast_one` on a `sum_const` step; `add_le_add_left`→`linarith`;
  `by positivity`→explicit `mul_nonneg/add_nonneg` (positivity ignores the opaque `Ktop_cd`/`C_cd`
  hyps).  **REMAINING (multi-session):** batch 3 wOmega_L2 (corner peel, the crux — recipe above),
  batch 4 wAlpha_L2 (`norm_iCG_wAlphaA_eq_succ_wOmega` + wAlphaB ball-uniform + triangle), batch 5
  perOrder endpoint `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated`, batch 6 summed
  `..._summed_topSeparated` (`jetL2_sum_lowShift a 2 3`), then the DOWNSTREAM field wrapper in
  `DeTurckLieCoeffL2JetBound.lean`.  `(N)` still 0%.
- 2026-07-24 (session 2) **BATCHES 3–6 COMPLETE + VERIFIED GREEN** (whole-file `lake env lean`
  EXIT=0, zero errors, zero NEW warnings; only pre-existing unusedSectionVars warnings, all at
  lines < 3500).  All four insert-level lemmas landed in `section DLbTopSeparated`:
  - batch 3 `wOmega_L2_topsep` — the crux corner peel.  Route CHANGED from the `.md` recipe: the
    corner coefficient carries NO `appCcGdiag`.  Used PUBLIC unconditional
    `rfns_appCcRS_appCcLeibnizPsi_diag_le` (`OperatorFieldFibreNormJet.lean:1728`) for the corner
    `rfns(appCcRS ψ_{n,n}(∇ⁿwXi)) ≤ rfns(cometricCastG0)·rfns(∇ⁿwXi)`, with `rfns(cometricCastG0) ≤
    ΛClow 0` (`cometricCastG0_rfns_lowOrder_le` at 0, `R`-free).  Lower sum via
    `rfns_appCcRS_argLower_le` (:1426) → antidiagonal ≤ two-arm triangular grid (Finset
    `sum_range_reflect`+`sum_range_succ'` reindex) → `exists_integrated_…_twoArm_rs_le` (S=cometricCastG0
    3 1, T=wXi 0 3).  **`Ktop = 2·ΛClow 0·Ktop_xi`, `R`-free, NO `appCcGdiag`** (cleaner than the
    planned `appCcGdiag(a+1)` collapse; RULING 2 satisfied — Ktop genuinely positive).  ~155 lines.
  - batch 4 `wAlpha_L2_topsep` — wAlphaA arm = `‖∇^{i+1}wOmega‖²` top-sep at `n=i+1` (top
    `‖∇^{i+2}P‖²`); wAlphaB arm reconstructs the `hBsum` two-arm block from
    `wAlpha_order0_jetL2_generic` (top-free, ball-uniform).  `Ktop = 2·Ktop_om`.
  - batch 5 `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated` — clones the ballUniform
    insert plumbing (:3041; htie/hδP/hPball/empty-M) + `hwin` top-split (`‖∇^{i+2}Pc‖²≤‖∇T‖²+‖∇T'‖²`)
    + `norm_iCG_wEndoInsert_eq_wAlpha`; absorbs C into `Kc i·1`.  `Ktop = Ktop_a`.
  - batch 6 `..._summed_topSeparated` — `jetL2_sum_lowShift a 2 3`, both windows `a+3`.
  SHAPES match the DLa siblings (`DeTurckLieKernelL2JetBound.lean:5680/5966`); quantifier order
  s-before-i.  **Field wrapper** (`DeTurckLieCoeffL2JetBound.lean`): `normSq_iCG_dlbField_le`
  (generic-g₁ `×4·finrank` per-order helper via `deTurckLieDLbCoeffField_eq_slotInsert_sum` +
  `rfns_iteratedCovGrad_dlbSlotZero_le`/`dlbSlotOne_le` + `sq_le_two_add`) + the two field
  endpoints; the summed field wrapper avoids the private `jetL2_sum_lowShift` by summing the helper
  against the insert-summed bound.  Field `Ktop = 4·finrank·Ktop_insert`, `R`-free.  Wrapper-file
  check + 4-endpoint axiom audit pending an olean refresh (the vector-field module is a heavy
  build).  `(N)` still 0% (DLb half of one C₀ constituent now built; assembly not started per
  session scope).
