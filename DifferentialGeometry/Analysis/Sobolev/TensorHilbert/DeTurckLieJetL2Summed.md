# DeTurckLieJetL2Summed.lean — Phase-A reconnaissance (NOT built; the covering engine EXISTS but its field-level bridge is a large missing reduction, not a small engine-swap)

## 2026-07-23 — dispatch = `deTurckLieCoeffField` top-separated producer; verdict: ENGINE FOUND, BRIDGE MISSING/LARGE

Dispatched (plan §"Planner acceptance №8") as the first of the two genuinely-missing C₀
constituents (`deTurckLieCoeffField`, then `lieCorr0Field`) of the threeArm precursor. Two phases:
(A) trace the field's committed structure and find which committed `_topSeparated_le` engine covers
its top-window gain; (B) build the summed producer IF covered, else report the exact missing engine.

**Outcome: the covering engine EXISTS — `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
(`CurvatureCoefficientDifferenceJetTower.lean:1823`, committed-clean) — and every committed identity
routing `deTurckLieCoeffField` → `connDiffSection` is present. BUT the committed field-level
reduction is fully GRID-COLLAPSED (dissolves the connDiffSection top-split into a raw ∇T-product grid
before integrating), so there is NO committed top-separated field-level bridge. Building one is a
LARGE multi-lemma re-derivation through the g₁-dependent bicontraction (`dLaBiContrFib`) and the
DeTurck-VF insertion (`deTurckLieWEndoInsert`) — NOT the ~40-line engine-swap the plan §№4/§№5
roadmap assumed for connDiff/Lie. No Lean written (a grid-collapsed R-dependent producer would
violate the ruling stop-signal; an orphan intermediate would be mislabelled machinery).**

---

## The field's committed structure (verified at HEAD `922dbc4ac`)

`deTurckLieCoeffField g₀ g₁ g_bg : SmoothCcTensor g₀ 2 2` (`RicciDeTurckSectionDifference.lean:7716`),
fibre `deTurckLieFib g₁ g_bg x = dLaBiContrFib g₁ g_bg x + deTurckLieDLbFib g₁ g_bg x` (`:7690`),
`g_bg`-dependent (three metrics). Committed additive split (`DeTurckLieKernelL2JetBound.lean:77`):

    deTurckLieCoeffField = deTurckLieDLaCoeffField + deTurckLieDLbCoeffField           (both (2,2))

- **DLa** (`deTurckLieDLaCoeffField`, `DeTurckLieKernelL2JetBound.lean:44`), fibre `dLaBiContrFib`:
  its lowered covector is a DIFFERENCE of covariant derivatives of `connDiffSection`
  (`dLaLoweredCovec`, `:1591`):

        dLaLoweredCovec g₀ g₁ g_bg = covGrad g₀ 1 2 (connDiffSection g₁ g₀)
                                   − covGrad g₀ 1 2 (connDiffSection g_bg g₀)

  committed background-splits: `deTurckLieCovDerivA_backgroundSplit` (:106),
  `dLaCovKernel_backgroundSplit` (:248), `connDiff_cocycle` (:91), `dLaLoweredCc_raise_repr` (:1629).
  The (2,2) field is the `dLaBiContrFib` bicontraction of this covector with the **g₁-orthonormal
  frame / sharpFlatEndo(g₁)** factors (`dLaBiContrFibFixedFrame`), i.e. a **g₁-dependent (nonlinear)
  product** of `covGrad(connDiffSection g₁ g₀)` with g₁-frame factors.

- **DLb** (`deTurckLieDLbCoeffField`, `:60`), fibre `deTurckLieDLbFib`: routes through the DeTurck
  vector field `deTurckLieWEndoInsert` (`DeTurckVectorFieldL2JetBound.lean:47`). The DeTurck VF is
  built from `connDiff`/`connDiffLoweredCc`: `wXi = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀
  g_bg` (`:57`, the cocycle split), `wEndo_eq_covDeriv_add_connDiff` (`:424`).

**Derivative order.** DLa's top factor is `covGrad(connDiffSection g₁ g₀)` = ∇(connDiffSection), one
covariant derivative MORE than the connDiff field. So `∇^i deTurckLieCoeffField` reaches `∇^{i+2}T`
(the committed grid runs `k ∈ range (i+3)`, top cell `∇^{i+2}T`;
`rfns_..._diagonalProductGrid_le:4409`; ball-uniform T-bound hyp is `j ≤ a+2`,
`DeTurckLieCoeffL2JetBound.lean:439`). Contrast: connDiff `∇^i` reaches `∇^{i+1}T`.
**So the deTurckLie top window is `a+2` (max derivative `∇^{a+2}T`), matching arm0Base
(the OTHER genuine C₀ constituent, top `a+2`), NOT connDiff (`a+1`).** The C₀ assembly top window is
therefore set at `a+2` by arm0 and deTurckLie together. Planner note: the "sibling-compatible (both
windows a+2)" target in the dispatch is compatible with **arm0** (top `a+2`), and the deTurckLie top
sum must be `∑_{j<a+3}‖∇^jT‖²` = `∑_{j≤a+2}`, one order above the connDiff/Lie `∑_{j<a+2}`.

## The covering engine (Phase-A answer)

**`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (`CurvatureCoefficientDifferenceJetTower
.lean:1823`)** — the `(1,2)` connection-difference engine, committed-clean (the 64 dirty lines of
that file are the unrelated `pureTrace`/`koszul_l2_succ` hunks; this engine is untouched and used
committed by `ConnDiffJetL2Summed.lean:178` and `DeTurckRemainderTameLipschitz.lean:41940`). Head
`10·S 0 · rfns(∇^{j+1}T)` (`S` from `sharpFlatEndoCc`, `(g₀,hδ₀)`-only ⇒ **R-independent Ktop**),
remainder in `boundedFactorGridWindow`. Applied at order `j = i+1`, it gives the deTurckLie top
window `∇^{i+2}T`. The three `(0,4)` curvature engines (`riemannLoweredBackgroundDifference:10570`,
`ricEndoBackgroundDifferenceField:11141`, `riemannG1LoweringDifference:11695`) are NOT a better fit:
deTurckLie's top factor is literally `covGrad(connDiffSection)`, not a curvature `(0,4)` difference.

Committed identities routing deTurckLie → connDiffSection (all present, all ball-uniform-only):
- DLa: `dLaLoweredCovec = covGrad(connDiffSection g₁ g₀) − covGrad(connDiffSection g_bg g₀)`
  (`:1591`); reduction `exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla` (`:2599`).
- DLb: `rfns_iCG_connDiffLoweredCc_eq_connDiffSection` / `norm_iCG_connDiffLoweredCc_eq_connDiffSection`
  (`DeTurckVectorFieldL2JetBound.lean:2192/2211`), `rfns_iCG_wCA_eq_connDiffSection` (`:2624`),
  `norm_iCG_wCA_eq_connDiffSection` (`:2648`), and the ball-uniform
  `connDiffSection_lowOrder_jetL2_succ_generic` (`:1954`) they feed.
- The `g_bg` parts (`connDiffSection g_bg g₀`, `connDiffLoweredCc g₀ g_bg`) are T-INDEPENDENT ⇒
  constant jets ⇒ absorbed into `Kc` (do NOT carry the top window); only the `g₁` part carries it.

## Why Phase B is NOT the small engine-swap the roadmap assumed (the blocker)

The committed field-level reductions are **fully grid-collapsed**, discarding the connDiffSection
top-split:

- `rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le`
  (`DeTurckLieKernelL2JetBound.lean:4397`):

        rfns(∇^i deTurckLieDLa) ≤ C i · ∑_{k∈range(i+3)} ∑_{n∈range(k+1)}
                                        ∑_{e∈antidiagonalTuple n k} ∏_m rfns(∇^{e m} T)

  — a raw `∇T`-product grid; the `10·S 0·rfns(∇^{i+2}T)` head is dissolved into the grid via
  `dLaGridWin`/`dLaPairCount`/`exists_rfns_pairTraceOpDla_tgrid`/`exists_rfns_dLaSym_tgrid`. The
  per-order ball-uniform proof (`:4606`) then integrates it with
  `antidiagonalTupleGrid_integral_ballUniform_tameWindow` into an R-opaque constant.
- DLb is analogous: `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform`
  (`DeTurckVectorFieldL2JetBound.lean:3041`) consumes the ball-uniform
  `connDiffSection_lowOrder_jetL2_succ_generic`, not the topSeparated engine.

There is **no committed head/topSeparated variant** for any `deTurckLie*`/`wEndo*`/`dLaBiContr*`
field (grep of `Analysis/Sobolev/TensorHilbert/` returns nothing). So the plan §№4/§№5 model
("swap the ball-uniform bound for the topSeparated engine, ~40-line reuse of `jetL2_sum_lowShift`")
does NOT apply: connDiff/Lie reused a single clean field↔section reindex
(`connDiffContrInsertionField_eq_reindex_slotExtend_two`); **deTurckLie has no such clean
field↔connDiffSection identity** — the bridge is the entire `dLaBiContrFib` bicontraction (DLa) and
`deTurckLieWEndoInsert` insertion (DLb), both g₁-dependent nonlinear products whose committed
pointwise reductions collapse the head.

## The exact missing bridge (smallest next brick)

A **top-separated pointwise reduction** replacing the grid-collapse — for DLa (and a DLb twin):

    ∃ Ktop ≥ 0 (from `10·S 0`, (g₀,hδ₀)[,g_bg]-only), ∃ Kc : ℕ→ℝ≥0,
      ∀ g₁ P htie hδ (hPball : ∀ j≤a+3, ‖∇^j P‖ ≤ R), ∀ i ≤ a, ∀ x,
        rfns(∇^i deTurckLieDLaCoeffField g₀ g₁ g_bg) x
          ≤ Ktop · rfns(∇^{i+2} P) x   +   Kc i · (grid remainder over ∇^{≤i+1} P)

built by re-running the `dLaBiContrFib` reduction with
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` at order `i+1` in place of
`rfns_iteratedCovGrad_connDiffSection_diagonalProductGrid_le` (used at `:2667`), keeping the head
cell (top factor `rfns(∇^{i+2}P)`) separate through the bicontraction Leibniz, and the `g_bg`-part
absorbed as a fixed field. Then integrate with `boundedFactorGridWindow_integral_ballUniform_
tameWindow` (top → `‖∇^{i+2}P‖²`, remainder → `Kc·(1+low)`), realizedFam wrapper (clone arm/connDiff),
and `jetL2_sum_lowShift` (top offset `p=2`, low offset `q=2`) to sum over `i≤a`. This is a
~300–500-line intricate tensor re-derivation PER HALF (DLa + DLb) with ~3-min focused-check cycles —
a multi-session brick, NOT one careful-iteration session. Recommended: DLa first (cleaner —
`dLaLoweredCovec` has the explicit covGrad identity), then DLb (via the DeTurck-VF ↔ connDiffSection
identities), then assemble `deTurckLieCoeffField = DLa + DLb` by triangle. The `lieCorr0Field`
constituent (LieCorr0Core.lean:583) is a separate later dispatch.

## Guardrails / verification status

No Lean written. Nothing committed; no dirty tracked file edited (elaboration never entered
`CurvatureCoefficientDifferenceJetTower.lean`; all claims are grep/Read forensics against HEAD
`922dbc4ac`). Only new untracked files touched (this note + the plan status log). (N)
`ricci_flow_unif_existence` remains **0%**; `deTurckLieCoeffField` is the 1st of the two genuinely-
missing C₀ constituents of the threeArm precursor (ruling item 2) and sits far below (N).

---

## 2026-07-23 (later) — DLa field bridge STARTED inside the file; route validated

The tree is now committed clean (plan №13); the bridge is being built **inside**
`DeTurckLieKernelL2JetBound.lean` next to its private deps.  Full route + piece status now lives in
`DeTurckLieKernelL2JetBound.md`.  Key corrections/findings vs the recon above:
- The "no top-separation" pessimism is resolved: the R-independence linchpin is
  `dLaGridWin b 1 = antidiagonalTupleGrid b 0 = 1`, so both frame operators (`pairTraceOpDla` and the
  perturb `slotInsert(perturbSharp)`) have **R-independent order-0 `rfns`**, and each appCcRS's
  `(i'=0,l=i)` cell carries the top `∇^{i+2}T` with an R-independent coefficient.
- **`dLaLoweredPerturbCc = appCcRS(perturb)(dLaLoweredCc)` also carries A1** (not purely lower-order as
  the recon guessed) ⟹ the field needs **two** nested appCcRS `(0,i)`-cell extractions (perturb + PT),
  both R-independent.  A generic extractor `rfns_iCG_appCcRS_topsep_of` handles both.
- The 8-summand kernel triangle top-separated twin (`exists_rfns_dLaKernelRaised_topsep`, the
  dispatched "Step 2") is a near-verbatim copy of `exists_rfns_dLaKernelRaised_tgrid` with `hA1`
  swapped for the top-separated connDiffSection bound (`Ktop = 128·(2·Kt0)`, R-indep).
- Per-cycle full-file `lake env lean` check ≈ 10-20 min (heavy in-file proofs with high heartbeats),
  so this is genuinely multi-cycle / multi-session as the recon estimated.

## 2026-07-24 — DLa field lift COMPLETE (session 2); DLa half of `deTurckLieCoeffField` DONE

Piece 4 (the field-level lift) is built + verified inside `DeTurckLieKernelL2JetBound.lean`
(`section DLaGridBrick`).  The DLa endpoint now exists:
`deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated`
(+ its per-order sibling), shape-matching `connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated`:
`∑_{i≤a}‖∇^i(deTurckLieDLaCoeffField g₀ (realizedFam …) g_bg)‖² ≤ Ktop·(∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²)) +
Kc·(1+∑_{j<a+3}(‖∇^jT‖²+‖∇^jT'‖²))`, `Ktop = CPT0·fr²·8·256·Kt0·(1+fr⁵δ₀²)·(appCcGdiag a)²` R-FREE,
`R` only in `Kc` (tame-window integrator).  Full decl list + constant derivation:
`DeTurckLieKernelL2JetBound.md` §"Piece 4 — BUILT".

Still open for `deTurckLieCoeffField` (= DLa + DLb): the **DLb** half
(`DeTurckVectorFieldL2JetBound.lean` / `deTurckLieDLbCoeffField`) top-separated summed producer, then the
**combined-coefficient assembly** `‖∇^i deTurckLieCoeffField‖² ≤ 2‖∇^i DLa‖² + 2‖∇^i DLb‖²` summed (via
`deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField`).

## 2026-07-24 — DLb field lift COMPLETE (session 2); DLb half of `deTurckLieCoeffField` DONE

The **DLb** half is now built + verified (axiom-clean: all four endpoints depend only on
`[propext, Classical.choice, Quot.sound]`, via direct `lean` with the project `LEAN_PATH`).  Layers:

- **Insert level** (`DeTurckVectorFieldL2JetBound.lean`, `section DLbTopSeparated`), the analytic
  heart — see `DeTurckVectorFieldL2JetBound.md` for the full tower.  The top order `∇^{i+2}T` enters
  ONLY through `wAlphaA = ∇^{i+1}wOmega`, and `wOmega`'s corner peel uses the argCorner Leibniz
  decomposition with the PUBLIC unconditional `rfns_appCcRS_appCcLeibnizPsi_diag_le` — so the corner
  coefficient bound is the `R`-free order-0 `cometricCastG0` fiber norm (`ΛClow 0`, NO `appCcGdiag`),
  and the top-free lower sum is bounded ball-uniformly by the two-arm grid integrator.  Endpoints:
  `deTurckLieWEndoInsert_realizedFam_jetL2_{perOrder,summed}_topSeparated`, `Ktop = 2·ΛClow 0·Ktop_xi`
  (`R`-free), summed via `jetL2_sum_lowShift a 2 3` (both windows `a+3`).
- **Field level** (`DeTurckLieCoeffL2JetBound.lean`), a THIN `×4·finrank` lift through
  `deTurckLieDLbCoeffField_eq_slotInsert_sum`: `deTurckLieDLbCoeffField_realizedFam_jetL2_{perOrder,
  summed}_topSeparated`, `Ktop = 4·finrank·Ktop_insert` (`R`-free).  Shapes match the DLa field
  siblings `deTurckLieDLaCoeffField_realizedFam_jetL2_{perOrder,summed}_topSeparated`
  (`DeTurckLieKernelL2JetBound.lean:5680/5966`).

Both DLa and DLb top-separated summed producers now exist and are shape-compatible.  **Remaining
for `deTurckLieCoeffField`:** the combined-coefficient assembly `‖∇^i deTurckLieCoeffField‖² ≤
2‖∇^i DLa‖² + 2‖∇^i DLb‖²` summed (via `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField`) — NOT
started this session (per dispatch scope: stop at the four verified DLb endpoints).  `(N)`
`ricci_flow_unif_existence` remains **0%**.

## 2026-07-24 — COMBINED assembly DONE (session 3); `deTurckLieCoeffField` constituent CLOSED

The combined-coefficient endpoints are built + verified + axiom-clean in
`DeTurckLieCoeffL2JetBound.lean` (the lowest file seeing both halves):
`deTurckLieCoeffField_realizedFam_jetL2_{perOrder,summed}_topSeparated`.  Route: the pointwise
triangle `‖∇ⁱ deTurckLieCoeffField‖² ≤ 2‖∇ⁱ DLa‖² + 2‖∇ⁱ DLb‖²` (private
`normSq_iCG_deTurckLieCoeff_le`, via the committed split `deTurckLieDLaCoeffField_add_
deTurckLieDLbCoeffField` :77 + `sq_le_two_add`), consuming the DLa field endpoints
(`DeTurckLieKernelL2JetBound.lean:5680/5966`, imported+visible) and the DLb field endpoints; summed
via `Finset.sum_le_sum` + `sum_add_distrib` + `← mul_sum` (no private `jetL2_sum_lowShift` needed).
Combined `Ktop = 2·(Ktop_DLa + Ktop_DLb)` R-FREE, single combined `Kc`.  SHAPES match the DLa/DLb
field siblings (s-before-i, windows `a+3`).  Whole-file `lake env lean` clean (zero errors, zero new
warnings); direct-`lean` axiom audit = `[propext, Classical.choice, Quot.sound]` for both.

**`deTurckLieCoeffField` (ruling item 2's 1st genuinely-missing C₀ constituent) is now CLOSED** — DLa
half + DLb half + combined assembly all built.  Next dispatches (planner's): `lieCorr0Field`
(`LieCorr0Core.lean:583`, the 2nd C₀ constituent) and the threeArm precursor assembly.  `(N)`
`ricci_flow_unif_existence` still **0%** (this constituent sits far below (N)).

## 2026-07-24 — `lieCorr0Field` (2nd C₀ constituent) RECON; STOPPED for two planner rulings

Full recon in `Analysis/Spectral/Intrinsic/DeTurckCoefficients/LieCorr0Core.md`
(§"jetL2 top-separated producer recon").  Headlines:

- **Ktop verdict: POSITIVE, R-FREE Ktop REQUIRED (DLb pattern, NOT Ktop=0).**
  Settled from the kernel structure: `lieCorr0Field = lc0Insert + lc0VB + lc0AMix + lc0Riem`
  (`LieCorr0Split.lean:154`); `lc0VB/lc0AMix` are order-1·order-1 quadratics and `lc0Riem` is
  T-independent g₀-curvature (all Kc); but `lc0Insert` carries `−deTurckLieWEndo g₁ g₀
  = −∇^{g₁}(deTurckVF g₁ g₀)` = bare ∇²T (order 2).  The "zeroth-order"/"algebraic" name is about the
  operator VALENCE, not the T-order — the top is real.
- **Top engine already built — direct DLb reuse at g_bg:=g₀.**  `insert_base` (`LieCorr0Split.lean:103`)
  ⟹ `lc0Insert g₀ g₁ g₀ = −deTurckLieEndoArmField g₀ g₁ g₀`, and `deTurckLieEndoArmField g₀ g₁ g_bg`
  ≡ `deTurckLieDLbCoeffField g₀ g₁ g_bg` (both `ofCLM(deTurckLieDLbFib g₁ g_bg)`, defeq).  So
  `lc0Insert g₀ g₁ g₀ = −deTurckLieDLbCoeffField g₀ g₁ g₀`, and the DLb field producer at g_bg:=g₀
  (`DeTurckLieCoeffL2JetBound.lean:432/483`) gives its top-separation verbatim, `Ktop = Ktop_DLb` R-free.
- **Low (Kc) machinery already built pointwise** in `LieCorr0LowJet.lean` (`vb_refold`:1408,
  `amix_refold`:1581, `riem_refold`:1628, `trace2_grid`:1810, `insert_diff`:1243) — lift to jetL2 by the
  same tame-window integrator the siblings use.
- **BLOCKER 1 (home):** endpoints must live DOWNSTREAM in `TensorHilbert/` (they reference the DLb
  producer + integrators); `LieCorr0Core.lean` is upstream (no TensorHilbert/CovGrad file imports any
  `LieCorr0` module).  Proposed: NEW leaf `TensorHilbert/LieCorr0CoeffL2JetBound.lean` (per-constituent
  pattern) importing `DeTurckLieCoeffL2JetBound` + `LieCorr0Split` + `LieCorr0LowJet`.  Editable set must
  expand.  (Alt: extend `DeTurckLieCoeffL2JetBound.lean`.)
- **BLOCKER 2 (assembly shape):** lieCorr0's ∇²T is designed to CANCEL DLb's base arm
  (`tail_base_split`:171 ⟹ `lieCorr0Field + deTurckLieEndoArmField(base)` is ∇²T-free).  Option A
  (this dispatch: standalone positive-R-free-Ktop producer, triangle into Psi0 — over-counts ∇²T but
  R-free, fine for R1τ) vs Option B (cancellation-preserving combined deTurckLie+lieCorr0 ∇²T-free
  bound).  Planner confirm A vs B before session 2.
- Session-2 route (Option A): `lc0_decomp` → 5 summands (split `lc0Insert g_bg` = base + diff) →
  5-way pointwise triangle → top summand via DLb producer @g_bg:=g₀ → 4 Kc summands via LowJet
  refolds + tame-window integrator → `Ktop = 5·Ktop_DLb` R-free, summed via `jetL2_sum_lowShift a 2 3`.
  ~1-2 sessions (both top engine and low machinery pre-built).  No Lean written this session.
