# DLaHeadCellRfns.lean — pointwise (`rfns`) top-separated head cell for the DLa 8-summand triangle

## Role in the tree

DLa Step 2 (the 8-summand triangle) sub-brick, of the 3-part DLa top-separation
(DLa head → DLa 8-summand triangle → DLb → `DLa+DLb`), which is the first of the two
genuinely-missing `C₀` constituents (`deTurckLieCoeffField`, `lieCorr0Field`) of the data-weighted
threeArm precursor — ruling item 2 of the R1τ frontier of the black box
`(N) = ricci_flow_unif_existence`.  `(N)` remains **0%**.

## What this file delivers (a COMPILING PREFIX, not the full Step-2 target)

One public theorem in namespace `DifferentialGeometry.Integral.Connection`:

- `covGradConnDiffSection_perOrder_rfns_topSeparated` — the **pointwise** (`riemannianFiberNormSq`,
  pointwise in `x`) top-separated bound for `covGrad (connDiffSection g₁ g₀)` (the `A1` top of the DLa
  8-summand kernel `dLaKernelRaisedCc`):
  ```
  rfns (∇^i (covGrad (connDiffSection g₁ g₀))) x
    ≤ (2·Kt0) · rfns (∇^{i+2} P) x
      + (2·Kc0(i+1)·(i+1)) · boundedFactorGridWindow (rfns ∇^{≤·} P weights) (i+1) (i+3)
  ```
  `Ktop = 2·Kt0` (`Kt0` = engine head `10·S 0`) is **`R`-independent**; the remainder is a
  `boundedFactorGridWindow` of the pointwise `∇^{≤ i+1}P` weights.

This is the **un-integrated sibling** of `DLaTopSeparated.lean`'s
`covGradConnDiffSection_perOrder_l2_topSeparated_generic` (which integrates exactly this pointwise
step).  The integrated head atom exposes only the `L²` bound; the 8-summand triangle needs **pointwise**
`rfns` bounds per summand (it triangles all 8 summands pointwise, then integrates once), so this is
precisely the shape the triangle's `A1` slot consumes.

Route = `DLaTopSeparated.lean`'s internal `hpt` step, exported as a standalone lemma:
commutation identity `rfns_iteratedCovGrad_covGrad_comm_rs` (equality, no `finrank²`) then the
committed top-separated engine `rfns_iteratedCovGrad_connDiffSection_topSeparated_le` at order `i+1`;
remainder reshaped by the copied private `tsResSum_le_boundedWindow`.

## Imports / scoping

Imports only committed-clean `RemainderCoeffL2JetMoser` + `RicciConnDiffOrder1TameEnvelope` (same cone
as `ConnDiffJetL2Summed.lean` / `DLaTopSeparated.lean`; their oleans are already co-located in
`C:/dgbuild/e87b/lib/lean/...`).  Does NOT import `DLaTopSeparated` (nothing needed from it),
`DeTurckLieKernelL2JetBound` (its DLa bridge is private — see blocker), or any dirty tracked file.
Private helper `tsResSum_le_boundedWindow` copied verbatim with provenance (pure `Combinatorics.*`).

## THE STRUCTURAL BLOCKER (why the full Step-2 target is NOT delivered here)

**The dispatched Step-2 target — a top-separated per-order/summed `L²` bound for the `(2,2)` field
`deTurckLieDLaCoeffField` — CANNOT be built in a leaf file at HEAD `922dbc4ac`.**  The task premise
("import `DeTurckLieKernelL2JetBound` and the DLa field's identities") is infeasible: the entire
bridge is `private`.

Verified `private`/`public` audit of `DeTurckLieKernelL2JetBound.lean` (git `922dbc4ac` + 10 dirty
lines):

- `private`: `deTurckLieDLaCoeffField_eq_pairTrace` (:4298), `dLaKernelRaisedCc` (:1589),
  `dLaLoweredCc` (:1497), `dLaLoweredCc_raise_repr` (:1629), `dLaSymCc` (:4002),
  `pairTraceOpDla` (:3922), `sigmaE0dla` (:3553), `dLaQuadCc` (:1539), `dLaConnArmPt` (:1527),
  `dLaGridWin` (:2096), `dLaPairCount` (:2227), `exists_rfns_dLaKernelRaised_tgrid` (:3018),
  `exists_rfns_dLaSym_tgrid` (:3346), `exists_rfns_pairTraceOpDla_tgrid` (:4194),
  `exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla` (:2599), `exists_fixedField_rfns_jet_dla`
  (:2324), `dLaQuad_tower_of_factors` (:2907), `rfns_iCG_add_le_dla`/`rfns_iCG_sub_le_dla` (:2307/:2284).
- The ONLY public DLa surface: `deTurckLieDLaCoeffField` (def), `…DLb…`, the three fibre identities
  (`connDiff_cocycle`, `deTurckLieCovDerivA_backgroundSplit`, `dLaCovKernel_backgroundSplit`),
  the order-0 ballUniform lemmas, `symmC0_rfns_le` (the +10 dirty lines), the grid-collapse
  `rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le`, and the R-dependent
  `deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_ballUniform`.  **No public top-separated entry
  point, and no public identity exposing the kernel/pairTrace/dLaSym structure.**

Consequences:
1. A leaf file cannot reference these private declarations (Lean `private` is module-scoped, even
   within the same `DifferentialGeometry.Integral.Connection` namespace).
2. Reconstructing the `(2,2)` bridge from public pieces is impossible: the `(2,2)` field's top passes
   through `deTurckLieDLaCoeffField_eq_pairTrace` → `dLaSymCc` (0,4) contracted with `pairTraceOpDla`
   (6,2) → `dLaLoweredG1Cc` = `dLaLoweredCc` + `dLaLoweredPerturbCc` → `dLaKernelRaisedCc` (1,3) →
   `A1` = `covGrad(connDiffSection)`.  Every arrow is a private def/lemma.
3. Copying the machinery verbatim would (a) DUPLICATE private defs that already exist in the imported
   module (`dLaQuadCc`, `dLaGridWin`, `dLaPairCount`, `dLaConnArmPt`, …) — a forbidden **parallel API**
   (CLAUDE.md "do not create a parallel API"); (b) run ~1300 lines for the `(1,3)` kernel alone and
   ~2500+ for the full `(2,2)` field including the perturbation/symmetrization/pairTrace layers —
   violating the surgical-change and ≤3000-line-file rules; (c) not be verifiable in one session
   (~3-min focused-check cycles).
4. Editing `DeTurckLieKernelL2JetBound.lean` in place (the correct home, next to its private deps) is
   **forbidden**: it is a dirty tracked file (Codex-owned; `git status --short` shows ` M`), and plan
   §"Executor constraints" bars touching any file in `git status --short`.

**The correct home for the DLa top-separation is INSIDE `DeTurckLieKernelL2JetBound.lean`, next to its
private dependencies.**  The +10 dirty lines there (`symmC0_rfns_le`, a public export of the `symmS`
order-0 `rfns` bound used by `exists_rfns_dLaSym_tgrid`) suggest the Codex lane may already be
building this exact top-separation in-file.  So this sub-brick is effectively **blocked on the Codex
lane** (either finishing/releasing that file, or exposing the needed private pieces — minimally
`dLaKernelRaisedCc`, `deTurckLieDLaCoeffField_eq_pairTrace`, and top-separated variants of
`exists_rfns_dLaSym_tgrid`/`exists_rfns_pairTraceOpDla_tgrid` — as public).

## Classification

Missing-API / verification obstruction (structural), NOT a mathematical obstruction.  The maths is
sound and the committed grid-collapsed proof (`exists_rfns_dLaKernelRaised_tgrid`,
`rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le`) shows the whole reduction is in
place; only the top cell is dissolved.  Top-separating it is the head-cell swap this file's lemma
verifies pointwise for `A1`, plus 7 into-`Kc` summands and the pairTrace Leibniz — but all of that must
happen where the private machinery lives.

## Verification

Direct `lean` typecheck vs the redirected olean tree `C:/dgbuild/e87b/lib/lean` (recipe in
`RemainderCoeffTopSeparated.md`).  Header carries `autoImplicit false`, `relaxedAutoImplicit false`,
`maxSynthPendingDepth 3`.  `#print axioms` on the theorem must be exactly
`[propext, Classical.choice, Quot.sound]`.

STATUS: <pending first typecheck — Codex lane held the Lean lock at dispatch; quiet-window waiter armed>

## Next line-level step (for whoever resumes, IN the owning file)

In `DeTurckLieKernelL2JetBound.lean` (once clean/owned), clone `exists_rfns_dLaKernelRaised_tgrid`
(:3018) into `exists_rfns_dLaKernelRaised_topSeparated`, replacing `hA1` (currently
`hCA g₁ T … (i+1) x` = grid) with the pointwise top-separated head (this file's
`covGradConnDiffSection_perOrder_rfns_topSeparated`, or inline the public engine + comm identity),
keeping `A1`'s `rfns(∇^{i+2}P) x` cell separate; the other 7 summands keep their committed grid bounds
→ `Kc`.  Then thread it up through `exists_rfns_dLaSym_tgrid` (:3346, keep `dLaLoweredPerturbCc`'s
`dLaLoweredCc` factor's top separate; its `CP`-perturb operator at order 0 is δ₀-bounded ⇒ into
`Ktop`) → the pairTrace Leibniz (`deTurckLieDLaCoeffField_eq_pairTrace`, keep the `i'=0` cell) →
integrate → realizedFam wrapper → `jetL2_sum_lowShift a 2 2`.
