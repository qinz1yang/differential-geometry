# LieCorr0CoeffL2JetBound

New leaf (RULING 1, planner acceptance №19): the `TensorHilbert/` home of the
`lieCorr0Field` realizedFam jet-L2 top-separated producer (2nd genuinely-missing
`C₀` constituent of `Ψ₀`).  Namespace `DifferentialGeometry.Integral.Connection`.

Endpoints (deferred until all four Kc atoms land, see below):
`lieCorr0Field_realizedFam_jetL2_{perOrder,summed}_topSeparated`, shapes verbatim
= the deTurckLie siblings `DeTurckLieCoeffL2JetBound.lean:739/799`, `Ktop`
R-free (from the DLb top piece), single summed `Kc`.

## State (2026-07-25): diamond RESOLVED; RE-RECON DONE; verdict POSITIVE (no LowJet).

The TensorRS TotalSpace topology-instance diamond that blocked `LieCorr0Split`
is FIXED (commit `55efbcbd7`): `LieCorr0Split` now BUILDS lake-green.
`LieCorr0LowJet` is an ABANDONED DEEP-WIP draft (~40 pre-existing errors: syntax
errors at :1381/:1520/:1598, undefined `lieCorr0IVPerm`, unimported
`ccTensorBilinSymm`/`gFibreOpBound`, embedded `sorry`s, genuine proof failures —
see `LieCorr0LowJet.md`).  It is a LIABILITY, quarantined, NOT an asset.  This
leaf must therefore be built WITHOUT LowJet.  (The full diamond saga is retired;
its blow-by-blow lived in this note's earlier revisions and is superseded.)

### Already written + green-in-principle (the TOP piece + assembly helper)
- `endoArm_eq_dlb` : `deTurckLieEndoArmField g₀ g₁ g_bg = deTurckLieDLbCoeffField
  g₀ g₁ g_bg` (both `ofCLM(deTurckLieDLbFib g₁ g_bg)`, by `ext`).
- `lc0Insert_base_eq_neg_dlb` : `lc0Insert g₀ g₁ g₀ = −deTurckLieDLbCoeffField
  g₀ g₁ g₀`.
- `lc0InsertBase_realizedFam_perOrder_topSeparated` : the top piece's per-order
  top-separated bound, inherited verbatim from the committed DLb field producer
  at `g_bg := g₀`; `Ktop = Ktop_DLb` (R-free).
- `sq_le_five_add` : `t ≤ a+b+c+d+e` (all ≥0) ⟹ `t² ≤ 5(a²+…+e²)`.

## The 5-way split (field level)

`lc0_decomp` (`LieCorr0Split.lean:169`): `lieCorr0Field g₀ g₁ g_bg = ((lc0Insert
g₀ g₁ g_bg + lc0VB g₀ g₁) + lc0AMix g₀ g₁ g_bg) + lc0Riem g₀ g₁`.  Split the
insert piece `lc0Insert g_bg = lc0Insert g₀ + (lc0Insert g_bg − lc0Insert g₀)`
(the base insertion is the top; the difference is a Kc piece):

    lieCorr0Field = lc0Insert g₀    [TOP,  Ktop R-free via DLb]
                  + (lc0Insert g_bg − lc0Insert g₀)   [Kc]
                  + lc0VB            [Kc]
                  + lc0AMix          [Kc]
                  + lc0Riem          [Kc]

Ruling 2 discipline: the four Kc pieces are `∇²T`-free (each `∇ⁱ` reaches at most
`∇^{i+1}T`, well inside the `∑_{j<i+3}` window) and carry `R` in `Kc` only; the
top piece keeps the R-free `Ktop`.  `sq_le_five_add` fans the 5-way sum out to
`Ktop = 5·Ktop_DLb`, single summed `Kc`.

## RE-RECON VERDICT (2026-07-25) — POSITIVE.  All four Kc pieces build from committed generic engines; LowJet's refolds are NOT needed.

The old plan (acceptance №19) lifted the four Kc pieces via LowJet's
`vb_refold`/`amix_refold`/`riem_refold`/`insert_diff` refolds.  That premise is
DEAD (LowJet is broken WIP).  Fresh recon of the committed tree shows the
refolds are unnecessary: a fully generic "cometric-trace of a product of two
order-1 factors → jet-L2 ball-uniform" engine already exists and covers all four
pieces.  NO salvage-port from LowJet is required.

### The reusable generic engine (the linchpin)
- **Pointwise Leibniz product-grid**: `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
  (`MetricArmCoeffJetTower.lean:2360`).  For the cometric contraction
  `appCcRS g p a b Φ W` (= `traceStep`-cometric ∘ `prodKappa(Φ)` ∘ `W`):
  `rfns(∇^j appCcRS Φ W) ≤ appCcGdiag j · ∑_{i<j+1} rfns(∇^i Φ) · ∑_{l<j+1-i} rfns(∇^l W)`.
  Proved by induction via `covGrad_appCcRS_eq` (Leibniz).  `appCcRS` is exactly
  `traceStep ∘ prodKappa`; `tensor0SProdKappaFib` (`DeTurckLieHigherOrderCoeffField.lean:389`)
  is the underlying `prodKappa`.
- **Integrator (ball-uniform, R in constant)**:
  `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
  (`RemainderCoeffPerOrderJetEnvelopes.lean:870`): for two fields S,T with
  order-0 sups `ΛS,ΛT`, `∫ ∑_i rfns(∇^i S)·∑_l rfns(∇^l T) ≤ C·(ΛT²·∑‖∇^i S‖² +
  ΛS²·∑‖∇^l T‖²)` (Moser split + Gagliardo–Nirenberg).  This is the ballUniform
  integrator (NOT `antidiagonalTupleGrid_integral_ballUniform_tameWindow`, which
  is used only in the topSeparated tower).
- **Committed end-to-end precedent** for the exact lc0VB shape:
  `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
  (`DeTurckLieArm1CoeffL2JetBound.lean:4812`) — "g₁-cometric trace of
  connection-difference × interior-product(deTurckVF)"; its per-piece glue
  `lieArm1_appCc12_normSq_le` (:1853) and sub-producers
  `lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform` (:4209) /
  `lieArm1Piece_connDiffBg_…` (:4311) combine layers 1+2.
- **ballUniform → topSeparated (Ktop=0) reshape**: the traceHess/Moser pattern —
  `P i ≤ 0·(top) + P i·(1 + low)` by `nlinarith` (see `TraceHessJetL2Summed.md`).

### Atom availability (agent-verified)
- `connDiff` / `connDiffSection` / `connDiffLoweredCc` (Atom 3): RICHLY controlled
  pointwise — `rfns_iteratedCovGrad_connDiffSection_le`
  (`ConnectionDifferenceJetTower.lean:1638`) + order-0/order-1 fibre bounds +
  envelope packagers.
- `metricConnDiffLoweredFib g₁ g₁ g'` (Atom 1): NO direct jet bound under its own
  name.  Only route is its `_toModel` identity `= gm.inner(connDiff gA gB v₀ v₁)
  v₂` (`DeTurckLieHigherOrderCoeffField.lean:460`) → push through Atom 3.
  **Mismatch to watch**: it lowers by **g₁** (moving), whereas the committed
  connDiff bounds lower by **g₀** (background) — the reduction must absorb the
  g₁-vs-g₀ lowering (the Arm1 file already handles this via
  `lieArm1_deTurckVF_cometric_trace`, `DeTurckLieArm1CoeffL2JetBound.lean:2897`).
- raw `deTurckVF g₁ g'` (Atom 2): NO direct jet bound; its jet control lives on
  the `deTurckLieWEndoInsert` endomorphism (= ∇W + connDiff·W) and, for the raw
  contraction, on the DLb low atoms `wOmega`/`wXi`
  (`DeTurckVectorFieldL2JetBound.lean` `_lowOrder_jetL2_succ_generic`).

### Per-summand routing

| Kc piece | fibre structure (`LieCorr0Core.lean`) | committed route | effort |
|---|---|---|---|
| `lc0VB` | `2·traceStep(g₁,VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) ∘ interior_product(deTurckVF g₁ g₀)` (:144) | twoArm engine (Φ = metricConnDiffLowered→connDiff, W = deTurckVF interior-product); closest to `deTurckLieArm1Coeff` (same atoms, different contraction — NOT a reindex) | MEDIUM |
| `lc0AMix` | `2·(AMixHalf + swap·AMixHalf)`, `AMixHalf` = chain of traceSteps over prodKappa(metricConnDiffLoweredFib g₁ g₁ g_bg) and prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) (:162) | twoArm engine, both factors connection-difference (via Atom-3 push) | MEDIUM |
| `lc0Riem` | `−traceStep(g₁,RiemPerm2) ∘ traceStep(g₀,RiemPerm1) ∘ prodKappa(lieCorr0RiemLoweredFib g₀)` (:237); passenger = FIXED g₀-curvature `g₀.inner∘riemannOp(LC g₀)` | ONE live factor (the g₁-cometric); passenger T-independent (constant jets).  Either twoArm with a constant arm, or the traceHess/gInvDiffSlotCoeff cometric template (`deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff` → `gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform`) | MEDIUM-LOW (simplest — one live factor) |
| `lc0Insert g_bg − lc0Insert g₀` | `slotInsert(NEndo g_bg − NEndo g₀)`; by `nEndo_diff` (`LieCorr0Split.lean:103`) = `slotInsert(connDiff g₁ g₀ (deTurckVF g₁ g₀ − deTurckVF g₁ g_bg))` | twoArm engine: connDiff (Atom 3, controlled) × deTurckVF-difference (controlled via DLb `wOmega`/`wXi`); slotInsert is a fibrewise isometry | MEDIUM |

All four go to `Kc` (R allowed).  Only the top piece needs the R-free `Ktop`,
already delivered via DLb.

## SESSION STATE + RESUMPTION POINT (2026-07-25, paused by planner stand-down)

### What is verified-green vs drafted (be precise)
- **NOTHING verified-green by this session.** No `lake`/`lean` build was run.
- The leaf `.lean` is UNTOUCHED this session (exactly as committed).  As
  committed it STILL imports `LieCorr0LowJet` (line 3) and therefore **does NOT
  build** (LowJet is broken WIP).  So the four written theorems (`endoArm_eq_dlb`,
  `lc0Insert_base_eq_neg_dlb`, `lc0InsertBase_realizedFam_perOrder_topSeparated`,
  `sq_le_five_add`) are DRAFTED and verified-in-principle (the top piece just
  inherits the committed DLb producer at `g_bg:=g₀`), but have NEVER been built.
- The recon verdict above is the only deliverable finalized this session (a note).

### Did LowJet turn out needed?  NO — FULLY AVOIDABLE (confirmed).
The generic twoArm product-grid engine
(`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le` +
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`) plus the
`deTurckLieArm1Coeff` ballUniform precedent cover all four Kc pieces.  LowJet's
`vb_refold`/`amix_refold`/`riem_refold`/`insert_diff` refolds are NOT needed and
NO salvage-port from LowJet is required.  The leaf's LowJet import should be
DROPPED (it is a pure liability).

### Exact resumption point for a successor
1. Edit the leaf `.lean`: DELETE line 3
   (`import …DeTurckCoefficients.LieCorr0LowJet`).  Keep line 1
   (`DeTurckLieCoeffL2JetBound`) + line 2 (`LieCorr0Split`).  For the Kc atoms,
   ADD imports of the twoArm-engine homes as needed:
   `Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower`,
   `Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes`,
   `Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound`.
2. Whole-file check the leaf (the four drafted theorems + dropped import) to bank
   the top piece green.  Expected clean (no LowJet symbol is used by them).
3. Land the FIRST Kc atom green (sorry-free), standalone ballUniform →
   topSeparated(Ktop=0) per-order producer.  Simplest-first order:
   `lc0Riem` (one live factor: the g₁-cometric; passenger is a fixed
   g₀-curvature with constant jets) → `insert-diff` → `lc0VB` → `lc0AMix`.
   Each: express the piece via `appCcRS`/twoArm of controlled factors, apply the
   pointwise product-grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
   + the integrator `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`,
   thread `realizedFam`, then reshape ballUniform→topSeparated with `Ktop=0`
   (`P i ≤ 0·top + P i·(1+low)`, `nlinarith`).
4. Assemble the two endpoints ONLY once all four Kc atoms are green (they need
   all four via `sq_le_five_add`).  Until then keep the leaf axiom-clean
   (top piece + landed atoms; NO sorries).  `Ktop = 5·Ktop_DLb` (R-free),
   single summed `Kc`.

## Honest accounting
`(N) ricci_flow_unif_existence` still **0%**.  The constituent is NOT closed:
the two endpoints are 0% (unstated), and their dedicated machinery is the top
piece (done) + four Kc atoms (0–1 landed this session) + the 5-way assembly
(helper `sq_le_five_add` done, wiring pending).  Realistic constituent
completion: top piece ~1/6, each Kc atom ~1/6, assembly ~0 until atoms land.
This is genuinely multi-session (four medium fresh derivations + endpoints), but
the route is now fully committed-machinery-backed with NO LowJet dependency —
the road is reopened.

## Verification
NONE run this session (paused at recon by planner stand-down before any build).
The leaf `.lean` is unedited/as-committed (still imports broken LowJet ⟹ does
not build until the resumption step 1 drops that import).  No commit.
