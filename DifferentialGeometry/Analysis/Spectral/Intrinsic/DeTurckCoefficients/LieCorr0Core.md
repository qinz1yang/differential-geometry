# LieCorr0Core

## Role

This module owns the reusable zeroth-order DeTurck correction field extracted
from the legacy monolithic implementation.

## Verified state

`lieCorr0Field` is public, sorry-free, and has passed focused verification and
its named module build. The extraction keeps the coefficient construction below
the 3000-line source limit and introduces no Sobolev assumptions.

This producer is complete (100%). It is infrastructure for, not a proof of,
the mixed `H3 -> H1` endpoint, which remains theorem-level 0%.

---

## jetL2 top-separated producer recon (2026-07-24, dispatched brick; STOPPED for two planner rulings)

Dispatch: build `lieCorr0Field_realizedFam_jetL2_{perOrder,summed}_topSeparated`
(2nd of the 2 genuinely-missing C0 constituents of Psi0 = -2*arm0Field +
deTurckLieCoeffField + lieCorr0Field), shape-matching the deTurckLie siblings
(`DeTurckLieCoeffL2JetBound.lean:739/799`).  This is RECON ONLY — no `.lean`
written — because both a canonical-home blocker and an assembly-shape choice
need a planner ruling before code.

### KTOP VERDICT (the decisive call): POSITIVE, R-FREE Ktop REQUIRED — NOT Ktop=0.

`lieCorr0Field` is the DLb pattern (RULING 2), NOT the traceHess pattern.
Settled from the ACTUAL kernel structure, not the "zeroth-order" name:

- `lc0_decomp` (`LieCorr0Split.lean:154`):
  `lieCorr0Field g0 g1 g_bg = lc0Insert g0 g1 g_bg + lc0VB g0 g1
   + lc0AMix g0 g1 g_bg + lc0Riem g0 g1`.
- Derivative orders (T = metric perturbation carried by g1; `deTurckVF g1 g'`
  = metric-trace of Christoffel difference = ORDER 1 ~ grad T; `connDiff g1 g'`
  = Christoffel-difference tensor = ORDER 1; `deTurckLieWEndo g1 g' =
  (LeviCivita g1).toFun (deTurckVF g1 g')` = grad^{g1}(deTurckVF) = ORDER 2,
  bare grad^2 T — this is exactly DLb's `wOmega = deTurckVF` (order 1),
  `grad^{i+1} wOmega ~ grad^{i+2} T`):
  * `lc0Insert` = slotInsert of `lieCorr0NEndo = connDiff(deTurckVF g1 g0)
    - connDiff(deTurckVF g1 g_bg) - deTurckLieWEndo g1 g0`.  The two connDiff
    terms are order-1 . order-1 products (the section derivative cancels in the
    CONNECTION difference — `connDiff_apply`), so NO bare grad^2 T; the third
    term `- deTurckLieWEndo g1 g0` carries bare grad^2 T.  **lc0Insert carries
    the genuine top.**
  * `lc0VB`, `lc0AMix` = products of `metricConnDiffLoweredFib` (order 1) and
    `deTurckVF` (order 1) / two Christoffel diffs — quadratic, order-1 factors,
    NO bare grad^2 T.  -> Kc.
  * `lc0Riem` = `riemannOp(LeviCivita g0)` (T-INDEPENDENT g0-curvature) traced
    against the g1-cometric (algebraic in T, no grad) — order 0 in grad T.
    -> Kc.
- So the standalone `lieCorr0Field` genuinely reaches `grad^{i+2} T` (through
  `- deTurckLieWEndo g1 g0` inside `lc0Insert`).  Lumping that under the
  R-carrying Kc would lose the top coefficient's R-freeness irrecoverably and
  poison the Psi0 assembly (exactly RULING 2's argument for DLb).  **Ktop=0 is
  REJECTED.  Positive R-free Ktop is required.**

### The top engine already exists — no new engine, direct DLb reuse at g_bg:=g0.

`nEndo_base` (`LieCorr0Split.lean:79`): `lieCorr0NEndo g0 g1 g0 = -deTurckLieWEndo
g1 g0`.  `insert_base` (:103) rearranges to `lc0Insert g0 g1 g0 =
-deTurckLieEndoArmField g0 g1 g0`.  And `deTurckLieEndoArmField g0 g1 g_bg`
(`RiemannCoefficientPalatiniRefold.lean:106`) and `deTurckLieDLbCoeffField
g0 g1 g_bg` (`DeTurckLieKernelL2JetBound.lean:60`) are BOTH definitionally
`ofCLM (deTurckLieDLbFib g1 g_bg)` — i.e. equal by `rfl`.  Hence

  **lc0Insert g0 g1 g0 = -deTurckLieDLbCoeffField g0 g1 g0**,

and the JUST-CLOSED DLb field producer
`deTurckLieDLbCoeffField_realizedFam_jetL2_{perOrder,summed}_topSeparated`
(`DeTurckLieCoeffL2JetBound.lean:432/483`, g_bg FREE) at `g_bg := g0` gives the
top piece's top-separation verbatim; `‖grad^i (lc0Insert g0 g1 g0)‖^2 =
‖grad^i (deTurckLieDLbCoeffField g0 g1 g0)‖^2` (norm of negation), so
`Ktop_lieCorr0 = Ktop_DLb` — R-free, inherited.

### The low (Kc) machinery already exists at the pointwise layer.

`LieCorr0LowJet.lean` (1810+ lines, focused-checked per its `.md`) already
proves the pointwise covariant-jet control for every grad^2-free piece:
`vb_refold` (:1408), `amix_refold` (:1581), `riem_refold` (:1628) rewrite VB /
AMix / Riem as moving-trace-of-fixed-passenger; `trace_grid` (:1648) /
`trace2_grid` (:1810) give antidiagonal metric-jet grid control of the moving
trace ("no pointwise second metric derivative is requested" — its `.md`);
`insert_diff` (:1243) / `nins_diff` (:1216) give the grad^2-free
`lc0Insert g0 g1 g_bg - lc0Insert g0 g1 g0 = connDiff(deTurckVF g1 g0)
- connDiff(deTurckVF g1 g_bg)` difference (`nEndo_diff`, `LieCorr0Split.lean:88`).
These lift to jetL2 by the same tame-window integrator the siblings use
(`antidiagonalTupleGrid_integral_ballUniform_tameWindow` /
`boundedFactorGridWindow_integral_ballUniform_tameWindow`).

### BLOCKER 1 (canonical home — needs planner ruling; mission's STOP condition).

The endpoint statement references the DLb field producer and the tame-window
integrators, all in `Analysis/Sobolev/TensorHilbert/`.  `LieCorr0Core.lean` (and
`LieCorr0Split` / `LieCorr0LowJet`) live in `Analysis/Spectral/Intrinsic/
DeTurckCoefficients/`, UPSTREAM of the jetL2 layer (verified: no TensorHilbert/
CovGrad file imports any `LieCorr0` module).  So the endpoints **cannot** live
in `LieCorr0Core.lean` (import cycle), and re-deriving the DLb engine upstream
is forbidden parallel API.  Per the mission editing rule ("if the endpoints must
live in a DIFFERENT file, STOP and report the split"): the endpoints must live
DOWNSTREAM in `TensorHilbert/`.  **Proposed home:** a NEW leaf
`Analysis/Sobolev/TensorHilbert/LieCorr0CoeffL2JetBound.lean` (namespace
`DifferentialGeometry.Integral.Connection`), mirroring the per-constituent
pattern (`ConnDiffJetL2Summed`, `LieFieldJetL2Summed`, `TraceHessJetL2Summed`).
Imports: `DeTurckLieCoeffL2JetBound` (DLb field producer + realizedFam plumbing),
`LieCorr0Split` + `LieCorr0LowJet` (decomposition + low machinery), the
tame-window integrator module.  (Alt: extend `DeTurckLieCoeffL2JetBound.lean`,
already 858 lines and the natural combined DeTurck-Lie home — less clean on the
3000-line cap.)  Either way the editable set must expand beyond
`LieCorr0Core.lean`.

### BLOCKER 2 (assembly shape — needs planner ruling; structural).

`LieCorr0Split.md` warns: estimating `lieCorr0` and the DLb base arm SEPARATELY
"would reintroduce a highest-derivative term that is not small at H3
regularity."  Reason: `tail_base_split` (`LieCorr0Split.lean:171`) shows
`lieCorr0Field g0 g1 g_bg + deTurckLieEndoArmField g0 g1 g0` is grad^2 T-FREE
(the `-deTurckLieWEndo g1 g0` top in lieCorr0 CANCELS the `+deTurckLieWEndo
g1 g0` base arm of DLb).  In Psi0 the DLb top (`+grad(deTurckVF g1 g_bg)`) and
the lieCorr0 top (`-grad(deTurckVF g1 g0)`) sum to `grad(deTurckVF g1 g_bg
- deTurckVF g1 g0)` = order-1 (T-independent Christoffel diff, algebraic g1^{-1})
— i.e. the bare grad^2 T of the two constituents CANCELS in the assembly.
  * OPTION A (this dispatch): standalone positive-R-free-Ktop producer for
    lieCorr0Field, combined into Psi0 by triangle (`-2 arm0`, deTurckLie,
    lieCorr0 each keep their R-free Ktop).  R-free (route-test compliant, RULING
    2 house pattern) but OVER-COUNTS grad^2 T (no cancellation).  Fine for R1tau,
    which needs Ktop R-FREENESS, not grad^2 T-freeness.
  * OPTION B: bound the CANCELLATION-preserving combined object
    (`deTurckLieCoeffField + lieCorr0Field`, grad^2 T-free via `tail_base_split`
    + `deTurckLieCoeffField_eq_covDerivArm_add_endoArm`), giving a Psi0 with NO
    grad^2 T top from these two constituents (tighter; needed only if the
    downstream requires literal grad^2-freeness rather than R-free Ktop).
  **Planner must confirm A vs B before session 2.**  If A, the standalone
  producer below is the deliverable.  If B, the deliverable changes to a
  combined deTurckLie+lieCorr0 grad^2-free producer and this standalone brick is
  moot.  (My read: the ratified route is R1tau, which RULING 2 already settled
  accepts positive R-free Ktop per constituent, so A is consistent — but the
  `LieCorr0Split.md` H3 warning is explicit enough to warrant the confirmation.)

### Session-2 entry plan (assumes OPTION A + a downstream home).

In the new leaf, `lieCorr0Field_realizedFam_jetL2_perOrder_topSeparated`
(g0 g_bg free; T,T',s realizedFam; top window i+2; shape = the deTurckLie
sibling at :739 verbatim):
1. `lc0_decomp` -> 4 pieces; split `lc0Insert g0 g1 g_bg = lc0Insert g0 g1 g0
   + (lc0Insert g0 g1 g_bg - lc0Insert g0 g1 g0)` (5 summands).
2. n-way pointwise triangle `‖grad^i (sum of 5)‖^2 <= 5 * sum ‖grad^i piece‖^2`
   (generalize `normSq_iCG_deTurckLieCoeff_le`, `DeTurckLieCoeffL2JetBound.lean
   :714`, from 2-way to 5-way; `iteratedCovGrad_add` + an `sq_le` fan-out).
3. TOP summand `lc0Insert g0 g1 g0 = -deTurckLieDLbCoeffField g0 g1 g0` ->
   DLb field producer at g_bg:=g0, `Ktop = Ktop_DLb` (R-free).
4. Four Kc summands: lift `vb_refold`/`amix_refold`/`riem_refold`/`insert_diff`
   pointwise `rfns` bounds via the tame-window integrator (ball-uniform, R in Kc
   only) — the DLa/DLb field-lift template (`jetL2` of a pointwise `rfns`
   top-sep with Ktop=0 on these).
5. `Ktop = 5 * Ktop_DLb` R-free; single combined `Kc`.  Summed endpoint via the
   `jetL2_sum_lowShift a 2 3` pattern (both windows a+3), re-derived privately
   (it is private upstream).
Estimated ~1-2 sessions (top engine + low pointwise machinery both pre-built;
the work is jetL2 lifting + realizedFam threading + the 5-way triangle + summed).

### Verification status
None — no Lean written this session (stopped at recon for the two rulings).
`(N)` `ricci_flow_unif_existence` still **0%**; this constituent's producer is
0% built (recon + entry plan only).

### CORRECTION (2026-07-24, build phase) — the "pre-built machinery" premise was FALSE-GREEN.

After rulings 1+2 were accepted (№19) and the build started, the new leaf
`TensorHilbert/LieCorr0CoeffL2JetBound.lean` could not be checked: the imported
`LieCorr0Split` / `LieCorr0LowJet` **fail `lake build`** (lakefile
`autoImplicit false`).  They are `lake env lean` FALSE-GREENs — the recon's
claim that the low machinery "already exists / focused-checked per its `.md`"
rested on the `.md`s' own autoImplicit-true focused checks, NOT a real build.
`LieCorr0Split` fix is ONE line (`open DifferentialGeometry.Integral.L2`; all 8
errors are `SmoothCcTensor`/`.ext`).  `LieCorr0LowJet` has the open but is
unbuilt (unknown residual depth).  BLOCKS the ratified plan until repaired; both
files are outside the authorized editable set -> planner scope ruling requested.
Details in `TensorHilbert/LieCorr0CoeffL2JetBound.md`.
