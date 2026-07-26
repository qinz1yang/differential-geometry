# MetricLeviCivitaReconcile.lean — notes

Date: 2026-06-13. Verification: focused `lake env lean` GREEN, **0 `sorry`, 0 warnings**.
Stage 1 of the Koszul-canonicalization is COMPLETE — the tensoriality-bridge sorry is closed
and `metricRicciAt_apply_eq_ricciTensor` is now hypothesis-free. See memory
`levicivita-canonical-koszul`.

## 2026-06-13 update — Stage 1 done (sorry closed, bridge hypothesis-free)

- **`leviCivita_contMDiffCovariantDerivativeLocally g`** ADDED — canonical producer of
  `ContMDiffCovariantDerivativeLocally (LeviCivita g) ∞`, transferred from `metricCov_smooth`
  across `leviCivitaConnectionOfMetric_apply_eq_leviCivita`. Use this instead of carrying that
  predicate as a hypothesis anywhere.
- **`riemannCurvatureAux_tangentConst_eq_riemannOp`** — the former frontier is PROVED (the
  de-privatization below is done). Now takes `[ContMDiffCovariantDerivative cov ∞]` (for `riemannOp`
  in the conclusion) + `(hcov : …Locally cov ∞)` (for the proof).
- **`metricRicciAt_apply_eq_ricciTensor`** — `hcov₂` hypothesis DROPPED; supplies the producer
  internally. Fully hypothesis-free + sorry-free.
- `Riemann/Basic/Sections.lean`: `exists_contMDiffSection_eventuallyEq_tangentConstAt` and
  `connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst` de-privatized.
- `Connection/LeviCivita/Defs.lean`: WARNING docstring on `LeviCivita` (prefer `metricCov`).

Lean lessons (failures hit, ~3 build cycles): (1) an instance needed by a constant in the
**conclusion** (`riemannOp`) must be a signature arg, not a body `haveI`. (2)
`ContMDiffCovariantDerivativeLocally`'s set arg is strict-implicit `⦃u⦄`: `hcov isOpen_univ`, not
`hcov Set.univ isOpen_univ`. (3) annotate `of_le`/`mdifferentiableAt` intermediate levels
(`(1 : WithTop ℕ∞)`) or get metavars `?m ≤ ∞` / `¬ ?m = 0`.

Stage 2 (remaining): redefine `LeviCivita g := leviCivitaConnectionOfMetric g`; only `Defs.lean`
internals break (→ one-liners via Koszul facts); this producer becomes near-`rfl`.

---
### Historical (pre-Stage-1) notes below — kept for the proof-route detail.

Date: 2026-06-13. Verification: focused `lake env lean` GREEN, **exactly one `sorry`**
(the tensoriality bridge `riemannCurvatureAux_tangentConst_eq_riemannOp`, line ~128).

## What this file delivers

The curvature/Ricci lift of the Levi-Civita reconciliation
(`Connection/LeviCivita/Reconcile.lean`), bridging the project's TWO curvature worlds:

- `metricRicciAt g` / `metricRm13At` (Koszul `metricCov = leviCivitaConnectionOfMetric`,
  drives a folder-level `SolutionOn.ricci`).
- `ricciTensor g` / `riemannOp` (stitched `LeviCivita g`, drives the chart bridges
  `ricciTensor_chartBasisVec_alpha_eq` etc.).

Public theorems (in dependency order):

1. **`connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita`** (sorry-free) — the
   connection-curvature FIELD of the two LC connections agree on smooth `∞`-sections.
   Proof: `covApply`-agreement via the reconciliation on diff `Z`; `MDiffAt (∇_Y Z)` via the
   PUBLIC `cov_smooth_apply_contMDiffAt` (`Riemann/Basic/Field.lean:171`, takes `∞`-sections,
   derives `∞+1` internally — NO `∞+1` sections needed); `show riemannSec … ; unfold riemannSec`
   + `rw` the three terms.  Takes a new `hcov₂` arg (LeviCivita Locally-smoothness).
2. **`riemannCurvatureAt_lcOfMetric_eq_leviCivita`** (sorry-free) — the pointwise `(1,3)`
   Riemann tensors agree.  Proof: `tensorRSSpace_ext (𝕜:=ℝ) 1 3 x` + `ContinuousMultilinearMap.ext`
   (NB: `ext` does NOT fire on the `Tensor13At` abbrev; must `apply tensorRSSpace_ext` with
   `open Tensor0SBundle`), extend the 3 inputs to global `∞`-sections via
   `exists_eq_at (n := (⊤:ℕ∞))` (gives `↑⊤ = (∞:WithTop ℕ∞)`-sections), `riemannCurvatureAt_apply_smooth`
   (uses `∞`-sections) on both sides, close by step 1 via `congrArg _`.
3. **`ricciCurvatureAt_leviCivita_apply_eq_ricciTensor`** (sorry-free modulo the bridge) —
   contraction-Ricci = trace-Ricci as scalars.  `ricciCurvatureAt_eq_trace` +
   `ricciFromRm13At_apply_basis_trace (chartModelBasis E)` + `ricciTensor_apply_basisSum`,
   then `Finset.sum_congr`; per term `riemannCurvatureAt_apply_const` (keeps the goal's exact
   `(chartModelBasis E) a`, NO extension/coercion mismatch) + the bridge +
   `cotangentToDual_dualToCotangent_gen` + `Module.Basis.coord_apply` + `rfl`.
4. **`metricRicciAt_apply_eq_ricciTensor`** (sorry-free modulo the bridge) — THE BRIDGE
   `metricRicciAt g x (vec2 v w) = ricciTensor g x v w`.  Chains step 2 (via a `have key`
   typed with `metricCov`, defeq-accepted) + step 3.

## The single remaining frontier (fill-ready)

**`riemannCurvatureAux_tangentConst_eq_riemannOp`** : `riemannCurvatureAux cov (const X)(const Y)
(const Z) x = riemannOp cov x X Y Z`  (`[ContMDiffCovariantDerivative cov ∞]`).

True by curvature tensoriality.  3-line fill once unblocked:
`riemannCurvatureAux (const) = crf (const)` (rfl, `riemannCurvatureAux_eq_connectionRiemannCurvatureField`);
`crf (const) x = crf (smoothExt) x` via `connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst`
(+ `exists_contMDiffSection_eventuallyEq_tangentConstAt` for the witnesses); `crf (smoothExt) x =
riemannSec (smoothExt) x = riemannOp x X Y Z` via `riemannOp_apply_smooth`.  `Locally cov ∞` for the
middle lemma is derivable from the `[ContMDiffCovariantDerivative]` instance (`.contMDiff.mono`).

**BLOCKER:** `exists_contMDiffSection_eventuallyEq_tangentConstAt` (`Riemann/Basic/Sections.lean:22`)
and `connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst` (`Sections.lean:67`)
are `private`.  `connectionRiemannCurvatureField_congr_point` (`Field.lean:939`, PUBLIC) cannot
substitute — it needs global `∞`-`ContMDiffSection`s, and `tangentConstAt` is only locally smooth.

**UNBLOCK (smallest):** de-privatize those two lemmas in `Sections.lean` (remove `private`),
targeted-build `+…Riemann.Basic.Sections`, then fill the bridge with the 3-line chain above.
(Not done here: another agent held the global Lake build lock; editing the shared upstream
`Sections.lean` during their build is unsafe in multi-agent mode.)

## Key gotchas (cost ~the whole session)

- `cov_smooth_apply_contMDiffAt` (public, Field:171) is the right `∞`-covApply-smoothness — it
  AVOIDS the `∞+1`-section trap.  `covApply_mdifferentiableAt_local` needs `∞+1`, but
  `exists_eq_at`/`_gen` are `{n : ℕ∞}` (max `⊤=∞`) and CANNOT build `(∞:WithTop ℕ∞)+1`-sections.
  Re-stating step 1 over plain `∞`-sections via `cov_smooth_apply_contMDiffAt` is what makes
  step-2's `exists_eq_at`-extensions feed step 1.
- `riemannCurvatureAt` lives in `…Integral.Connection.CovariantDerivative` → need `open CovariantDerivative`.
- `chartModelBasis` lives in `…Integral.Measure` → need `open …Measure`.  This ALSO makes
  `tangentConstAt` ambiguous (Field's `CovariantDerivative.tangentConstAt` vs KoszulFormula's
  `Connection.tangentConstAt`); qualify the bridge's args as `CovariantDerivative.tangentConstAt`.
- The basis-trace term-bridge MUST use `riemannCurvatureAt_apply_const` (keeps the goal's exact
  `(chartModelBasis E) a`).  Extending the basis vector to a section (then `rw`) fails with a
  `(chartModelBasis E) a` coercion-form mismatch (the extended-section `Ba x` vs the lemma-produced
  basis vector elaborate differently re E↔TangentSpace).

## Overall project context (honest %)

End goal: `ham3_main` (Hamilton 3D positive-Ricci) ⊃ `ham3_short_isSolution` (short-time `IsSolutionOn`
packaging) ⊃ the `ricciCont`/`rm04Cont` continuity fields, which need `metricRicciAt = ricciTensor`
to transport the existing `ricciChartFrameComp_jointContinuousOn` (stated for `ricciTensor`) onto
`S.ricci = metricRicciAt (g t)`.

- This file (the curvature-world reconciliation bridge): **~90%** — all 4 steps proved, 1 isolated
  fill-ready frontier (privacy-blocked, not math).
- `ricciCont`/`rm04Cont` consumer wiring (keystone `tensor0SFamilyContinuousOnSet_of_chartBasisComp`
  on `S.ricci` + this bridge + the joint-continuity re-export): NOT started (0%).  `rm04Cont` is the
  `(0,4)` analog (needs a `metricRm04 = …` bridge too).
- `ham3_short_isSolution` as a sorry-free theorem: still 0% (unstated/unproved); this bridge is one
  of several `IsSolutionOn` fields' prerequisites.
- Whole HCG/short-time-existence frontier: low single digits.  This bridge is necessary plumbing,
  not the theorem.

## 2026-06-14 local smoothness cleanup

The stitched `LeviCivita` connection is now definitionally the Koszul metric
connection in this checkout.  The reconcile file was simplified accordingly:
the local-smoothness producer is a direct `metricCov_smooth` specialization, and
the public curvature/Ricci reconcile intermediates no longer take `hcov`
parameters.

Verification passed for the edited file.
