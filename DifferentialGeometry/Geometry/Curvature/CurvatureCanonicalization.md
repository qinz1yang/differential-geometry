# Curvature canonicalization — item-3 plan + de-duplication punch-list

Owner of this plan: the inventory/planning session. **Executor: the session doing the
LeviCivita→Koszul collapse** (item 1/3 workstream). This doc is the roadmap; do not run two
editors on the curvature-core files concurrently.

## Goal

Collapse the project's curvature representations onto **one canonical world**, now that Stage 2
made `LeviCivita g = leviCivitaConnectionOfMetric g` defeq (`Connection/LeviCivita/Defs.lean`).
The duplication is NOT ~80 redundant defs — it is **one 2× split** (Koszul vs stitched-LeviCivita)
across the fundamental objects, plus a handful of low-use variants. Most "representations" are
legitimate distinct views (chart vs intrinsic, (0,4) vs (1,3), section vs pointwise, component,
∇ᵏ, realization predicate) and stay — they just each need a canonical `_eq` bridge.

## Canonical decision: the **Koszul** world

`metricRicciAt` / `metricRm04At` / `metricRm13At` / `metricScalarAt` (`Geometry/Curvature/Metric.lean`)
are canonical. Rationale: every `SolutionOn` already uses them (`S.ricci = metricRicci`,
`S.base.rm04`, `S.scalar = metricScalarAt`); they are the direct Koszul construction with the
local-smoothness producer; and post-Stage-2 the stitched-LeviCivita objects are *provably equal
views* of them, not a parallel world.

## Inventory (fundamental objects → representation count)

- **Ricci**: 2 fundamental (`ricciTensor` stitched-LC, `metricRicciAt` Koszul) → ~25–30 reps.
- **Rm**: 4 fundamental (`metricRm04At`/`metricRm13At` Koszul, `riemannCurvature04At`/`riemannCurvatureAt`
  stitched-LC) → ~40+ reps.
- **Scalar**: **1 fundamental** (`metricScalarAt` = `metricTracePair0SAt g (metricRicciAt g x)`, the trace of the
  canonical Koszul Ricci) → ~15 reps. **CORRECTION 2026-06-14:** there is NO separate stitched-LC scalar def
  (grep: no `scalarCurvatureAt` = trace of `ricciTensor`). The other "scalar" entries are frame-trace VIEWS
  (`scalarFromRicciTraceInFrame`, `Basic.lean:150`) and realization PREDICATES (`ScalarRealizesRicciTrace*`),
  not a parallel construction — so the scalar needs NO two-worlds bridge; it is already single-canonical.
  (`S.scalar` accessor = `metricScalarAt`.) Bucket-C work for the scalar = ensure one canonical trace lemma for
  the frame views, not a `_eq`-to-Koszul bridge.
- Total ≈ **8 fundamental objects, ~80 representations**; the 2× everywhere is the collapsible split.

## Classification + punch-list

### A. SHIM — the two-worlds bridges (post-Stage-2 defeq; the active session's core work)

Make these `rfl`/one-line and reduce the reconcile files to thin shims. Pick the Koszul side as
the definition; keep the stitched-LC name as a **`@[deprecated]`-or-docstring-WARNING'd compat
alias** that points to the canonical (see [[levicivita-canonical-koszul]] for the transition rule).

| stitched-LC (demote to view of…) | …canonical Koszul | bridge lemma |
|---|---|---|
| `ricciTensor g x v w` | `metricRicciAt g x (vec2 v w)` | ✅ `metricRicciAt_apply_eq_ricciTensor` (hypothesis-free) |
| `riemannCurvature04At (LeviCivita g)` | `metricRm04At` | ✅ **DONE 2026-06-14** `metricRm04At_eq_riemannCurvature04At` (`MetricLeviCivitaReconcile.lean`; `unfold riemannCurvature04At; rw [key]` over the connection-level agreement) |
| `riemannCurvatureAt (LeviCivita g)` (1,3) | `metricRm13At` | ✅ **DONE 2026-06-14** `metricRm13At_eq_riemannCurvatureAt` (`MetricLeviCivitaReconcile.lean`; = `riemannCurvatureAt_lcOfMetric_eq_leviCivita` since `metricRm13At` is by def the Koszul `riemannCurvatureAt`) |
| `Reconcile.lean` / `MetricLeviCivitaReconcile.lean` | — | collapsed to `simp [LeviCivita]` / `rfl` |

**Bucket A is now COMPLETE** (2026-06-14): all three two-worlds objects (Ricci, (0,4) Rm, (1,3) Rm) have a sorry-free,
hypothesis-free `_eq` bridge from the canonical Koszul object to the stitched-`LeviCivita` view. Note `riemannCurvature04At`/
`riemannCurvatureAt` are the GENERIC curvature-of-a-connection functors (parametrized by `cov`); the "stitched-LC world" is
them applied to `LeviCivita g`, and the "Koszul world" (`metricRm04At`/`metricRm13At`) is them applied to `metricCov g` — the
bridges are exactly the connection-substitution `metricCov g ≡ leviCivitaConnectionOfMetric g` lifted through the curvature
functors. Verified: focused check green + targeted build green (warning-free).

`riemannOp`/`riemannSec`/`connectionRiemannCurvatureField`/`riemannCurvatureAux` are the
**curvature-OPERATOR API** — keep (they are the bundled-operator layer `ricciTensor` is built from),
but they now agree with the Koszul curvature; ensure the `riemannOp ↔ metricRm` bridge exists.

### B. RETIRE / INLINE — genuinely redundant low-use variants (verify usage, then remove)

Run `grep -rE '\bNAME\b'` first; if the listed consumers can route through the canonical, inline & delete.

| rep | uses | action |
|---|---|---|
| `metricRm04Std` (`Metric.lean:112`) | 1 | ✅ **DONE 2026-06-14** — was dead (only its own `@[simp]` apply lemma referenced it; `metricRm04StdAt` and `metricRm04Std_pullback` are separate). Deleted def + apply lemma. |
| `metricRm04LastDualAt` (`Metric.lean:138`) | 2 | **KEEP** — not a thin wrapper; it's a genuine `Module.Dual` construction (`W ↦ Rm04(X,Y,Z,W)`) with `map_add'`/`map_smul'` proofs and a real consumer (`Metric.lean:654`). Inlining would bloat, not dedup. |
| `rm04ContrCurried` (`ShiftedReaction.lean:1007`) | 2 | **DESCOPE — KEEP** (2026-06-14): a 2-use named CLM helper is a legitimate small abstraction; inlining it CONTRADICTS the "prefer theorem-form/named lemmas over inline rewrites" rule. Revisit only if it's a trivial pass-through. |
| `rm04MidCLMAt` (`ShiftedReaction.lean:922`) | 2 | **DESCOPE — KEEP** (2026-06-14): same as `rm04ContrCurried` — named CLM helper, keep. |
| `metricRm04StdAt` (`Metric.lean:104`) | 10 | KEEP unless the 10 uses are all `Std`-specific (then fold into `metricRm04At`) |
| duplicate `coordinateFrameAt_isLocalFrame_one` (`Geometry/Coordinates/CoordinateFrame.lean:292` in `DifferentialGeometry.Tensor.Coordinates` — canonical, dozens of uses — **vs** `Geometry/Connection/Chart/NablaComponents/Basic.lean:39` in top-level `Coordinates`) | — | **DESCOPE — KEEP SEPARATE** (2026-06-14): the two defs live in DIFFERENT namespaces; the Chart-tree copy keeps the Chart/NablaComponents layer decoupled from the `Tensor.Coordinates` tree. Merging would couple them (possible import cycle) + retarget the Chart consumers, forcing a large rebuild for marginal gain. Intentional decoupling, not redundancy. |
| **duplicate `metricSharp`/`metricFlatLinear`/`metricFlatLinear_injective`** in `Integral.Connection` (`Geometry/Operator/Operators.lean:48,67,105`) **vs** `Integral.DivergenceTheorem` (`Geometry/Operator/Gradient.lean:92,109,161`) | — | same musical-iso value in 2 namespaces; canonical = `Integral.Connection`; remove the `DivergenceTheorem` copies + reroute its consumers. **2026-06-14: this latent dup caused an `Ambiguous term` build break when the Stage-2 `import Torsion` widened the cone; consumers (`Ricci/DualNorm.lean`, `EigenvectorChartCrossRightLimit.lean`) were qualified to `Integral.Connection.*` as the surgical unblock. ✅ ROOT DEDUP DONE + VERIFIED GREEN 2026-06-14 (see B′): `DivergenceTheorem` copies replaced by `export Integral.Connection (…)`; both consumers reverted to unqualified.** |

### B′. Musical-iso block dedup — **✅ DONE + VERIFIED GREEN 2026-06-14**

**Verification:** full `lake-locked build` green — 9910/9910 jobs, exit 0, zero errors. All four touched
files built: `Operators.lean`, `Gradient.lean` (20s), `Ricci/DualNorm.lean`, and
`EigenvectorChartCrossRightLimit.lean` (91s), plus the entire ~1120-module downstream cone of
`Operators.lean`. Confirmed: the `export` resolves all 6 names; `metricFlatMap` is defeq to the exported
`metricFlatEquiv` so `metricSharp_def`/`metricFlatMap_apply` hold by `rfl`; and the `unfold metricSharp`
sites in Connection-namespace files (`Scaling`, `KoszulFormula`, `HamiltonRHS`) are unaffected (they
resolve to the real def, not the alias). Lean's `export` alias is followed to the canonical constant by
tactic name-resolution, so no consumer `unfold`/`simp [metricSharp]` broke.

**Gotcha recorded:** a `/-- … -/` doc-comment CANNOT precede the `export` *command* (it expects a
declaration keyword) — use a plain `/- … -/` block comment. This caused the first build to fail at
`Gradient.lean:97`; fixed by downgrading the doc-comment.

**Status:** the export-based consolidation below was carried out. Edits made:
1. `Operators.lean` (`Integral.Connection`): added `inner_metricSharp_right` (theorem, after `inner_metricSharp`) — pure addition; canonical sharp-symmetry lemma.
2. `Gradient.lean` (`Integral.DivergenceTheorem`): `import …Geometry.Operator.Operators`; replaced the duplicate
   `metricFlatLinear`/`_apply`/`_injective` defs with `export DifferentialGeometry.Integral.Connection
   (metricFlatLinear metricFlatLinear_apply metricFlatLinear_injective metricSharp inner_metricSharp
   inner_metricSharp_right)`; **deleted** the duplicate `metricSharp`/`inner_metricSharp`/`inner_metricSharp_right`
   defs (they collided with the export). Kept `metricFlatMap` unchanged — its `linearEquivOfInjective` body now
   references the *exported* (Connection) `metricFlatLinear`/`_injective`, making it defeq to Connection's
   `metricFlatEquiv`, so `metricFlatMap_apply`/`metricFlatMap_apply_symm`/`metricSharp_def` stay valid by `rfl`.
   Made `gradFun_eq_zero_of_mfderiv_eq_zero` alias-robust (`rw [gradFun_def, metricSharp_def]` instead of
   `unfold metricSharp`, since the exported `metricSharp` is an alias).
3. Reverted the surgical `Integral.Connection.*` qualifications in `Ricci/DualNorm.lean` (`metricSharp`×2,
   `inner_metricSharp`, `metricFlatLinear_injective`) and `EigenvectorChartCrossRightLimit.lean`
   (`metricFlatLinear`/`_apply`/`_injective`, 7 spots) — unqualified now dedups to the single Connection decl.
   NOTE: the qualified `Integral.Connection.metricSharp`/`inner_metricSharp` in `Metric.lean:640,647` and the
   `…Connection.gradientAt/gradientFun/metricSharp` in `HamiltonRHS.lean:644` are PRE-EXISTING (not the band-aid)
   and were left as-is (those files may not open both namespaces).

**Pre-flight check (done):** a 1-decl scratch experiment confirmed Lean `export` makes `B.foo` resolve to the
SAME `Name` as `A.foo`, so `open A; open B; foo` is NOT ambiguous (alias dedup) — validating the mechanism.

---

#### Original plan (for reference)


`Geometry/Operator/Gradient.lean` (`Integral.DivergenceTheorem`) re-implements, **verbatim**, the
musical-iso block of `Geometry/Operator/Operators.lean` (`Integral.Connection`) — identical defs of
`metricFlatLinear`, `metricFlatLinear_apply`, `metricFlatLinear_injective`, `metricSharp`,
`inner_metricSharp` (the only naming diff: Gradient's `metricFlatMap` = Operators' `metricFlatEquiv`).
The two `metricSharp`/`metricFlatLinear` are NOT defeq (built via `metricFlatMap` vs `metricFlatEquiv`,
separate `def`s), so when a file `open`s both namespaces the SHARED names are `Ambiguous term`.

**Shared names (the clash):** `metricFlatLinear`, `metricFlatLinear_apply`, `metricFlatLinear_injective`,
`metricSharp`, `inner_metricSharp`.  **DivergenceTheorem-only (no clash):** `metricFlatMap`,
`metricFlatMap_apply`, `metricFlatMap_apply_symm`, `metricSharp_def`, `inner_metricSharp_right`, `gradFun…`.

**Plan (canonical = `Integral.Connection`):**
1. `Operators.lean`: add `inner_metricSharp_right` (copy of Gradient:176) — pure addition.
2. `Gradient.lean`: `import …Operator.Operators`; **delete** the 5 shared dups (+ the two `private`
   `metricFlatLinear_finrank_eq`/`tangentSpace_finiteDimensional`); add
   `export DifferentialGeometry.Integral.Connection (metricFlatLinear metricFlatLinear_apply
   metricFlatLinear_injective metricSharp inner_metricSharp inner_metricSharp_right)`.  Export makes
   `DivergenceTheorem.X` resolve to the SAME declaration as `Connection.X`, so opening both is no longer
   ambiguous (same decl) AND every existing `DivergenceTheorem.X` consumer keeps working.
3. Keep DivergenceTheorem-only names; redefine `metricFlatMap g x := metricFlatEquiv (I:=I) g x`
   (delegate; `metricFlatMap_apply`/`_apply_symm`/`metricSharp_def` follow by `rfl`/`inner_metricSharp`).
   `gradFun` (and all divergence-theorem internals) then use the exported (Connection) `metricSharp` —
   verbatim-identical, so the proofs are unchanged.
4. Revert the surgical `Integral.Connection.*` qualifications in `Ricci/DualNorm.lean` and
   `EigenvectorChartCrossRightLimit.lean` (no longer needed once unqualified resolves unambiguously).

**Blast radius (verify before/after):** DivergenceTheorem-exclusive-name consumers (3 files:
`Integration/DivergenceTheorem/Gradient.lean`, `Analysis/Integration/.../GradientLaplacian/Gradient.lean`,
`Connection/ChartBridge/Gradient.lean`) + the ~6 files that open `DivergenceTheorem` and use a shared
musical name.  `gradFun` (heavily used) is UNAFFECTED (stays in DivergenceTheorem; only its internal
`metricSharp` reroutes).  **RISK:** touches the foundational gradient/divergence-theorem layer →
mandatory full build.  **UNCERTAINTY to confirm first:** that Lean `export` actually de-duplicates the
ambiguity (alias → same `Name`); validate with a 1-decl experiment before the full edit.  Best done as a
focused pass (NOT a late-night incremental edit, given the downstream breadth).

### C. KEEP-AS-VIEW — **AUDIT COMPLETE 2026-06-14** (3 parallel Explore agents, by view family)

**Headline: bucket C is largely already OK.** The canonical objects + bucket-A bridges + the existing
view `_apply`/`_eq`/`_realizes` lemmas already cover almost every view. ONE genuine gap found and FIXED
(the explicit metric-level trace ladder); the rest is OK / KEEP-PREDICATE; a few soft MIGRATE candidates
are DEFERRED (low-confidence, involve chart-bridge plumbing + symmetry hypotheses).

**✅ FIXED 2026-06-14 — metric-level canonical trace ladder** (`Metric.lean`, additive `rfl` lemmas):
- `metricRicciAt_eq_trace`: `metricRicciAt g x = ricciFromRm13At (metricRm13At g x)` — the canonical
  "Ricci = trace of (1,3) Rm" at the metric level (was only implicit in the `metricRicciAt`→`ricciCurvatureAt`
  →`ricciFromRm13At` def chain). Focused check + targeted build green.
- `metricScalarAt_def`: `metricScalarAt g x = metricTracePair0SAt g (metricRicciAt g x)` — canonical
  "scalar = metric trace of Ricci" (def restatement, so downstream needn't unfold).

**OK (canonical lemma exists + used; no action):**
- ∇ᵏ tower `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field`/`nablaKRm04Field`: the fixed-k forms are
  DEFINITIONAL specializations of `nablaKRm04Field` (k=1,2,3), each with `_realizes` + an `iteratedRmComp_*_eq_*`
  bridge; the all-k inductive `iteratedRmComp_eq_nablaKRm04Field` subsumes them. **No consolidation needed.**
- Trace views `ricciFromRm13At` (`ricciFromRm13At_eq_contract_trace`), `ricciCurvatureAt`
  (`ricciCurvatureAt_eq_trace`, `@[simp]`, `rfl`) — canonical trace lemmas present.
- Section-level components `ricciComp`/`rm04Comp`/`rm13Comp` (have eval/`_eq` lemmas at the section tier);
  pointwise `ricciCompAt`/`rm04CompAt` already have GENERIC `_apply` lemmas that bridge to any supplied tensor
  (a specialized `_eq_metricRicci` would be redundant). `ricciCompInFrame`/`rm04CompInFrame` DO NOT EXIST.
- Canonical sections `metricRm04`/`metricRm13`/`metricRicci` + `metricRm04StdAt`/`metricRm04LastDualAt`:
  all have `_apply` (`@[simp]`) lemmas — OK.

**KEEP-PREDICATE (realization interfaces, not curvature objects; no bridge needed):**
- `ricciFromRiemann04TraceInFrame`, `scalarFromRicciTraceInFrame`, `scalarCurvatureFromRicciTraceInFrame`
  (frame-trace VIEWS, each with `_apply` + `_realizes`); `DScalarTraceAt/Sec`, `NablaRicTraceAt/Sec`
  (Bianchi differential-identity predicates); `RicciRealizesRm04TraceInFrame`, `ScalarRealizesRicciTraceInFrame`,
  `RicciTensorRealizesRm13Trace`, `ScalarSectionRealizesRicciTraceInFrame`, etc.

**DEFERRED — soft MIGRATE/ADD candidates (low-confidence; revisit only with a concrete consumer):**
- `chartRicciTensor`/`chartRiemannTensor` (`Riemann/Defs.lean`, chart coordinate layer): no `_eq` to
  `metricRicciAt`; a bridge needs the chart-Ricci SYMMETRY hypothesis (`[I.Boundaryless]`). Involved; defer
  until a consumer needs the chart↔intrinsic identity directly.
- `ricciFun` (chart bilin, `Riemann/Defs.lean:150`): bridge `ricciFun_eq_ricciTensor_of_basis_identity` EXISTS
  (`Connection/ChartBridge/Ricci.lean:402`) but reconcile uses `ricciTensor` directly — MIGRATE only if a
  re-derivation site is found.
- `rm13Section`/`rm04Section`/`ricciSection` (bundled sections): bridged via the `CurvatureSectionProducerData`
  realization predicates (`Metric.lean:187-200`), not an explicit `_eq`. The predicate IS the interface;
  add explicit `_eq_metric*` only if downstream re-derives. Soft.

### D. KEEP AS-IS — settled self-contained local algebra (do not touch)

- `ShiftedReaction.lean` contraction cluster (`rm04Mid02At` 25, `rm04RicciContrAt` 9,
  `rm04ContrRightCLM` 8, `rm04OfRic3At` 16, perms): a self-contained dim-3 reaction algebra; settled API.
- `DimensionThree/` 3D forms (`stdRicci3`, `RicciSymAt`, `ricciCovAt`, `displayedRiemannFromRicciRhs3`,
  `ricciEigen*3`, `stdScalar3`): dimension-specialized algebra; keep.

## Bridge-lemma naming convention

`<canonicalName>_eq_<viewName>` (or `<viewName>_eq_<canonicalName>` if the view is the natural LHS),
stated as the pointwise scalar/tensor equality, `@[simp]` only if it is a genuine normal-form move.

## Sequencing

1. ✅ **A DONE 2026-06-14** — two-worlds collapse complete: Ricci + (0,4) Rm + (1,3) Rm bridges all sorry-free
   & hypothesis-free in `MetricLeviCivitaReconcile.lean`; reconcile bodies are `simp [LeviCivita]`/`rfl` shims.
2. ✅ **B DONE/DESCOPED 2026-06-14** — flagship B′ musical-iso dedup landed + full-build verified; remaining
   B items (`rm04ContrCurried`/`rm04MidCLMAt` inlines, duplicate frame lemma) DESCOPED with rationale above
   (keep named helpers; keep the Chart-tree frame decoupling). `metricRm04Std` was deleted earlier.
3. ✅ **C AUDITED + core gap FIXED 2026-06-14** (see "C. KEEP-AS-VIEW — AUDIT COMPLETE" above): all view
   families audited (∇ᵏ tower, trace views, components, sections, chart, realization predicates). Result:
   bucket C was largely already OK; the one genuine gap (explicit metric-level trace ladder) is FIXED
   (`metricRicciAt_eq_trace` + `metricScalarAt_def` in `Metric.lean`, verified). Remaining items
   (chart↔intrinsic bridge, `ricciFun`/section migrations) are DEFERRED — consumer-driven, low-confidence.
4. D is out of scope.

**ITEM-3 SUBSTANTIVELY COMPLETE 2026-06-14.** One canonical Koszul curvature world; all fundamental objects
(Ricci, (0,4) Rm, (1,3) Rm, scalar) canonical with two-worlds bridges; the explicit trace ladder
(scalar→Ricci→Rm) named; all views audited with canonical lemmas. The musical-iso namespace dedup (B′) is
landed + full-build-green. Remaining = only the DEFERRED consumer-driven view migrations.

## Final low-use-variant scan — 2026-06-14 (verdict: NO further retirements; punch-list closed)

A last dedup scan (Explore agent) for additional low-use / redundant curvature defs across
`Geometry/Curvature/**` + `Flow/RicciFlow/**` (names `ricci`/`rm04`/`rm13`/`riemann`/`scalar`/`weyl`/`curv`).
**Result: the genuine redundancies were already removed** (the 2× Koszul/stitched split → bucket A; the
musical-iso dup → B′; `metricRm04Std` → deleted). Every remaining candidate is a LEGITIMATE keeper under the
project rules (settled API / surgical / **prefer named lemmas over inline** / wrappers that preserve a public
endpoint), so retiring them would be churn for negligible gain:

- `scalarCurvatureFromRicciTraceInFrame` (`Realized/Curvature.lean:58`): transparent `abbrev` of
  `scalarFromRicciTraceInFrame` that carries the public "scalarCurvature" name + its `_realizes` realization
  API — KEEP (endpoint-preserving wrapper; `abbrev` is already cost-free).
- `ricciFromRiemann04TraceInFrame`, `scalarFromRicciTraceInFrame` (`Basic.lean:130,150`): frame-trace VIEWS
  whose canonical bridge IS the `*RealizesRicciTrace*` / `*RealizesRm04Trace*` predicate (a frame-trace view
  cannot have an *unconditional* `_eq` to `metricScalarAt`/`metricRicciAt` — it needs the g-orthonormal/frame
  hypothesis the predicate encodes) — KEEP-PREDICATE.
- `curvRicciRicciReactionInFrame`, `curvatureTraceDuAt`, `curvatureActionOnDuCoord`
  (`Bochner/BochnerTensor.lean`, `Bochner/ScalarBochner.lean`): thin NAMED helpers each used by ≥1 same-file
  Bochner simp-lemma/assembly — KEEP (named local abstractions; inlining lengthens the settled Bochner proofs).
- `tensor04OutAt`/`tensor04StdOfOutAt`/`tensor04ToField` (`Tensor.lean`): slot-order convention bridges + the
  section→field view — KEEP (a `tensor04OutAt`→standard-order SHIM would be a separate convention migration
  needing a full Flow-layer slot-order audit; out of scope, not a dedup win).

**Conclusion: the curvature-rep dedup punch-list is CLOSED.** Item-3 (buckets A/B/C) is done; the only open
curvature items are the explicitly-DEFERRED consumer-driven view migrations (chart↔intrinsic `chartRicciTensor`
bridge; `ricciFun`/section `_eq` migrations), to revisit only when a concrete re-derivation consumer appears.

### EVENTUAL CLEANUP TARGETS — soft-deprecated 2026-06-14 (registry)

These are the defs kept ONLY because they have current uses (tolerated redundancy — a transparent alias, a
convention-migration shim, a namespace duplicate).  They are fine now but should get NO new uses and be
removed once their consumers migrate.  Each now carries a **docstring `⚠ SOFT-DEPRECATED` note** at its
definition (we use a docstring WARNING, NOT a hard `@[deprecated]`, to avoid spraying deprecation warnings
across the currently-green settled code that still uses them — the same surgical pattern as the `LeviCivita`
→ `metricCov` transition).  Grep `SOFT-DEPRECATED` to find them.

| def | file | tolerated because | use instead / cleanup |
|---|---|---|---|
| `scalarCurvatureFromRicciTraceInFrame` | `Realized/Curvature.lean` | transparent `abbrev` alias (no math beyond the name) | `scalarFromRicciTraceInFrame` |
| `tensor04OutAt` | `Curvature/Tensor.lean` | output-first slot-order eval, convention-migration artifact | `tensor04StdAt` (standard order); migrate the legacy consumers |
| `coordinateFrameAt_isLocalFrame_one` (local `Coordinates` ns) | `Connection/Chart/NablaComponents/Basic.lean` | 2nd copy kept to decouple the Chart tree | canonical `Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one`; eventual merge |

**NOT soft-deprecated (legitimate keepers, recorded for clarity):** the named CLM/Bochner helpers
(`rm04ContrCurried`, `rm04MidCLMAt`, `curvRicciRicciReactionInFrame`, `curvatureTraceDuAt`,
`curvatureActionOnDuCoord`), `metricRm04StdAt`/`metricRm04LastDualAt`, and `tensor04StdOfOutAt`/
`tensor04StdToOutPerm` (load-bearing in the canonical lowering) are kept because they are GOOD abstractions
or canonical machinery, NOT merely "because used" — so they get no deprecation mark.  If you later want HARD
enforcement on the three above, switch their docstring notes to `@[deprecated (since := …)]` (accepting the
use-site warning spray).

Do NOT start B/C edits on `Metric.lean` / `Reconcile*` / `Core.lean` / `LeviCivita/Curvature/*`
while the active session holds them. Related: [[levicivita-canonical-koszul]], [[framecompsmooth-unconstructible]].
