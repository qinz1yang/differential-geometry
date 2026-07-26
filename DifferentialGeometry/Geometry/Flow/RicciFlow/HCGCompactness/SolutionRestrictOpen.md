# SolutionRestrictOpen.lean — Brick 1 of the P4 conv engine

**Goal (Brick 1):** the missing transport link `solutionOn_restrictOpen` +
`isSolutionOn_restrictOpen` — restrict a Ricci-flow solution `S` on `M` to an open
submanifold `U`, giving a solution on `U` with `family.metric t = (S.metric t).restrictOpen U`
and all 9 `IsSolutionOn` fields. Mirrors `SolutionPullback.lean` field by field, but along the
open inclusion `U ↪ M` instead of a global diffeomorphism `Φ : M ≃ₘ N`.

## Status

- **Chunk 1 — curvature germ-locality (DONE, focused check green):**
  - `ricciTensor_restrictOpen` — Ricci unchanged by restriction. Mirrors `ricciTensor_pullback`:
    orthonormal-basis trace (`ricciTensor_eq_orthonormal_trace`) → per-term `Rm04` via
    `metricRm04StdAt_eq_inner_riemannOp` → banked `metricRm04StdAt_restrictOpen` → back. No
    `mfderiv`: the tangent vectors are literally shared (`TangentSpace I (x:U) ≡ TangentSpace I ↑x ≡ E`).
  - `metricRicci_restrictOpen_eval` — bundled `(0,2)` Ricci section restricts.
  - `metricScalarAt_restrictOpen` — scalar curvature unchanged. Mirrors `metricScalarAt_pullback`
    (`metricTracePair0SAt_eq_sum_basis` + `ricciTensor_restrictOpen`).
  - Instances: carries `[BoundarylessManifold I U]` as a hypothesis (needed by
    `metricRm04StdAt_eq_inner_riemannOp`; NOT auto-derived for opens — Brick 2's call site must
    supply it, same as it must for `solutionOn_pullback`). `IsManifold I ∞ U` IS auto (global
    Opens instance), so only `[IsManifold I 1 U] [IsManifold I ((∞)+1) U]` are explicit, matching
    `metricRm04StdAt_restrictOpen`.

- **Chunk 2 — the 9-field assembly (DONE, sorry-free; targeted build green; `#print axioms
  isSolutionOn_restrictOpen` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):**
  - `solutionOn_restrictOpen S U : SolutionOn (M:=U) D` with `base.metric t = (S.metric t).restrictOpen U`.
  - `metricRm04_restrictOpen_eval` — `(0,4)` analog of `metricRicci_restrictOpen_eval`
    (`metricRm04_apply`/`metricRm04StdAt_apply` bridge + `metricRm04StdAt_restrictOpen`), flavor-safe
    `have hcmm := congrArg _ (…)`/`exact (…).symm` pattern (NOT `rw`).
  - Per-field theorems mirror `SolutionPullback`: `metricVariationEquation_restrictOpen`,
    `scalar_restrictOpen`/`scalarCont_restrictOpen`/`scalarTime_restrictOpen`,
    `ricciCont_restrictOpen`/`rm04Cont_restrictOpen` (via new `Tensor0SFamilyContinuousOnSet.restrictOpen`
    + eval lemmas), `ricciNorm_restrictOpen` (via banked `normSq0S_restrictOpen_apply` — takes ONE
    section `A`, so rewrite the Ricci section with `ext`+`metricRicci_restrictOpen_eval` FIRST),
    `ricciNormSpace_restrictOpen`/`ricciNormGrad` (DIRECT: `normSq02_smooth` + `gradientFun_mdiffAt`,
    no transport), `smoothConnection_restrictOpen` (DIRECT: `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative`).
  - `metricFamilySmoothOn_restrictOpen`: `coeff`/`coeff_cont` are LITERALLY `hS.smoothMetric.coeff ↑x X Y`
    (restrictOpen_inner is `rfl`); `metricTensor_cont` via `Tensor0SFamilyContinuousOnSet.restrictOpen`;
    `frameCompSmooth` via `frameCompSmooth_restrictOpen`.

- **The crux sub-lemma — `Tensor0SFamilyContinuousOnSet.restrictOpen`** (added to
  `Curvature/Realized/MetricFamilyContinuity.lean` next to `.pullback`; needs one new import
  `Geometry/Metric/OpenSubtype`): direct restriction-analog of `.pullback` along the open inclusion,
  `tensor0SFamilyContinuousOnSet_of_chartBasisComp` on `U` + `hA.eval_continuous` with base `↑x` and
  slots pushed by `mfderiv Subtype.val` (= id), collapsed by `mfderiv_subtype_val_apply`.
  Pin `contMDiff_subtype_val (n := ∞)` for `continuous_tangentMap (by simp)`; final goal is
  `A .. (fun i =>…) = A .. (fun k =>…)` (alpha) — `simp only [Set.restrict_apply, mfderiv_subtype_val_apply]`
  does NOT close it, needs a trailing `rfl`.

- **The frame-transfer — `frameCompSmooth`** (hardest; `isLocalFrameOn_restrictOpenPush` +
  `restrictOpenPush_contMDiffWithinAt` + `frameCompSmooth_restrictOpen`): build the pushed M-frame
  `frameM k y := if h:y∈U then frame k ⟨y,h⟩ else 0` on `Subtype.val '' u ⊆ M`, apply
  `hS.smoothMetric.frameCompSmooth frameM`, precompose with `ρ(t,x)=(t,↑x)`, collapse `frameM ↑x = frame x`.
  The frame SMOOTHNESS field (`restrictOpenPush_contMDiffWithinAt`) is the real work: express
  `T% frameM i = tangentMap Subtype.val ∘ (T% frame i) ∘ cor` where `cor : M → U` is the
  corestriction `y ↦ ⟨y, ·⟩` padded with `default` (needs `Inhabited U := ⟨x⟩`). `cor` is C∞ at `↑x`
  via `contMDiffAt_subtype_iff` (its `Subtype.val`-precomposition is `id` on `U`), then
  `ContMDiffWithinAt.comp` + `congr_of_eventuallyEq`. See gotchas below.

## KEY GOTCHA: TangentSpace flavor breaks `rw` (U-point vs M-point)

`x : U` and `↑x : M` give `TangentSpace I x` vs `TangentSpace I ↑x`, both defeq to `E` but
tracked SEPARATELY by elaboration. A compound term like `vec2 (basis i) (basis j)` gets its
flavor fixed by the EXPECTED argument type at each site: as an argument to a U-tensor it is
U-flavored, to `_ ↑x` it is M-flavored. So `rw [h]` where `h`'s side was elaborated at one flavor
FAILS to match an occurrence at the other flavor ("did not find instance of the pattern", or a
`simp`/`rw` silently rewriting only one side). Hit this three times in chunk 1.

**Robust pattern (use everywhere U/M points are mixed):**
- Close the final equality with `exact`/`congrArg`, which unify up to defeq, NOT `rw`.
- Convert `metricRicciAt _ _ (vec2 v w) = ricciTensor _ _ v w` via a standalone
  `have e := metricRicciAt_apply_eq_ricciTensor …` (the `:=`/`exact` absorbs the flavor
  difference), then `rw [e]` on the clean statement.
- For `slots = vec2 (slots 0) (slots 1)`, feed it through
  `congrArg (metricRicciAt … x) (by funext i; fin_cases i <;> rfl)` rather than `rw [hs]` —
  a bare `rw [hs]` also rewrites the `slots` INSIDE `slots 0`/`slots 1`.

## Chunk-2 gotchas (frame transfer / bundle typing / Decidable)

- **`Decidable (y ∈ U)` for the `dite` frame.** The pushed frame `if h:y∈U then frame k ⟨y,h⟩ else 0`
  needs `Decidable (y ∈ U)` at ELABORATION (it is in the theorem STATEMENT, not just the proof).
  A file-level `open scoped Classical` works but trips the `linter.style.openClassical` warning.
  Fix: `open Classical in` immediately BEFORE each theorem's docstring (`restrictOpenPush_contMDiffWithinAt`,
  `isLocalFrameOn_restrictOpenPush`); for `frameCompSmooth_restrictOpen` the `dite` is inside a tactic-mode
  `set`, so a leading `classical` tactic suffices. (Both give `Classical.propDecidable`, defeq, so the
  `set frameM` and the `isLocalFrameOn_restrictOpenPush` output unify.)
- **Bundle-flavor pinning in `restrictOpenPush_contMDiffWithinAt`'s statement.** Writing the section as
  bare `T% (fun y:M => if … else 0)` makes Lean infer the TRIVIAL bundle `Trivial M E` (because `0 : E`),
  not `TangentSpace I`, → a type mismatch against the `IsLocalFrameOn.contMDiffOn` field. Fix: write it
  explicitly `fun y:M => TotalSpace.mk' E (E := fun z:M => TangentSpace I z) y (if … else 0)`.
- **`cor` corestriction `M → U` smoothness.** `cor y := if h:y∈U then ⟨y,h⟩ else default` (needs
  `haveI : Inhabited U := ⟨x⟩`). `ContMDiffAt I I ∞ cor ↑x` via
  `rw [← contMDiffAt_subtype_iff (U:=U) (x:=x)]` then the reduced goal `(fun z:U => cor ↑z) = id`
  is closed by `funext`+`hcorval` (`cor ↑z = z` for all `z:U`); do NOT use `.congr` on `contMDiffAt_id`
  directly (its `ChartedSpace` stays a metavar) — `rw [hid]; exact contMDiffAt_id` instead.
- **`tangentMap`/`TotalSpace` equality at the collapse.** `tangentMap Subtype.val ⟨⟨z,hz⟩, v⟩ = ⟨z, mfderiv Subtype.val ⟨z,hz⟩ v⟩`.
  `TotalSpace.mk'_snd` does NOT exist; `TotalSpace.ext rfl …` leaves an `HEq`-ish snd goal that `simp` won't
  close. Robust: two `show`s pinning `tangentMap`→`TotalSpace.mk'` form, then `rw [mfderiv_subtype_val_apply]`.
- **`ContMDiffWithinAt.congr_of_eventuallyEq (h) (h₁ : f₁ =ᶠ f) (hx : f₁ x = f x)`** — the `.comp` result is
  `f`, the target section is `f₁`, so both the eventual-eq and the point-eq go `target = g∘cor` (use `.symm`
  of your `(g∘cor) z = target z` helper).
- **`ContMDiffWithinAt.comp x hg hf`** needs `hg` AT `f x = cor ↑x`; provide `hpush'` at `cor ↑x` via
  `rw [hcorval x]; exact hpush` (the point `cor ↑x` is only propositionally `x`).

## Chunk-2 plan (9 fields; model = `SolutionPullback.isSolutionOn_pullback`)

`solutionOn_restrictOpen S U : SolutionOn (M:=U) D` with
`base := { metric := fun t => (S.base.metric t).restrictOpen U }`. U-instances via hypotheses
(match `metricRm04StdAt_restrictOpen`); NO `letI` gymnastics in the lemma itself (that's Brick 2's
`ofRestrictPullback` job).

Field-by-field (DIRECT = from the restricted metric's own smoothness; TRANSPORT = via chunk-1
lemmas + inclusion; NEW = needs a new restriction lemma):
- `smoothMetric` (MetricFamilySmoothOn U): `coeff`/`coeff_cont` transport (t-function is literally
  `hS.smoothMetric.coeff ↑x X Y` via `restrictOpen_inner`); `metricTensor_cont` NEW
  (`Tensor0SFamilyContinuousOnSet.restrictOpen`); `frameCompSmooth` NEW (frame-transfer along the
  open inclusion — a C∞ frame on `u ⊆ U` transports to a C∞ frame on `Subtype.val '' u ⊆ M`).
- `smoothConnection`: DIRECT — `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
  ((restrictOpen metric) t)` (exactly `smoothConnection_pullback`).
- `equation`: TRANSPORT — coeff `∂ₜ` is the same function (restrictOpen_inner rfl); Ricci via
  `metricRicci_restrictOpen_eval`/`ricciTensor_restrictOpen`; then `hS.equation t ↑x`.
- `scalarCont`/`scalarTime`: TRANSPORT — `metricScalarAt_restrictOpen` + compose with the
  continuous inclusion `(t,x) ↦ (t, ↑x)` / `hS.scalarTime … ↑x`.
- `ricciCont`/`rm04Cont`: NEW — `Tensor0SFamilyContinuousOnSet.restrictOpen` +
  `metricRicci_restrictOpen_eval` / a new `metricRm04_restrictOpen_eval` (bundled `(0,4)` section,
  analogous to `metricRicci_restrictOpen_eval` using `metricRm04StdAt_restrictOpen`).
- `ricciNormSpace`: DIRECT — `ricciNorm (restrictOpen S) t` is C∞ on U (`normSq02_smooth`),
  so `MDifferentiableAt` at every x (simpler than the pullback's chain-rule route).
- `ricciNormGrad`: DIRECT — copy `isSolutionOn_pullback`'s field: `normSq02_smooth` (restricted
  metric's own `|Ric|²`) + `gradientFun_mdiffAt`. NO gradient transport needed.

**The two genuinely-new sub-lemmas (crux of chunk 2):**
1. `Tensor0SFamilyContinuousOnSet.restrictOpen` — model = `.pullback`
   (`Curvature/Realized/MetricFamilyContinuity.lean:217`, via
   `tensor0SFamilyContinuousOnSet_of_chartBasisComp` + `hA.eval_continuous`). For the inclusion:
   either mirror chartBasisComp (chart-basis on U = chart-basis on M restricted) OR use that the
   open-subtype tensor-bundle total space embeds and `U-map = (M-map) ∘ (id × ↑)`.
2. `frameCompSmooth` frame-transfer along `U ↪ M` (a C∞ local frame on U → C∞ local frame on the
   image open set in M; the open inclusion is a local diffeo, so this is a restriction-analog of
   `IsLocalFrameOn.pushforward`).
Plus the small `metricRm04_restrictOpen_eval`.
