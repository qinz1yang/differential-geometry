# WindowDataPullback.lean — pullback transport of the `SolWindowData` analytic sub-records

## Maintenance repair (2026-07-17)

`solnEvolField_pullback` now normalizes scalar multiplication at the `(0,2)` tensor-fiber layer
with the canonical fully qualified `Tensor0SBundle.Tensor0SSpace.smul_apply` lemma before applying
`solnRicField_pullback`. This is a proof-normalization repair only: no theorem statement or public
API changed, and focused verification passed. The theorem and its dedicated pullback machinery
remain 100% complete. Project estimates are unchanged: Chapter 4 machinery is about 90%, whole-HCG
machinery about 60%, while the conditional compactness endpoint and unconditional endpoints remain
theorem-level 0%.

End-goal context: `winGInfOfData` (MetricPreconvWindowSolutions.lean) consumes a `SolWindowData`,
which bundles a `SolutionOn` sequence + `IsSolutionOn` (built by `isSolutionOn_pullback`, P1.4) + 5
analytic sub-records.  For the HCG g_∞ assembly (MSM135 Ch4 Thm 3.10 ⇐ 3.9) the flows are recentered
by diffeomorphisms `Φ_k`, so every datum must transport from `N` to `M` along `Φ`.  This file is the
consuming-side companion to `SolutionPullback.lean`.

## Status (2026-06-30, build green 3899, sorry-free) — LAYER COMPLETE

**The entire pullback → `SolWindowData` layer is DONE: all 5 `Sol*Data` records + the keystones +
the capstone `solWindowData_pullback` + the endpoint `winGInfOfPullback`.**  The transport principle
throughout: `Φ` is an isometry between `(M, Φ^*g)` and `(N, g)` (`Diffeomorph.pullbackMetric_inner` —
both metrics evaluate at the same `dΦ v`), so every *ratio*/norm/bound is preserved and the only
bookkeeping is moving spatial sets along `Φ` (compact image / open preimage).

**Capstone:** `solWindowData_pullback (W : SolWindowData (M:=N)) (Φ : M ≃ₘ N) : SolWindowData (M:=M)`
— `cases`/`mk` transporting all 17 fields; compact set via `Φ⁻¹' K = Φ.symm '' K`
(`hK.image Φ.symm.continuous`); `IsSolutionOn` via `isSolutionOn_pullback`; the 5 records via the
`sol*Data_pullback` producers.  **Endpoint:** `winGInfOfPullback hne W Φ := winGInfOfData hne
(solWindowData_pullback W Φ)` — the g_∞ pre-convergence conclusion for a `Φ`-recentered flow.

Keystones (reusable, the mathematically meaningful layer):
- `metricUniformEquivalentOn_pullback` / `…OnWindow_pullback` — equivalence transports, same constant
  (`pullbackMetric_inner` at `v = v`).  Feeds 4 of 5 records.
- `metricCovDerivNorm_pullback` — `metricCovDerivNorm a (Φ^*h) (Φ^*gRef) x = metricCovDerivNorm a h
  gRef (Φ x)`, via `metricCovDeriv_pullback` (the existing tower naturality, eval form) +
  `normSq0S_pullback_eval_of_orthonormal`.  Cov-derivative analog of `ricCovTower_normSq0S_pullback`.
- `metricCovDerivOrderBoundOn_pullback` / `…OnWindow_pullback` — order-`a` bound transport (direct
  from `metricCovDerivNorm_pullback`).

Records (assembly over the keystones + the P1.3 `ricCovTower_normSq0S_pullback`):
- `solLowData_pullback` — global lower control (no set; `Φ` bijection; same `c`).
- `solLip0Data_pullback` — `SolLip0Data` (order-0 Shi via `ricCovTower_normSq0S_pullback`; the `2`
  vs `2+0` rank alignment is handled by ascribing the lemma's type to rank `2`, defeq).
- `solCovData_pullback` — `SolCovData`; the `∀ K' compact` pack is handled by applying the source
  `pack` at the compact image `Φ '' K'` (`IsCompact.image Φ.continuous`) and pulling the witness
  open set back to `Φ⁻¹' U` (`IsOpen.preimage Φ.continuous`); scalar/time conditions unchanged.
- `solLipData_pullback` — `SolLipData`; fixed `K` moves to `Φ⁻¹' K`; lower-order + top-order bounds
  via `metricCovDerivOrderBoundOnWindow_pullback`.
- `solSwapData_pullback` — `SolSwapData`, the time-derivative SWAP (the one non-spatial record).
  Eval helpers `solnMetricField_pullback` (`metricTensorField`+`pullbackMetric_inner`),
  `solnRicField_pullback` (`ricciSection_pullback`), `solnEvolField_pullback`
  (`-2 • solnRicField`, `ContMDiffSection.coe_smul`).  Core: push `V` to `N` via `pushFwdSection`,
  instantiate the source datum at `(pushFwd V, Φ x0)`, convert each `extDerivFun (F_pb s) x V` to
  `extDerivFun (F_source s)(Φ x)(dΦ V)` via `covDerivOfField_pullback` (general base, `hA0` from the
  eval helpers) + `pushFwdSection_apply_at_image` + `extDerivFun_comp_diffeomorph`; the source
  `HasDerivWithinAt` in `s` carries over since `Φ` is time-independent.  MDiff hypothesis from
  `covDerivOfField_eval_contMDiff`.

Gotchas banked:
- Needs `[FiniteDimensional ℝ E]` (in the variable block — `pullbackMetric` requires it) and, for the
  Shi/cov-derivative producers, `[NeZero (Module.finrank ℝ E)]` + the full
  `IsManifold 1/2/(∞+1) M&N` + `Boundaryless M&N` + `SigmaCompact/T2 N` block (theorem-local).
- `open DifferentialGeometry.PDE.RicciFlow` is REQUIRED (this file is in namespace
  `DifferentialGeometry.HCGCompactness`, but `SolutionOn`/`IsSolutionOn`/`solutionOn_pullback`/
  `isSolutionOn_pullback` live in `PDE.RicciFlow`); also `open …Integral.Connection` for
  `exists_gOrthonormalBasis`.
- `SolLip0Data`/`SolCovData`/`SolLipData` are `structure`s in `Type` (data fields), so their
  producers are `noncomputable def`, NOT `theorem`.  `SolLowData`/`SolSwapData` are `Prop` `def`s.
- Set membership `x ∈ Φ⁻¹' U` is defeq `Φ x ∈ U`, so `hV := fun _ hx => hx` discharges the
  `∀ x ∈ Φ⁻¹' U, Φ x ∈ U` side-conditions, and `hK'U ⟨x, hx, rfl⟩` gives `K' ⊆ Φ⁻¹' U`.

## `solSwapData_pullback` — DONE (the time-derivative swap)

`SolSwapData gRef D S` (a `Prop`) asserts, via `FixedBaseExtDerivTimeDerivativeOnRegular`
(Bundle/PartialMfderiv/FixedBase.lean), that `∂ₜ` of the spatial `extDerivFun` of
`covDerivOfField gRef (solnMetricField (S i) ·) p'` equals that of
`covDerivOfField gRef (solnEvolField (S i) ·) p'` on regular times — a time/covariant-derivative
SWAP, the one record that is NOT spatial-bound bookkeeping.  Built from existing infrastructure
(NO new frontier was needed):
- `extDerivFun_comp_diffeomorph` (FixedBase.lean:32): the directional-derivative chain rule
  `extDerivFun (fun y => f (Φ y)) x v = extDerivFun f (Φ x)(dΦ v)`.  Since `Φ` is time-INDEPENDENT,
  the source `HasDerivWithinAt` in `s` carries over verbatim.
- `covDerivOfField_pullback` (general base, MetricCovDerivPullback.lean:367) with `hA0` from
  `solnMetricField_pullback` / `solnEvolField_pullback`: gives `F_pb s = (F_source s) ∘ Φ` pointwise.
- `pushFwdSection Φ` + `pushFwdSection_apply_at_image`: push `V` to `N`; instantiate the source datum
  at `(pushFwd V, Φ x0)`.
- `covDerivOfField_eval_contMDiff` (MetricPreconv.lean:588): the `MDifferentiableAt` hypothesis.
The proof was a single inline assembly (`hfield`/`hMDiff`/`hconv` helpers + a `funext` for the
`s`-function and a value rewrite), no `HasDerivWithinAt.congr` needed — direct `exact` after the two
rewrites.

## Honest denominator

The pullback → `SolWindowData` layer is COMPLETE and verified sorry-free: `isSolutionOn_pullback`
(P1.4) + all keystones + all 5 records + `solWindowData_pullback` + `winGInfOfPullback`.  This whole
layer is the *input transport* for the conv field (g_∞) — it lets a window-solution package and its
recentering diffeomorphism produce the g_∞ pre-convergence conclusion on the recentered manifold.

What remains for MSM135 Ch4 Thm 3.10 ⇐ 3.9 is the BROADER recentering argument that CONSUMES
`winGInfOfPullback`: constructing the source `SolWindowData` from the actual flow sequence, choosing
the recentering diffeomorphisms `Φ_k`, and assembling the final 3.10 ⇐ 3.9 statement (the
compactness/recentering proper).  That is a separate, larger phase.  The pullback transport layer
itself — a multi-week sub-frontier when this branch started — is done.  Whole HCG compactness
project ≈ 25–30%.

## Verification

Per-lemma focused `lake env lean`; authoritative `lake-locked build
+…HCGCompactness.WindowDataPullback` green sorry-free (3899 jobs).  **Axiom-clean confirmed
(2026-06-30):** `isSolutionOn_pullback`, `solWindowData_pullback`, `winGInfOfPullback`,
`solSwapData_pullback` each `#print axioms` = `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no stray axioms.
