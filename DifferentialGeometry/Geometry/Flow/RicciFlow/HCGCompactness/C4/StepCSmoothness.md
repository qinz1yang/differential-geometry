# StepCSmoothness.lean — MSM135 C2 (`lbl430`), smooth dependence of the center of mass

## Goal
`lbl430`(i): the Riemannian center of mass `cm = argmin Σ μᵢ ½d(·,qᵢ)²` is `C¹` (in fact `C^∞`)
in the weights `μ` and the points `q`. Route (book chapter4.tex L2709+, transfer to normal
coordinates as at L1699–1703): the **Banach implicit function theorem** on the defining equation
`G(y,μ,q⃗) := Σ μᵢ exp_y⁻¹ qᵢ = 0`, solving for `y = cm` as a function of `(μ, q⃗)`, using that
`∂_y G ≈ -(Σμᵢ)·id` is invertible near the diagonal.

## State — verification PASSED, SORRY-FREE, axiom-clean
The whole file builds under a targeted `lake build`. Axiom probe on all new theorems:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### Session 2026-07-04 addition — the step-1 diagExpInv identification anchor (DONE)
`normalChart_eq_diagExpInv_snd` (new `section DiagExpIdentification`, sorry-free, axiom-clean):
`(normalChartAt g y q : E) = (diagExpInv g hEnorm p (y, q)).snd`, given `hsrc` (the fiber in the
`expMapDiffeo g y` source) and `hexp` (`expMapDiffeo g y (diagExpInv.snd) = q`, the honest producer
output). Proof = `(expMapDiffeo g y).left_inv hsrc` after `rw [hexp]` — `normalChartAt g y = symm`
by definition, so the fiber that inverts `expMapDiffeo g y` at `q` *is* the normal-chart coordinate.
This pins the E-valued moving-base equation `chartCmEqn` (which `hjoint` must be smooth in) to the
only jointly-`C¹` producer, `Exponential.diagExpInv`.
- **Instance plumbing that worked** (needed because `diagExpInv`/`expMapIntrinsic` need more than the
  bare manifold): section vars in ORDER `[RiemannianBundle (fun x:M => TangentSpace I x)]` FIRST
  (else `IsRiemannianManifold` and `IsContinuousRiemannianBundle` fail to synth), then
  `[PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]`; and
  `[IsContinuousRiemannianBundle E …]` must be a THEOREM binder UNDER the `attribute [-instance]
  Tensor0SBundle.tangentSpace_normed* in` scope (as a bare section var it can't synth the per-fiber
  `InnerProductSpace ℝ (TangentSpace I x)` — the Tensor0SBundle diamond). Mirror of HalfSqDistGrad.
- `hexp`'s native provenance (for the caller): `expIntr_diagExpInv` (`expMapIntrinsic g proj snd = q`,
  ∀ᶠ near `(p,p)`) + `diagExpInv_proj` (`proj = y`) + the `expMapIntrinsic = expMapDiffeo` agreement
  on the small ball (`exists_expMapIntrinsic_eq_expMap_radius` / `expMapDiffeo_apply_eq`).

Sorry-free:
- `cmSolution_hasStrictFDerivAt` — the `𝕜`-general Banach-IFT **consumer** bridge (prior session):
  turns an `ImplicitFunctionData 𝕜 (Ey × P) F P` into `HasStrictFDerivAt` of the `Ey`-component
  of the implicit function. Unchanged.
- **Step 1 / CORRECTNESS ANCHOR — `chartCmEqn` + `chartCmEqn_center` (PROVEN, sorry-free).**
  `chartCmEqn g p z (μ,ξ) := Σ μᵢ • normalChartAt g ((chart_p).symm z) ((chart_p).symm ξᵢ)` is the
  `E`-valued equation (`chart_p := normalChartAt g p`). `chartCmEqn_center` proves that at the
  `p`-chart coordinates of `centerOfMass` and the points, `chartCmEqn` reduces to the book's sum
  `Σ μᵢ • normalChartAt g (cm) qᵢ` — i.e. `chartCmEqn … = 0 ↔ Σ μᵢ exp_cm⁻¹ qᵢ = 0`
  (`centerOfMass.expInv_eqn`). Proof = `normalChartAt_left_inv` on the base and each point
  (`Finset.sum_congr` + `simp only [NormalCoordinates.normalChartAt_left_inv …]`). This pins the
  IFT statement to the actual cm-equation. **No trivialization/tangent-bundle chart needed** —
  using the `E`-valued `normalChartAt` (which *is* `expInv_eqn`'s LHS) makes the anchor
  definitional-after-`left_inv`, strictly simpler than the planner's tangent-bundle-fiber form.
- **Step 3 / honest input — `CmHessianInput` (STATED, sorry-free).**
  `CmHessianInput g p z₀ params := ∃ L : E ≃L[ℝ] E, HasFDerivAt (fun z => chartCmEqn g p z params) L z₀`.
  The `lbl430`/`lbl413` Hessian nondegeneracy `∂_z G ≈ -(Σμᵢ)·id`, invertible for `Σμᵢ>0`; native
  provenance = per-summand near-`-id` bound `‖∂_z(exp_y⁻¹ qᵢ)+id‖<1` + Neumann series.

- **Step 4 / endpoint — `chartCm_hasStrictFDerivAt` (PROVEN, sorry-free).**
  Given `hjoint : HasStrictFDerivAt (fun w => chartCmEqn g p w.1 w.2) D (z₀,params₀)` (the joint
  `C¹`-ness = step 2, carried as hypothesis), `hinv : CmHessianInput …`, and
  `hz₀ : chartCmEqn g p z₀ params₀ = 0` (z₀ solves the equation), concludes `∃ f Df, f params₀ = z₀
  ∧ HasStrictFDerivAt f Df params₀ ∧ ∀ᶠ params in 𝓝 params₀, chartCmEqn g p (f params) params = 0`.
  The Banach IFT bridge (`cmSolution_hasStrictFDerivAt`) is now fed a fully-assembled
  `ImplicitFunctionData` — the whole IFT logic is discharged.

## How step 4 was assembled (the proof that landed)
Build `φ : ImplicitFunctionData ℝ (E × P) E P` (`P := (ι→ℝ)×(ι→E)`), `leftFun := fun w =>
chartCmEqn g p w.1 w.2`, `leftDeriv := D`, `rightFun := Prod.snd`,
`rightDeriv := ContinuousLinearMap.snd ℝ E P`, `pt := (z₀,params₀)`. Key facts (all landed):
1. `hDL : D.comp (ContinuousLinearMap.inl ℝ E P) = (L : E →L E)` via
   `(hjoint.hasFDerivAt.comp z₀ hk).unique hL` where `hk := (hasFDerivAt_id z₀).prodMk
   (hasFDerivAt_const params₀ z₀)` — **NB the chain-rule `.comp` needs the composite ascribed to the
   explicit `leftFun ∘ (fun z => (z,params₀))` form**, NOT to `fun z => chartCmEqn g p z params₀`
   (the latter triggers higher-order unification and fails to pin `g`). Gives `hDv : ∀ v, D (v,0)=L v`.
2. `range_leftDeriv := LinearMap.range_eq_top.mpr hDsurj` (the CLM `.range` field accepts the
   `LinearMap.range_eq_top` proof directly — no `ContinuousLinearMap.range_eq_top` exists but the
   defeq goes through); `hDsurj w := ⟨(L.symm w, 0), by rw [hDv]; exact L.apply_symm_apply w⟩`.
3. `range_rightDeriv := LinearMap.range_eq_top.mpr Prod.snd_surjective`;
   `hasStrictFDerivAt_rightFun := hasStrictFDerivAt_snd` (NOT `(snd _).hasStrictFDerivAt` — function
   form `Prod.snd` vs `⇑(snd)` mismatch).
4. `isCompl_ker`: `disjoint_iff`+`Submodule.eq_bot_iff`+`LinearMap.mem_ker` (NO
   `ContinuousLinearMap.mem_ker`); codisjoint via `Submodule.mem_sup` with witnesses
   `(-(L.symm (D (0,q))), q) ∈ ker D` (split with `← ContinuousLinearMap.map_add`, `hDv`) and
   `(z + L.symm (D (0,q)), 0) ∈ ker snd`. Membership goal needs `change D … = 0` (LinearMap coe).
5. Conclusion: `f params₀ = z₀` via `implicitFunction_apply` + `toOpenPartialHomeomorph.left_inv`
   at `pt_mem_toOpenPartialHomeomorph_source`; the `∀ᶠ …=0` via
   `tendsto_const_nhds.prodMk_nhds Filter.tendsto_id` feeding `leftFun_implicitFunction` /
   `rightFun_implicitFunction`, then a `set x`-guarded `calc` (`set` first so the standalone
   `params` in the `(x.1, params)` tuple is not over-rewritten). Derivative = `cmSolution_hasStrictFDerivAt φ`.

## What is NOT done, and why — step 2 (`hjoint`) is a confirmed deep frontier
Step 1 (identification) is DONE. `hjoint` (joint `C¹`-ness of `chartCmEqn` in `(z, params)`) is
still carried as a hypothesis of `chartCm_hasStrictFDerivAt`. The precise obstruction, now
diagnosed:

- With the step-1 identification, `chartCmEqn`'s summand `(z, ξᵢ) ↦ normalChartAt g y qᵢ` equals the
  E-valued fiber `(diagExpInv g hEnorm p (y, qᵢ)).snd`, and `diagExpInv` is `C¹` (`diagExpInv_contMDiffAt`,
  `DiagExpDerivative.lean:558`) — but only into `TangentBundle I M` (model `I.tangent`).
- **The abstract `.snd` projection `TangentBundle I M → E` is NOT smooth** w.r.t. the tangent
  bundle's smooth structure. Although `TangentSpace I x := E` is a constant type synonym (so the
  fiber TYPE is `E`), the tangent bundle is NOT the trivial bundle `M × E`: its charts mix base and
  fiber through the derivative of the base-chart transitions. So `Bundle.TotalSpace.snd` (the naive
  type-level second projection) is not a smooth map. This is the genuine obstruction — not a
  route-choice or missing-API issue at the identification level.
- The smooth E-valued readout is the **chart** fiber `(extChartAt I.tangent ⟨p,0⟩ (diagExpInv …)).2 =
  A(y)·(exp_y⁻¹ qᵢ)`, where `A(y)` is the tangent-bundle fiber transition (the `inTangentCoordinates`
  / `inCoordinates` matrix; project machinery exists in `DifferentialGeometry/Bundle/PartialMfderiv/`
  and `Bundle/LocalFrameRegularity.lean`). Recovering the true `normalChartAt = A(y)⁻¹ ∘ (chart
  readout)` needs `A(y)⁻¹`'s joint smoothness — a real bundle-machinery assembly on top of a
  neighborhood-management step (`diagExpInv_contMDiffAt` is `C¹` only near `(p,p)`, so the
  configuration `(center, ptsᵢ)` must sit in that neighborhood — the smallness discipline).
- **Next-session route** (per planner): assemble `A(y)` via `inTangentCoordinates`, prove
  `A(y)`/`A(y)⁻¹` jointly `C¹` (bundle transition smoothness), compose with `diagExpInv_contMDiffAt`
  and the fixed `p`-chart, then the finite `μ`-linear sum gives `hjoint`; feed it to
  `chartCm_hasStrictFDerivAt`. This is a multi-part effort in the Bundle layer, not attempted this
  session. Alternatively, *redefining* `chartCmEqn` to use the chart readout `A(y)·(…)` directly (a
  linear iso, so `=0` is preserved — `chartCmEqn_center` would need re-proving) would make `hjoint`
  the direct chart-of-`C¹`-map, dodging `A(y)⁻¹`; this restructures the IFT chain and is a design call.

## Step 3 (wiring) — NOT reached
The implicit `f` from `chartCm_hasStrictFDerivAt` is to be identified near `params₀` with
`params ↦ chart_p (centerOfMass …)` (both solve `chartCmEqn = 0`; `chartCmEqn_center ↔
expInv_eqn_local`; local uniqueness from `CenterInput.unique` / `StrictDistInput`), giving
`centerOfMass` `C¹`. Blocked on step 2 (`hjoint`).

## CmHessianInput native discharge (note, per planner)
`CmHessianInput` (the `∂_z G ≈ -(Σμᵢ)·id` invertibility) is left as an honest input this session
and should NOT be reworked. Its native discharge is the **per-summand near-`-id` bound**
`‖∂_z(exp_y⁻¹ qᵢ) + id‖ < 1` (the derivative of each moving-base inverse-exp summand is close to
`-id` for `qᵢ` near `y`) plus the **Neumann-series refinement** (`Σμᵢ(-id + Eᵢ)` invertible when
`‖Σμᵢ Eᵢ‖ < Σμᵢ`, i.e. `Σμᵢ > 0`). That refinement consumes the same `diagExpInv`-derivative data
as `hjoint`, so it is naturally done together with / after step 2.

## Then: honest inputs still above this file
- Step 2 (joint `C¹` of `G`) — the `diagExpInv`→`E`-valued `normalChartAt` tangent-bundle-chart
  transfer. Real geometric frontier.
- `CmHessianInput` at the live configurations — the `lbl413`/§5 curvature-comparison Hessian bound
  (sibling of `Item3GpScaleInput`); book-cited, un-provable natively.
- Wiring `chartCm_hasStrictFDerivAt` back to `centerOfMass` C¹-dependence (compose with
  `(normalChartAt g p).symm`, use `chartCmEqn_center`) for the B1 consumer.

## Project position (honest)
This is the C2 brick of Step C of MSM135 Ch4 (Thm 3.9/3.10 HCG compactness). C2's **entire IFT
logic is now a closed, sorry-free, axiom-clean Lean theorem**: correctness anchor proven, honest
Hessian input stated, and the full Banach-IFT endpoint (`chartCm_hasStrictFDerivAt`) assembled and
proven — conditional only on the two honest inputs `hjoint` (step-2 joint `C¹`-ness) and `hinv`
(Hessian nondegeneracy). The remaining C2 work is NOT the IFT (done) but: (i) **discharging step 2**
— the `diagExpInv`→`E`-valued-`normalChartAt` tangent-bundle-chart smoothness transfer (the deep
geometric frontier); (ii) the `CmHessianInput` §5/`lbl413` curvature-comparison input at live
configurations; (iii) wiring `chartCm_hasStrictFDerivAt` back to `centerOfMass` via
`chartCmEqn_center`. C2 is one of several Step-C bricks; Step C is one part of Ch4; Ch4/HCG
compactness overall ≈ 20–25%. Prior session: IFT logic (anchor + input + endpoint) proven
sorry-free. This session (2026-07-04): the **step-1 `diagExpInv` identification anchor**
(`normalChart_eq_diagExpInv_snd`) proven sorry-free/axiom-clean, pinning `hjoint`'s statement to the
`diagExpInv` producer, and the deep obstruction in step 2 (`hjoint`) diagnosed precisely (abstract
`TangentBundle.snd` is non-smooth; the smooth readout is `A(y)·(fiber)` needing the
`inTangentCoordinates` fiber-transition `A(y)⁻¹`). `lbl430`(i) as a statement about the actual
`centerOfMass` still needs: step-2 `hjoint` (the bundle-transition smoothness assembly + smallness
neighborhood), the wiring (iii), and the `CmHessianInput` discharge. `hjoint` is a genuine
multi-part Bundle-layer frontier, not a local proof.

## PLANNER RULING #3 (2026-07-04) — the step-2 wall DISSOLVES: readout-form equation, no A(y)⁻¹

The "genuine Bundle-layer frontier" classification is REJECTED for the route that matters — this
is the project's recurring wall-dissolves-on-restatement pattern (cf. the P1.4 double-model false
wall and `ricciflow-agents-overcount-walls`). The diagnosis (abstract `TangentBundle.snd` is
non-smooth; the smooth object is the trivialization readout `A(y)·(fiber)`) is CORRECT — but the
conclusion ("need `A(y)⁻¹` joint smoothness, a Bundle-layer assembly") only holds for the
`A⁻¹`-recovery route. Take the executor's own alternative instead, which Planner Ruling (Wall 3)
already licensed:

**Redefine the equation in READOUT form.** `chartCmEqn' (z, params) := the trivialization-at-p
fiber readout of Σ μᵢ • (diagExpInv (y, qᵢ)).snd`, i.e. `A(y) · (Σ μᵢ exp_y⁻¹ qᵢ)` (A(y) is
LINEAR — it pulls out of the finite sum). Since `A(y)` is a linear ISO on the single fiber:
- **Zero sets coincide pointwise**: for each `params`, `{z : chartCmEqn' = 0} = {z : chartCmEqn = 0}`,
  so the IMPLICIT FUNCTION IS LITERALLY THE SAME FUNCTION — the anchor `chartCmEqn_center`
  re-proof is the old anchor + "linear iso kills a vector iff it is zero" (one lemma).
- **`hjoint` becomes free-standing**: the readout of a `ContMDiffAt` map into the tangent bundle
  is jointly `C¹` BY `contMDiffAt_totalSpace` (Mathlib `VectorBundle/Basic.lean:197` — the exact
  pattern already used at `StepBInputs.lean:297`), applied to `diagExpInv_contMDiffAt`, then the
  finite weighted sum (μ linear). NO `A(y)⁻¹` smoothness is needed ANYWHERE.
- **`CmHessianInput` moves with the equation** (it is existential — the `A`-twist is absorbed into
  the invertible `L`); the honest-input status is unchanged.
- The wiring (iii) uses only the zero-set equivalence, so it is untouched.

Remaining real content after the redefinition: (a) the readout-vs-sum commutation (A linear over
the finite sum), (b) neighborhood management (diagExpInv is `C¹` near the diagonal — handle by the
established smallness-hypothesis style), (c) the anchor re-proof, (d) the wiring. That is one
session, not a Bundle-layer program. Keep `normalChart_eq_diagExpInv_snd` (it anchors the readout
to the geometry); keep the current `chartCmEqn`+endpoint as-is if simpler to ADD `chartCmEqn'` +
equivalence rather than edit in place.

## RULING #3 IMPLEMENTED (2026-07-04) — the wall is dissolved, `hjoint` is now PROVED
All new declarations sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]` (targeted
`lake build`). The `hjoint` "deep Bundle-layer frontier" of the prior session is now a proved lemma.

- **CRUX — `diagExpReadout_contMDiffAt`** (readout smooth). `(y,q) ↦ (trivializationAt E
  (TangentSpace I) p (diagExpInv g hEnorm p (y,q))).2` is `ContMDiffAt (I.prod I) 𝓘(ℝ,E) 1` at
  `(p,p)`. Proof: `rw [contMDiffAt_totalSpace] at (diagExpInv_contMDiffAt …); … exact h.2` — the
  readout of a `ContMDiffAt` map into the tangent bundle is `ContMDiffAt` (`VectorBundle/Basic.lean`,
  the `StepBInputs:297` pattern). `diagExpInv_center` gives `(diagExpInv (p,p)).proj = p`. **NO `A⁻¹`.**
- **Ruling step 1 — `chartCmEqn'` (def) + `readout_sum_eq_clm` (factoring) + `readout_sum_eq_zero_iff`
  (zero-set equivalence).** `chartCmEqn'` = the weighted sum of readouts. Given the per-index
  `hpt i : diagExpInv (y, qs i) = ⟨y, normalChartAt g y (qs i)⟩` (from `diagExpInv_proj` +
  `normalChart_eq_diagExpInv_snd`), the readout sum `= CLE_y (Σ μᵢ • normalChartAt g y qᵢ)` via
  `Trivialization.continuousLinearEquivAt_apply'` + `apply_eq_prod_continuousLinearEquivAt` + `map_sum`
  /`map_smul`; hence `chartCmEqn' = 0 ↔ chartCmEqn = 0` (`CLE.map_eq_zero_iff`).
- **Ruling step 2 — `chartCmEqn'_contDiffAt` (`hjoint'`).** `chartCmEqn'` is `ContDiffAt ℝ 1` at
  `(z₀,params₀)`: `ContDiffAt.sum` + `ContDiffAt.smul`; each summand is `(inverse chart) ∘ readout`
  via `contMDiffAt_iff_contDiffAt` + `(hsm i).comp … hinner` (bind the comp in a `have` first — the
  goal-splitting inference fails otherwise; and use `contMDiffAt_iff_contDiffAt; fun_prop` for the
  normed projections, since `contMDiffAt_fst` wants `I.prod J` not `𝓘(ℝ, E×P)`). Honest hyps: `hchz`,
  `hchξ` (inverse-chart `ContMDiffAt`), `hsm` (readout `ContMDiffAt` at the config = the smallness
  discipline transporting the crux off `(p,p)`).
- **Endpoint generalization — `implicitSol_hasStrictFDerivAt`** (abstract equation `G`, the old
  `chartCm_hasStrictFDerivAt` proof verbatim with `chartCmEqn g p → G`); `chartCm_hasStrictFDerivAt`
  kept as a thin wrapper.
- **Ruling step 3 core — `readoutSol_hasStrictFDerivAt`.** `implicitSol_hasStrictFDerivAt` at `G =
  chartCmEqn'`, with `hjoint'` supplied by `chartCmEqn'_contDiffAt.hasStrictFDerivAt one_ne_zero`
  (NB `ContDiffAt.hasStrictFDerivAt` wants `n ≠ 0`, not `1 ≤ n`). **`hjoint` is discharged**; the
  implicit solution `f` is `C¹` and solves `chartCmEqn' = 0`, conditional ONLY on `hinv'`
  (`CmHessianInput` in readout form — the `A`-twist absorbed into the fresh `L`) + the smallness data.

### C2 LAST-MILE DONE (2026-07-04) — `center_hasStrictFDerivAt` (lbl430(i) at C¹), sorry-free
`readoutSol` gives the `C¹` implicit solution `f` of the readout equation. The last-mile identifies
`f` with `normalChartAt g p ∘ c` (any center family) and concludes the center of mass is `C¹`:

- **IFT-side uniqueness (added to `implicitSol_hasStrictFDerivAt`).** A fourth conjunct
  `∀ᶠ zp in 𝓝 (z₀,params₀), G zp.1 zp.2 = 0 → zp.1 = f zp.2` — the `G=0` solution near the base is the
  implicit function. Proof = `φ.leftFun_eq_iff_implicitFunction` (the `toOpenPartialHomeomorph`
  injectivity) + `hz₀`; `zp.1 = (φ.implicitFunction (leftFun pt) (rightFun zp)).1 = f zp.2`. Propagated
  to `chartCm_hasStrictFDerivAt` and `readoutSol_hasStrictFDerivAt`. (This is the planner's preferred
  Banach-injectivity route — no strict-convexity ⟹ minimizer lemma needed.)
- **`center_hasStrictFDerivAt`.** For any center family `c : params → M` solving the readout equation
  near `params₀` (`hc_solves` — from `chartCmEqn_center` + `expInv_eqn_local` + `readout_sum_eq_zero_iff`)
  and continuous there (`hc_cont : Tendsto (chart_p ∘ c) (𝓝 params₀) (𝓝 z₀)`), the uniqueness conjunct
  `(hc_cont.prodMk_nhds tendsto_id).eventually huniq` + `hc_solves` give `chart_p ∘ c =ᶠ f` near
  `params₀`; then `hfderiv.congr_of_eventuallyEq hid.symm` transfers `f`'s strict derivative. Endpoint:
  `∃ Df, HasStrictFDerivAt (fun params => normalChartAt g p (c params)) Df params₀` — the center of mass
  is `C¹` in `(weights, points)`, conditional only on `hinv'` (`CmHessianInput`), the readoutSol
  smallness data, and `c`'s honest center properties (`hc_solves` = `StrictDistInput`-derived,
  `hc_cont` = center continuity). **Sorry-free.**

Instantiating `c := centerOfMass ∘ config` (deriving `hc_solves`/`hc_cont` from the per-`params`
`CenterInput`) is the remaining plumbing to state it against the literal `centerOfMass`; the C¹
mathematics is complete.

### C2 endpoint at the project's own symbol DONE (2026-07-04) — `centerOfMass_hasStrictFDerivAt`
The literal endpoint now exists (green, sorry-free): `centerOfMass_hasStrictFDerivAt` specializes
`center_hasStrictFDerivAt` to `c params := centerOfMass g params.1 (fun i => (normalChartAt g p).symm
(params.2 i)) join p r (H params)` — the project's `centerOfMass` symbol appears in a `HasStrictFDerivAt`
statement (`lbl430`(i)). No instance conflict (the section's `PseudoEMetricSpace M` and `centerOfMass`'s
internal `HopfRinow` `MetricSpace` coexist). It consumes:
- `H` — a per-parameter `CenterInput` family (data);
- `hc_solves` — dischargeable per parameter from `expInv_eqn_local` + `readout_sum_eq_zero_iff` (the
  `CenterInput`+smallness threading over `𝓝 params₀`);
- `hc_cont` — **DISCHARGED 2026-07-04 (GREEN)** by `centerOfMassChart_cont` (this file):
  `centerOfMass_cont` (`StepCCenterOfMass`, from the general `Comparison/CenterOfMass.metricEnergy_argmin_stable`
  argmin-stability) composed with `normalChartAt_contMDiffOn.continuousOn.continuousAt` gives the
  chart-center `Tendsto`. Honest remaining inputs: `hpts` (config point-map continuity), `hsrc`
  (center in chart source) — smallness, not producers.

### The `hc_cont` producer chain DONE (2026-07-04) — C2 endpoint conditional only on the two honest inputs
1. `Comparison/CenterOfMass.metricEnergy_argmin_stable` (GENERAL, `set_option maxHeartbeats 800000`):
   `μ, pts : P → …` continuous over first-countable `P`, `c a` a global `metricEnergy`-minimizer in a
   compact `K`, `c p₀` the *unique* min ⟹ `Tendsto c (𝓝 p₀) (𝓝 (c p₀))`. Proof = `tendsto_iff_seq_tendsto`
   → `tendsto_of_subseq_tendsto` → `IsCompact.tendsto_subseq` (compact `K`) → limit-pass the min
   inequality via joint energy continuity (`Continuous (fun (a,q) => metricEnergy (μ a) (pts a) q)`) →
   uniqueness. **No Mathlib argmin-continuity lemma existed — assembled from scratch.**
2. `StepCCenterOfMass.centerOfMass_cont`: the literal center's continuity, feeding (1) the
   `centerOfMass.{min,mem,unique}` package (`centerEnergy → metricEnergy` via `centerEnergy_eq_dist`)
   and `K = closedBall p (2r)` compact (`HopfRinow.properSpace_riemMetric`). No topology diamond.
3. `StepCSmoothness.centerOfMassChart_cont`: `(2) ∘ normalChartAt continuity` = `hc_cont`.

### C2 UPGRADED C¹ → C^n (`lbl430`(ii)) DONE (2026-07-05) — every finite order, sorry-free, axiom-clean
Full `lake build` GREEN; `#print axioms centerOfMass_contDiffAt = implicitSol_contDiffAt =
[propext, Classical.choice, Quot.sound]`. The C¹ endpoints are UNTOUCHED; the C^n versions sit
alongside. Four steps, exactly the planner's route (no new mathematics):

1. **`DiagExpDerivative.diagExpInv_contMDiffAt_order`** (order `n`, `hn : 1 ≤ n`): the moving-base
   inverse exponential is `C^n` at `(p,p)`. Same IFT construction as the order-1 anchor; the KEY is
   `ContDiffAt.localInverse`/`to_localInverse` are **order-independent by proof irrelevance**
   (`(diagExpIFT g hEnorm p).symm = (chartedDiagExp_contDiffAt … n hn).localInverse … := rfl`), so
   only the ContDiffAt-order on the forward map bumps. Import graph checked: the C∞ forward exp facts
   are NOT downstream of DiagExpDerivative, so the bump is in-place (no Step-B cycle). `hn0 :
   ((n:ℕ∞):WithTop ℕ∞) ≠ 0` is the ContDiff-order coercion (double coe).
2. **`diagExpReadout_contMDiffAt_order`** + **`chartCmEqn'_contDiffAt_order`** (StepCSmoothness):
   readout `contMDiffAt_totalSpace`-of-`diagExpInv_contMDiffAt_order`, then the
   `ContDiffAt.sum/.smul/.comp` assembly — order-generic, every factor supplied at `(n:ℕ∞)`.
3. **`implicitSol_contDiffAt`** — the C^n Banach implicit function theorem via the **pinned map**
   `Φ(z,params) := (G z params, params)`. `dΦ = D.prod snd` is block-triangular, realized as an
   explicit `ContinuousLinearEquiv` (`ContinuousLinearEquiv.equivOfInverse D' D'inv …`) with inverse
   `(a,b) ↦ (L⁻¹(a − ∂_pG·b), b)` — the `z`-block `L` is the SAME `CmHessianInput`, order-independent.
   `ContDiffAt.to_localInverse` (needs `n ≠ 0` = `hn`) makes `Φ⁻¹` `C^n`; `f params := (Φ⁻¹(0,params)).1`.
   The four conclusions (`f params₀=z₀`, `ContDiffAt n f`, solves `G=0`, local uniqueness) come from
   `HasStrictFDerivAt.localInverse`'s `localInverse_apply_image`/`eventually_right_inverse`/
   `eventually_left_inverse` (the strict form is defeq to the ContDiffAt localInverse by proof irrel).
   LESSON: Mathlib's `eventually_*`/`localInverse_apply_image` come **beta/projection-reduced** — do
   NOT `rw [hΦpt]` the un-beta'd lambda filter-base; instead **type-ascribe** the clean form
   (`… : ∀ᶠ y in 𝓝 ((G z₀ params₀, params₀) : …), … invF …`, accepted by defeq) then `rw [hz₀]`.
   The block-inverse laws: `simp only [prod_apply, comp_apply, sub_apply, coe_fst', coe_snd',
   inr_apply, coe_coe, Prod.mk.injEq, and_true]` (the `and_true` collapses the `snd`-component `= _ ∧
   True`) + `hDsplit : D(v,u) = L v + D(0,u)` + `L.symm_apply_apply`/`L.apply_symm_apply`.
4. **`readoutSol_contDiffAt`** (specialize to `chartCmEqn'` via `chartCmEqn'_contDiffAt_order` +
   `implicitSol_contDiffAt`), **`center_contDiffAt`** (transfer via `ContDiffAt.congr_of_eventuallyEq`
   on the SAME `hid : normalChartAt g p ∘ c =ᶠ f` from `hc_solves`+`hc_cont` — order-independent
   identification; note `congr_of_eventuallyEq` for `ContDiffAt` takes `f₁ =ᶠ f` so use `hid`, NOT
   `hid.symm` as the `HasStrictFDerivAt` variant does), **`centerOfMass_contDiffAt`** (literal
   `centerOfMass` endpoint). All conditional ONLY on `CmHessianInput` (`hinv'`) + `StrictDistInput`
   (via `c`/`hc_solves`) + smallness (`hchz`/`hchξ`/`hsm` at order `n`) — the same honest inputs as C¹.

### `lbl430`(i) QUANTITATIVE bounds half → `C4/StepCDerivBounds.lean` (see StepCDerivBounds.md)
Regularity (`C^n`, above) ≠ bounds (`k`-uniform `C̃_j`).  The uniform-in-configuration derivative
bounds `|∇^j (chart∘cm)| ≤ C̃_j` (eq `lbl431`, gates `stepB1_approxIso`'s `(ε,p)` conjunct) live in
the new file `StepCDerivBounds.lean`.  Base case + honest inputs DONE 2026-07-05 (axiom-clean):
`implicitDeriv_one_le` (abstract order-1 IFT bound `‖Df‖ ≤ Λ·B` from chain-ruling `G(f,·)=0`),
`CmHessianBoundInput` (`‖L⁻¹‖ ≤ Λ`), `CmGDerivBound` (`‖∇^j G‖ ≤ B_j`), `cmChartFDerivLe` (`j=1`).
The general-`j` `cmChartDerivLe` keeps ONE sorry = the Faà-di-Bruno leading-term induction step.
LESSON (`HasFDerivAt.comp` for `fun p => G (f p) p`): Lean mis-guesses the inner map as
`Prod.mk (f params₀)` (it fits the point); fully pin `(𝕜:=ℝ)(E:=)(F:=)(G:=)(f:=)(g:=)` AND take the
`have hcomp := …` result **unascribed** (an ascription-coercion leaves a `Module ?m E` metavar that
stucks every consumer of `hcomp`), then `hcomp.unique hconst` with `hconst` in the matching `∘` form.

## 2026-07-10 — pinned branch extraction and off-diagonal readout domains

- Factored the pinned-map derivative into `existsPinnedDeriv` and exposed its
  local inverse as `existsPinnedLocal`. `implicitSol_contDiffAt` now reuses this
  producer instead of duplicating the block-triangular algebra.
- Added `diagExpInv_eq_normal`, packaging the base projection and fiber
  identification into the exact tangent-bundle equality consumed by
  `readout_sum_eq_zero_iff`.
- Added `diagReadout_of_md`, the arbitrary-point trivialization adapter, and
  `exists_readoutDom`, an open finite-order neighborhood of `(p,p)` carrying
  readout `C^n` regularity plus the right-inverse/projection/intrinsic-exp facts.
- Focused verification passed; targeted `StepCSmoothness` and downstream
  `StepCCmDomain` builds passed. The pre-existing unused-`Fintype` warning on
  `implicitSol_hasStrictFDerivAt` remains unrelated.
- Honest stop condition: `exists_readoutDom` is order-dependent. A fixed open
  configuration region carrying every finite order still needs a common
  `C^∞` branch theorem. Diagonal recentering and the pointwise
  `normalChartAt` choice both reduce to that same missing moving-base API.

## 2026-07-10 — pointwise realized/intrinsic branch identification

- Added `diagInv_eq_normal_lt`.  It derives the tangent-bundle equality between
  `diagExpInv` and the moving normal chart from three honest lower facts: the
  branch projection, the intrinsic exponential identity, and smallness below
  `expDiffeoRadius`.
- This consumes the new pointwise producers `expDiffeo_mem_of_lt` and
  `expDiffeo_eq_intr`; callers no longer need to assume a full realized
  exponential equality as one opaque hypothesis.
- Focused verification passed and the targeted module object was refreshed.
- Limitation: the theorem is pointwise.  Producing its smallness hypothesis
  uniformly on the finite-hat configuration family remains part of the common
  branch/configuration-containment frontier.

## 2026-07-10 — common all-order readout domain

- Added `exists_readoutDom_inf`, the fixed-trivialization restriction of
  `DiagExpDerivative.exists_diagInvDom_inf`.  One open neighborhood of `(p,p)`
  now carries joint `ContMDiffOn ∞` readout regularity and the right-inverse,
  projection, and intrinsic exponential identities.
- The proof uses the existing `diagExpInv` and `trivializationAt`; it does not
  create a sigma-box inverse or a second branch.
- Focused verification passed.  Together with the targeted upstream build, the
  common all-order inverse/readout-domain API is complete.
- Remaining limitation is geometric containment: the concrete finite-hat
  configurations must be placed in this open domain, below
  `centerOfMass.eqnRadius`, and below the moving `expDiffeoRadius` required by
  `diagInv_eq_normal_lt`.

## 2026-07-10 — numerical branch radius and local containment

- Added `exists_readoutEBall`.  For each fixed `(M, g, p)` it extracts one
  finite positive Riemannian extended radius `δ` on which the readout is jointly
  `C^∞` and all inverse/projection/intrinsic-exp branch identities hold.
- Added `centerPairs_lt_of`, `centerPairs_lt_le`, and `centerPairs_lt`.  They
  convert the standard center-of-mass bounds into membership of that product
  eball.  The cage-facing form says that `dist p q ≤ R` and
  `ENNReal.ofReal (R + 2 * r) < δ` suffice; the finite-hat consumer can take
  `R = 4 * lambda`.
- Focused verification and the targeted module build passed.  These lemmas close the local triangle-inequality
  and topology bookkeeping; they do not claim that the extracted `δ` has a
  positive lower bound over the sequence index.
- Exact remaining branch-scale gap: `NormalCoordMetricBoundInput.metricC` is
  uniform, but its `radius` has only pointwise `radius_pos`.  The current input
  can therefore shrink with `k` and cannot imply the uniform branch radius
  needed by the selected global `SigmaScaleField` route.  A fixed-index finite
  minimum is valid but does not by itself discharge the eventual all-`k`
  `StepB1RawInput` producer.
- If the global-sigma route is retained, the next genuine producer is a
  quantitative normal-coordinate `chartedDiagExp` approximation (for example
  `ApproximatesLinearOn` with constants uniform on live centers), followed by an
  explicitly controlled inverse branch.  Adding a bare consumer-side
  `branchRadius` field would only rename this missing geometry.

## 2026-07-11 - selected-branch equation core

- Added `chartCmEqnB`, the readout center equation parameterized by an explicit
  `DiagInvBranch`.  The existing `chartCmEqn'` remains unchanged as the legacy
  compatibility API.
- `chartCmEqnB_std` proves that specialization to `stdBranch` recovers the old
  equation exactly, using `std_inv_eq` rather than a new uniqueness argument.
- `chartCmEqnB_cdAt` proves joint smoothness at an arbitrary order from the
  selected readout's smoothness and the two inverse-chart hypotheses.  This is
  the branch-generic analytic core needed by both the legacy and quantitative
  lanes.
- `readoutB_sum_eq` and `readoutB_zero_iff` transport the selected ambient
  branch readout to the intrinsic normal-coordinate sum under an explicit
  pointwise inverse identification.
- `readoutSolB_strict` and `readoutSolB_cdAt` run the existing implicit-function
  engine for the selected branch.  `centerB_hasStrict` and `centerB_contDiff`
  then transfer the local implicit solution to any continuous center family
  solving that branch equation.
- Focused verification passed without warnings or local `sorry`s.  The
  equation, zero-set, implicit-solution, and chart-center migration brick is
  complete.  The selected-branch extension/domain consumers in
  `StepCCmDomain`, the concrete quantitative HCG branch producer, and the
  finite-hat scale specialization remain.

## 2026-07-18 framed selected-branch coordinates

The selected-branch equation stack now interprets its fixed-base model
parameters with `framedChartAt g p`: `chartCmEqnB`, `chartCmEqn'`, their joint
smoothness lemmas, both implicit-solution APIs, and the concrete center
endpoints all use the same orthonormal coordinates as the quantitative branch.
The moving-base `normalChartAt g y q` terms remain raw because they represent
the actual inverse-exponential tangent vector at `y`, rather than a fixed-base
parameter coordinate.

The framed section now obtains its normed-space instance from
`InnerProductSpace` and records the required `CompleteSpace E`, avoiding the
old model-with-corners instance mismatch. Focused verification and the exact
module refresh passed. No new assumption or parallel equation API was added.
