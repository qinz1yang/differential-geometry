# MetricCovDerivTimeDeriv.lean — the tower evolution core (P2, eq. 3.4)

## 2026-07-12 — short-time branch alignment

- The evaluated Ricci-flow equation now uses `Tensor0SSpace.smul_apply` explicitly for the `-2 Ric` field.
- Focused verification passed without `sorry`; this is a compatibility repair, not new progress on the HCG endpoint.

Status: **sorry-free, verified** (focused check + targeted build green, 2026-06-11).

## What this file provides

The `∂ₜ∇ᵖg = -2∇ᵖRc` track of MSM135 Lemma 3.11 eq. (3.4), from the flow
equation up to the `hevComp` input of `covOrderBound_stage`:

* `covDerivOfField_eval_hasDerivWithinAt` — the p-fold induction core in the
  **flow-interval two-set shape**: derivatives within the time carrier `T`,
  required only at regular times `R`, swap input as
  `FixedBaseExtDerivTimeDerivativeOnRegular T R {x₀}`.  Engine =
  `totalNabla0SFun_hasDerivWithinAt_pt` (pointwise-swap variant added in
  `TotalNabla0STimeDeriv.lean`; the predicate-form originals are now thin
  wrappers).  Slot extension via `ContMDiffSection.exists_eq_at_gen`,
  tuple identification by `Fin.cases`.
* `covDerivOfField_swapReg` — **the swap discharged from regularity**: the
  `hswap` input produced from joint `(t,x)` C² smoothness + spatial
  differentiability of the tower scalars via
  `fixedBaseOnReg_of_timeDerivWithin`; the `hTime` input at level `p` is the
  chain itself at level `p` (strong induction `Nat.strong_induction_on`, the
  chain is invoked with `N := p` and the inductive swaps).
* `solnMetricField` / `solnRicField` / `solnEvolField` — the solution's moving
  metric, Ricci (bundled `ricciSection` of the moving LC connection — same
  base field as `ricCovTower`), and `-2·Ric` evolution field.
* `solnRicField_eq_ricciAt` — pointwise agreement with `S.ricciAt`
  (`ricciSection_apply` + definitional chain through `metricRicciAt`,
  `metricCov = leviCivitaConnectionOfMetric` rfl, proof irrelevance for the
  smoothness argument: `ContMDiffCovariantDerivativeLocally` is a `Prop`).
* `solnMetricDeriv` — the evaluated flow equation
  (`metric_derivWithin_eq_neg_two_ricci` + `metricTensorField_apply` +
  `vec2 (v 0) (v 1) = v` by `fin_cases`).
* `solnTower_hasDerivAt` — the solution wrapper: full `HasDerivAt` at every
  regular time (upgrade via `D.regular_mem_nhds`, which yields
  `carrier ∈ 𝓝 t` — this is WHY the chain must run within the carrier).
* `solnTowerSwap_of_smooth` — solution-level swap producer (regularity in,
  `FixedBaseExtDerivTimeDerivativeOnRegular` out).

Consumed by `RicBound.lean`: `hevComp_of_solutions` (sequence adapter, value
bridge `covDerivOfField_smul` + `covDerivOfField_eq_iterCov` + rfl-identification
with `ricCovTower`/`nablaRicReal`) and the P2 capstone `covOrderBound_of_soln`.

## Design decisions (why this shape)

* **Two-set (T, R) form, not single-T**: `regular_mem_nhds` gives
  `carrier ∈ 𝓝 t`, NOT `regular ∈ 𝓝 t`; so HasDerivAt at regular times needs
  the within-set to be the carrier, while the flow equation only holds at
  regular times.  Same shape as the order-1 precedent
  `metricFrameComp_fixedBaseSwap_of_solution`.
* **Pointwise-swap engine variant (`_pt`)**: the all-t predicate
  `FixedBaseExtDerivTimeDerivativeOn` is undischargeable at carrier endpoints
  (the swap value at an irregular endpoint is wrong/unavailable); the Clairaut
  proof only ever consumes the swap at the working `t`, so `_pt` is the honest
  engine and the regular-form predicate plugs in directly.
* **`hTime` is the chain itself**: the discharger
  `fixedBaseOnReg_of_timeDerivWithin` needs the time derivative of the level-p
  scalar at ALL x — exactly the chain's level-p conclusion.  Hence swap p and
  chain p are produced by one strong induction, and the analytic content of
  the swap reduces entirely to regularity.

## Gotchas hit (cost real time)

* `(-2 : ℝ) • (field)` under a DFunLike application fails elaboration TWO ways:
  (1) without `set_option backward.isDefEq.respectTransparency false` the SMul
  instance on `Tensor0SField` does not synthesize AT ALL (this option is
  file-level in `MetricCovDerivLinear.lean` — that is why the same smul works
  there); (2) even with the option, under an application the HSMul result type
  stays a metavariable — pin it with a named def (`solnEvolField`).
* The same transparency option is needed in `RicBound.lean` for the
  `ContMDiffSection.coe_smul` rewrite (scoped `set_option ... in` before
  `hevComp_of_solutions` and `covOrderBound_of_soln`).
* Unfolding project defs in tactic blocks: `simp only [defName]` (equation
  lemma), not `rw [defName]`.
* Identifying the reindexed tower value: `simp` + `domDomCongr_apply` does NOT
  fire; the working pattern (precedent `metricCovDerivNorm_eq_iterCov`) is
  `show` into the `ContinuousMultilinearMap.domDomCongr (...) (... x)` form,
  then `simp only [nablaRicReal]` / rfl.

## Remaining frontier (NOT in this file)

The regularity inputs of `solnTowerSwap_of_smooth`:
joint `(t,x)` C² of `(t,x) ↦ (∇ᵖ_gRef g_t)(x)(V·x)` for p < N (plus spatial
differentiability of the metric/evolution towers).  Should ultimately come from
`IsSolutionOn.smoothMetric` (`MetricFamilySmoothOn`) + a joint-smoothness
calculus for `totalNabla0SFun` applied to time families — a missing-API track,
not deep mathematics.  Order-0 precedent: `metricInner_mdiffAt`
(`Evolution/Connection/MetricCovDerivProducer.lean`).

### ✅ REGULARITY TRACK COMPLETE (2026-06-11, commit 0619be60)

`solnMetricJointAt` (level-0 joint smoothness from
`MetricFamilySmoothOn.frameCompSmooth`: localFrame coefficient expansion via
`eventually_eq_localFrame_sum_coeff_smul` + `contMDiffAt_localFrame_coeff`
(ROOT namespace, not `Bundle.Trivialization`!) + bilinear double-sum expansion
— expand only the inner-product slots with an auxiliary `hexp`-rewrite, NOT a
global `rw [h0, h1]` which also hits the coefficient arguments; finish with
`Finset.sum_comm` + per-term `ring`) → `solnTowerSwap_reg` (the swap fully
discharged; single input `hDreg : t ∈ D.regular → D.regular ∈ 𝓝 t`) →
`covOrderBound_of_soln` (RicBound.lean) now consumes `hDreg` instead of the
three tower-regularity hypotheses.  Verification green.

### Historical: regularity-track progress (2026-06-11 late): BOTH tower inductions DONE

* `covDerivOfField_eval_contMDiffAt` (this file, ✅ green): joint C^∞ of every
  tower-level slot evaluation from level-0 joint smoothness (engine
  `prodExtDerivAt_inf`; slot updates by inline `∇_{V0}(V a)` sections).
* `covDerivOfField_eval_smoothAt` (this file, ✅): the spatial fixed-field
  sibling (engine `extDerivFun_apply_contMDiffAt`) — for `hFdiffT`/`hFtdiffT`.
* REMAINING for the full hSmoothT/hFdiffT/hFtdiffT discharge:
  (i) spatial level-0 for the metric: `(t fixed) y ↦ g.inner y (V₀y)(V₁y)` is
      ContMDiff ∞ — 2-liner: `cotangentCov_pairing_contMDiff
      (ContMDiff.clm_bundle_apply g.contMDiff hY) hZ` (the ContMDiff prefix of
      `metricInner_mdiffAt`'s proof, MetricCovDerivProducer.lean:62-76);
  (ii) spatial level-0 for `-2Ric_t`: slot pairing of the smooth
      `ricciSection` field with smooth sections (Tensor0SField-eval smoothness;
      look in NablaOnTensors/Regularity/Tensor0S.lean);
  (iii) JOINT level-0 for the metric family: from
      `MetricFamilySmoothOn.frameCompSmooth` (frame components,
      `ContMDiffOn (D.regular ×ˢ u)`) — needs (a) the ContMDiffOn→ContMDiffAt
      upgrade (`D.regular ×ˢ u ∈ 𝓝 (t,x)`: requires t ∈ interior D.regular or
      an `IsOpen D.regular` hypothesis — NO existing consumer discharges this
      yet, BBS route has the same open input), and (b) the local-frame
      coefficient expansion `g_t(V₀,V₁) = Σ_{ij} c⁰ᵢ c¹ⱼ g_t(eᵢ,eⱼ)` near x
      (Mathlib LocalFrame: `eventually_eq_localFrame_sum_coeff_smul`,
      `contMDiffAt_iff_localFrame_coeff` for coefficient smoothness) +
      ContMDiffAt.congr_of_eventuallyEq on the product (univ ×ˢ frame-domain);
  (iv) assembly: instantiate the two tower inductions at
      `A := solnMetricField S` / `A0 := solnEvolField S t`, `.of_le` ∞→2,
      landing exactly in `solnTowerSwap_of_smooth`'s hSmoothT/hFdiffT/hFtdiffT.
* When the other session's Multilinear/Tensor work settles, refactor the inline
  `W`-sections to `TensorLieDeriv.covSection` and the inline `hcov` to
  `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative` (both committed,
  78c1202b).

### Regularity-track plan (scouted 2026-06-11, engines 1 done)

* **Engine 1 ✅ DONE** (`Bundle/PartialMfderiv/Basic.lean`, commit d727cb50):
  `prodExtDerivAt_gen` (jointly C^{m+1} F, smooth field X ⇒ spatial directional
  derivative jointly C^m; m ≤ ∞) + `prodExtDerivAt_inf` (the iterable ∞ form).
  `prodExtDerivAt` (C³→C², pre-existing) was the template.
* **Engine 2 (∇_X Y as a smooth section for the Koszul LC), route found**:
  - Mathlib's `ContMDiffCovariantDerivative cov n` has ONE field `contMDiff :
    ContMDiffCovariantDerivativeOn E n cov.toFun univ`-shaped (see the
    `LeviCivita_isContMDiff` instance, `Geometry/Connection/LeviCivita/Defs.lean:347`).
    The in-tree `ContMDiffCovariantDerivativeLocally` (Connection/Smooth.lean:29)
    is `∀ open u, ContMDiffCovariantDerivativeOn E k cov.toFun u` — so
    `ContMDiffCovariantDerivative (leviCivitaConnectionOfMetric g) ∞` should be
    `⟨Locally-fact isOpen_univ⟩` (ONE liner).
  - Then `ContMDiffCovariantDerivative.contMDiff_apply`
    (`Tensor/RSTensor/NablaOnTensors/Connection/Smooth.lean:45`) gives the smooth
    Hom-section; note its `Y : ContMDiffSection (n+1)` — with n = ∞ use
    `ENat.coe_top_add_one` (∞ + 1 = ∞) to repackage an ∞-section.
  - DO NOT route through the stitched `LeviCivita g` (Defs.lean) — different
    hierarchy (`Measure.SmoothRiemannianMetric`, `IsMetricCompatible` vs `_gen`),
    and the uniqueness lemmas (`Uniqueness.lean:204`) demand
    `ContMDiffCovariantDerivative` for BOTH sides (circular; the args are
    underscored-unused but still required).
* **Tower induction** (to write, in this file or a new TowerRegularity.lean):
  P(p): ∀ V tuple of ∞-sections, (t,x) ↦ (covDerivOfField gRef (A t) p) x (V·x)
  jointly C^∞ at regular (t,x).  Step: `totalNabla0SFun_apply_section` +
  `nabla0SFun_eval_smooth_slots` decompose level p+1 = `extDerivFun`(level-p
  scalar)(V 0) − Σ_a level-p at slot tuples updated by Engine-2 sections;
  first term by `prodExtDerivAt_inf`, corrections by IH; need the funext lemma
  "evaluation commutes with `Function.update` of section tuples".
* **Base case**: `MetricFamilySmoothOn.frameCompSmooth` gives joint ⊤ smoothness
  of FRAME components on `D.regular ×ˢ u` (NOTE: ContMDiffOn on regular ×ˢ u —
  need `IsOpen D.regular`-style upgrade to ContMDiffAt, or t in the interior;
  check how the order-1 consumers discharge hSmooth).  Convert to arbitrary
  ∞-section slots via local-frame coefficient expansion
  (`e.localFrame_coeff`, Mathlib LocalFrame) — scalar = Σ coeffs · frame comps.
* **hFtdiffT (Ric side)**: fixed-t spatial smoothness; ricciSection is a smooth
  section (`rm13Section` smoothness with the `Locally` hcov), then the tower of
  a smooth field is smooth (spatial engine `contMDiffAt_extDerivFun_apply`,
  `Geometry/Connection/Realization/SmoothSectionsLocal.lean`).
