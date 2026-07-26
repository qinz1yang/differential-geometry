# MetricCovDerivCoordStep.lean — coordinate-frame recursion for the metric covariant tower (P3 Gap B)

**Status (2026-06-13): DONE + verified** — focused check + targeted build (3629
jobs) green; both lemmas `#print axioms` clean (`propext, Classical.choice,
Quot.sound`).

## What landed

Two lemmas turning the `metricCovDeriv` tower's `a → a+1` step into an explicit
coordinate-frame component recursion, the algebraic heart of the single-`φ`
Gap-B induction.

- `metricCovDeriv_succ_apply_section (h gRef a X x slots)`:
  `metricCovDeriv h gRef (a+1) x (Fin.cons (X x) slots) =
   nabla0SFun (a+2) (leviCivita gRef) X (metricCovDeriv h gRef a) x slots`.
  One-line `rw [metricCovDeriv_succ, metricCovDerivStep_apply,
  totalNabla0SFun_apply_section]` — the existing `MetricCovDerivLinear` rfl
  lemmas (`metricCovDeriv_succ`, `metricCovDerivStep_apply`) handle the
  `(a+2)+1 = (a+1)+2` index juggling, so NO Nat-cast pain.  This is the
  general-`a` analogue of `metricCovDeriv_one_apply_section`.

- `metricCovDeriv_succ_eval_smooth_slots (h gRef a X V x)` (the **preferred
  recursion for the convergence induction**): leading section `X`, smooth section
  slots `V`,
  `metricCovDeriv h gRef (a+1) x (Fin.cons (X x) (V·x)) =
     extDerivFun (fun y => metricCovDeriv h gRef a y (V·y)) x (X x)
     − Σ_p metricCovDeriv h gRef a x (update (V·x) p ((leviCivita gRef (V p)) x (X x)))`.
  Two-liner: `rw [metricCovDeriv_succ_apply_section]; exact
  nabla0SFun_eval_smooth_slots …` (the general-`s` Regularity-tree smooth-slots
  formula).  General-`a` analogue of `metricCovDeriv_one_eval_smooth_slots`.

- `metricCovDeriv_succ_component_coordFrame (h gRef a x I0)` with
  `I0 : Fin (a+3) → CoordinateIdx E`:
  `component0S (coordinateFrameAt_toBasis x) (metricCovDeriv h gRef (a+1) x) I0 =
     coordDeriv0SAt (coordinateFrameAt x (I0 0)) x (metricCovDeriv h gRef a) (tail I0)
     − Σ_p Σ_k Γ^k_{(I0 0)(tail I0 p)} · coordComponent0SAt (metricCovDeriv h gRef a x)
                                            (update (tail I0) p k)`,
  the `Γ` being `christoffelAlongInFrame` of the `gRef` Levi-Civita connection.
  Proof = producer (2) `nabla0SFun_eval_coordFrame` (from `CoordFrameStep.lean`)
  specialised to `α = metricCovDeriv h gRef a`.

## Route / Lean gotchas

- The leading derivative slot of `nabla0SFun` needs a GLOBAL `ContMDiffSection`,
  but the coordinate frame is only local.  Resolved by the SAME pattern as
  `metricCovDeriv_one_eval_localFrame`:
  `(coordinateFrameAt_isLocalFrame x).exists_contMDiffSection_eqOn_nhd` gives a
  global `sec` agreeing with `coordinateFrameAt x ·` near `x`; use `X := sec (I0 0)`.
- Both producer (2)'s directional term (`coordDeriv0SAt`, = `mfderiv … (X x)`)
  and its Christoffel term (`christoffelAlongInFrame … (X x) …`) depend on the
  leading slot ONLY through `X x`.  So the bridge back to the actual frame value
  is a single rewrite `hsecx : sec i x = coordinateFrameAt x i x`:
  `simp only [hsecx]` clears the Christoffel directions; a small `hcd`
  (`simp only [coordDeriv0SAt]; rw [hsecx]`) clears the directional term.  No
  germ/derivative bridge needed — that is the payoff of producer (2) being a
  pure pointwise-direction formula.
- Slot reshaping `(fun q => coordinateFrameAt x (I0 q) x) =
  Fin.cons (sec (I0 0) x) (fun p => coordinateFrameAt x (tail I0 p) x)` by
  `funext`/`Fin.cases`; the `succ` branch closes with `Fin.cons_succ` then `rfl`
  (`Fin.tail I0 p ≡ I0 p.succ`).

## Placement

New file in HCGCompactness importing `MetricCovDerivLinear` (tower rfl lemmas +
`metricCovDeriv`) and `Geometry/Coordinates/NablaComponents/CoordFrameStep`
(producer 2).  `metricCovDeriv_succ_apply_section` could fold into
`MetricCovDerivLinear` next to `metricCovDerivStep_apply`; kept here to avoid
rebuilding that file's dependents during the Gap-B push.

## Next (Gap B remaining) — section-based induction is the clean route

**Use `metricCovDeriv_succ_eval_smooth_slots`, NOT the coordinate-frame recursion,
for `componentConv_covDeriv_of_chartCInf`.**  B0's carrier is already
section-based (`g.inner w (σi w) (σj w)`), so staying with smooth section slots σ
keeps the induction over the WHOLE patch with NO frame-mismatch / germ-localisation:

- **carrier**: `carrier_a^σ (y) := metricCovDeriv g gRef a y (fun q => σ_{tuple q} y)`
  for slot tuples from the fixed finite frame-section family σ (from B0).  IH = its
  chart-rep converges `C^∞`-on-compacts along the single `φ`, for ALL tuples.
- **base `a=0`**: B0 `exists_engine_frameCInfConv` directly (carrier = `g.inner σ σ`).
- **step**: `metricCovDeriv_succ_eval_smooth_slots`.  Directional term
  `extDerivFun (carrier_a^σ) x (σ_d x)` → chart `fderiv` via the EXISTING connector
  `extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq`
  (`Bundle/PartialMfderiv/FixedBase.lean:199`) ⇒ **B2**.  Each correction
  `metricCovDeriv g gRef a x (update (σ·x) p ((cov σ_p) x (σ_d x)))`: expand
  `(cov σ_p)(σ_d) = Σ_e c_e · σ_e` (`c_e` = fixed `gRef`-smooth frame coefficients,
  `g`-INDEPENDENT) ⇒ slot becomes `Σ_e c_e · carrier_a^{σ with slot p→σ_e}` ⇒
  **mulLeft + sum + IH** (the swapped tuples are still σ-tuples, covered by the
  all-tuples IH).
- **extract**: pointwise at `x` of the `C^∞` limit gives
  `component0S b (metricCovDeriv g gRef a x)` convergence for a basis `b` realised
  by sections with `σ_q x = b (slots q)` — the shape `hnorm` needs.
- then finite-cover `hnorm` (`metricDerivNorm_le_compSq_uniform`) → `metricPreconvInf`.

The coordinate-frame recursion (`metricCovDeriv_succ_component_coordFrame`) and
producer (2) remain valid reusable component-API lemmas, but the σ-section route
above is what the convergence proof should use.
