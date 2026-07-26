# JacobianImageLe.lean — B5a deliverable L3

## Result

`MeasureTheory.image_lintegral_le` (public, `namespace MeasureTheory`):

    μ : Measure E, [IsAddHaarMeasure μ], E finite-dim real normed space,
    hs : MeasurableSet s, hf : Measurable f, hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x,
    hw : Measurable w →
      ∫⁻ y in f '' s, w y ∂μ ≤ ∫⁻ x in s, w (f x) * ENNReal.ofReal |(f' x).det| ∂μ

The weighted, **non-injective** area inequality (`E → E`). Companion private helper
`image_simpleFunc_le` (abstract weight `d`, per-set bound `hkey` as hypothesis).

## Route (validated)

1. Per measurable `T`: `μ (f '' s ∩ T) ≤ ∫⁻ x in s ∩ f⁻¹'T, |det f'|` from Mathlib's
   injectivity-free `addHaar_image_le_lintegral_abs_det_fderiv` (Jacobian.lean:903) on the
   measurable set `s ∩ f⁻¹'T`, using `Set.image_inter_preimage` and `.mono inter_subset_left`.
2. Lift to a simple function `φ` by `SimpleFunc.induction`. Base case = one indicator
   (`lintegral_indicator`, `setLIntegral_const`, `Measure.restrict_apply/restrict_restrict`,
   `Set.indicator_mul_left`, `lintegral_const_mul_le`). Additive step = **`le_lintegral_add`**.
3. General measurable `w = ⨆ n, eapprox w n`: rewrite the LHS as a sup (`lintegral_congr` +
   `iSup_eapprox_apply`, `lintegral_iSup`), then `iSup_le` with each simple-function bound
   `.trans` a `lintegral_mono` up to `w`.

## KEY LESSON — the weight is NOT measurable

`|(f' x).det|` is not assumed measurable (`f'` is an arbitrary section, unique only where
`s` has a unique tangent). This is the crux and it dictates the whole route:

- The additive step of the simple-function induction MUST use the unconditional
  superadditivity `le_lintegral_add` (`∫⁻f + ∫⁻g ≤ ∫⁻(f+g)`, Lebesgue/Add.lean:248), NOT
  `lintegral_add_left` (needs a measurable summand).
- Monotone convergence is applied to the **image side only** — the weight is never moved
  across a limit/sum/integral.
- Two natural alternatives FAIL for exactly this reason: the measure-pushforward route
  (`Measure.map f ((μ.restrict s).withDensity d)`) needs `lintegral_withDensity_eq_lintegral_mul`
  ⇒ `d` measurable; the layer-cake route needs a Tonelli swap ⇒ `d` measurable.

`Measurable f` is required (for `f⁻¹'T` measurable in the base case). Honest and
consumer-satisfiable (the intended `f = expMapIntrinsic x` is smooth ⇒ measurable);
"measurable-on-`s`" would also suffice but adds `Subtype.val` measurable-embedding plumbing.

Mathlib search confirmed no weighted non-injective form exists: the weighted change of
variables `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Jacobian.lean:1189) is
injective (`InjOn f s`) and an equality.

## Lean gotchas paid

- `SimpleFunc.induction` case binders: use `| @const c T hT` / `| @add φ₁ φ₂ _ h₁ h₂` — the
  set (`{s}`) and functions (`⦃f g⦄`) are implicit/strict-implicit and are NOT counted by
  the plain `with` binder list ("N provided, M expected").
- `omit … in` must precede the docstring, which must sit directly on the lemma.
- indicator-under-preimage `T.indicator g (f x) = (f⁻¹'T).indicator g x` closes by `rfl`
  (preimage membership is defeq).
- `mul_le_mul_left'` / `mul_le_mul_right'` are deprecated → `gcongr`.

## Verification

Focused check + targeted module build both PASSED, sorry-free, no new axioms. Only Mathlib
imports (Jacobian, Lebesgue/Add, GroupWithZero/Indicator).

## Handoff to L5

`image_lintegral_le` is the Euclidean per-chart engine for the manifold-valued non-injective
area inequality `riemannianVolume_image_le_lintegral_density`. Feed it, per chart, the
chart-target set and the pushed weight; combine with the L4 chart decomposition
(`vol_le_tsum_supp`) and the density identity (B5b FRONTIER-B).
