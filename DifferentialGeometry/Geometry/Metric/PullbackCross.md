# PullbackCross

Cross-model companion of `Pullback.lean`. Mechanical generalization of the
metric-pullback API from `Φ : M ≃ₘ⟮I,I⟯ N` (same model) to `Φ : M ≃ₘ⟮I,J⟯ N`
(`M` over `I`/fiber `E`, `N` over `J`/fiber `F`).

## Status

Build GREEN and sorry-free (locked build of
`+DifferentialGeometry.Geometry.Metric.PullbackCross`, 2690 jobs).

## What changed vs the template (the only changes)

- N-side tangent: `TangentSpace I` → `TangentSpace J`.
- N-side derivative: `mfderiv I I Φ` → `mfderiv I J Φ`; `tangentMap I I Φ` →
  `tangentMap I J Φ`; `I.tangent` codomain → `J.tangent`.
- N-side bundle fiber: `E` → `F` (so `g.inner` section is `F →L F →L ℝ`,
  `g.contMDiff` targets `J.prod 𝓘(ℝ, F →L F →L ℝ)`).
- The CLE `Diffeomorph.mfderivToContinuousLinearEquiv Φ … x` is now
  `TangentSpace I x ≃L[ℝ] TangentSpace J (Φ x)`.
- The `pullbackInnerCross` RESULT is a form on `T_x M` (fiber `E`, model `I`), so
  `cotangentCov_clmSection_smooth_aux` and the whole M-side machinery apply
  UNCHANGED.

## Mathlib cross-model primitives — all genuinely cross-model, nothing missing

Verified in `.lake/packages/mathlib`:

- `Diffeomorph.mfderivToContinuousLinearEquiv (Φ : M ≃ₘ^n⟮I,J⟯ N) (hn) (x)` and
  `…_coe` — `LocalDiffeomorph.lean:403/408`, stated for distinct `I J`. `_coe`
  gives `= mfderiv% Φ x` (the `mfderiv%` macro = `mfderiv I J Φ x`).
- `ContMDiff.contMDiff_tangentMap` — `ContMDiffMFDeriv.lean:308`, `f : M → M'`
  with distinct models `I I'`. `Φ.contMDiff.contMDiff_tangentMap (le_refl _)`
  yields `ContMDiff I.tangent J.tangent ∞ (tangentMap I J Φ)`.
- `ContMDiff.clm_bundle_apply₂` — `VectorBundle/Hom.lean:419`. Single base
  manifold `M` (model `IM=I`) with base map `b : M → B` into a single target
  bundle base `B` (model `IB`). Cross-model use: `B = N`, `IB = J`, fibers
  `E₁=E₂=TangentSpace J`, `E₃=ℝ`, model fibers `F₁=F₂=F`, `F₃=ℝ`.

## Lesson / gotcha

Exactly one error during iteration: the `inner_comp_smooth_along_diffeoCross`
statement first copied `ContMDiff I (I.prod 𝓘(ℝ, F →L F →L ℝ)) …`. That section
(`g.inner ∘ Φ`) is a section of a bundle over `N`, so its CODOMAIN model must be
`J.prod`, not `I.prod` (the `I.prod` version fails `ChartedSpace` synthesis on
the Hom total space). Fixed to `J.prod`. Everywhere else the same-model
`I.prod`/`J.prod` split just follows which manifold the bundle sits over.

## Endpoints produced (all in `namespace DifferentialGeometry`)

- `Diffeomorph.pullbackInnerCross (g : SmoothRiemannianMetric J N)
  (Φ : M ≃ₘ⟮I,J⟯ N) (x : M) : T_x M →L T_x M →L ℝ`
- `Diffeomorph.pullbackInnerCross_symm` / `_pos` / `_isVonNBounded`
- `inner_comp_smooth_along_diffeoCross`
- `Diffeomorph.pullbackMetricCross [SigmaCompactSpace M] [T2Space M] (g) (Φ)
  : SmoothRiemannianMetric I M`
- `Diffeomorph.pullbackMetricCross_inner`
- `diffeomorph_pullback_metric_existsCross`
- `Diffeomorph.pullbackInnerCross_contMDiff`
- `Diffeomorph.mfderiv_contMDiffCross`
- private: `pullbackInnerCross_eval`, `mfderiv_eq_mfderivCLE_applyCross`,
  `mfderiv_apply_section_smooth_along_diffeoCross`, `infty_ne_zero_cross`

Note: `pullbackMetricCross_refl` was intentionally NOT ported — the reflexivity
lemma is meaningful only in the same-model case (`Diffeomorph.refl I M` needs
domain model = codomain model), so it stays in `Pullback.lean`.
