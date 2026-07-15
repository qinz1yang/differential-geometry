# PullbackNaturalityCross

Cross-model companion of `PullbackNaturality.lean`. Mechanical generalization of
the metric-curvature pullback naturality chain from `Φ : M ≃ₘ⟮I,I⟯ N` (same
model) to `Φ : M ≃ₘ⟮I,J⟯ N` (`M` over `I`/fiber `E`, `N` over `J`/fiber `F`).

## Status

Build GREEN and sorry-free (locked build of
`+DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross`, 3597 jobs,
first pass — no iteration needed). No errors, no warnings, no `sorry` in this
file. The read-only `lake env lean` check is also clean.

## Endpoint (compiled)

```
theorem metricRm04Std_pullbackCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (Diffeomorph.pullbackMetricCross g Phi) x X Y Z W =
      metricRm04StdAt g (Phi x)
        (mfderiv I J (Phi : M → N) x X) (mfderiv I J (Phi : M → N) x Y)
        (mfderiv I J (Phi : M → N) x Z) (mfderiv I J (Phi : M → N) x W)
```

Namespace `DifferentialGeometry.Integral.Connection`. Matches the required
signature exactly (`Phi` spelled where prompt wrote `Φ`).

## Ported chain (each with `Cross`/`C` suffix so no clash with template)

- private `mfderiv_eq_cle_applyCross`, `infty_ne_zeroC`
- `mpullback_symm_applyCross`
- private `pushFwdFieldCross` (+ `_apply_at_image`)
- `pushFwdSectionCross` (+ `pushFwdSectionCross_apply_at_image`)
- `directionalDeriv_pullbackCross`
- private `inner_bracket_pullback_pushFwdCross`
- private `koszulScalar_pullback_pushFwdCross`
- `metricCov_pullbackCross`  (the deep half)
- private `connectionRiemannCurvatureField_pullback_pushFwdCross`
- `metricRm04Std_pullbackCross`  (endpoint)

## The only changes vs the same-model template

The port was purely mechanical; every proof body is line-for-line the template
with these substitutions on the N-side:

- N-side tangent: `TangentSpace I` → `TangentSpace J`.
- N-side derivative: `mfderiv I I Phi` → `mfderiv I J Phi`.
- Pullback metric: `Diffeomorph.pullbackMetric` → `Diffeomorph.pullbackMetricCross`
  (import `Metric/PullbackCross.lean`); `_inner` lemma → `pullbackMetricCross_inner`.
- N-side pushed-forward field fiber: sections are
  `ContMDiffSection J F … (TangentSpace J)` (fiber `F`, model `J`).
- `metricCov (M := N) g` is over model `J`.
- N-side `metric_inner_contMDiffAt`, `leviCivitaConnectionOfMetric_inner_eq_koszulScalar`,
  `koszulScalar`, `directionalDeriv`, `connectionRiemannCurvatureField`,
  `riemannCurvature04At_apply_smooth`, `metricRm04StdAt`, `metricCov_smooth`,
  `tangentFlatLinear_injective_gen` — all invoked with `(I := J)`. These lemmas
  are single-model and are applied on the M-side with `(I := I)` /
  `pullbackMetricCross g Φ` and on the N-side with `(I := J)` / `g` SEPARATELY,
  exactly as the prompt's strategy note said.
- Directional-derivative codomain model: `𝓘(ℝ, ℝ)` (the scalar model is the
  same on both sides).

## Vector-field pullback arg order (the one thing to get right)

The pushforward is `VectorField.mpullback` of the INVERSE `Phi.symm : N → M`.
Source is `N` (model `J`), target is `M` (model `I`), so:

- `VectorField.mpullback J I (Phi.symm) X` — model order is (source, target) =
  `(J, I)`.
- `ContMDiff.mpullback_vectorField (I := J) (I' := I)` — Mathlib's `I` = source
  model, `I'` = target model.
- `VectorField.mpullback_mlieBracket (I := J) (I' := I)` gives
  `mpullback J I f (mlieBracket I V W) = mlieBracket J (mpullback J I f V) (mpullback J I f W)`,
  i.e. the pushed-forward bracket lives over `N` under `mlieBracket J`.

All three Mathlib vector-field lemmas (`mpullback`, `ContMDiff.mpullback_vectorField`,
`mpullback_mlieBracket`) live in a variable block with distinct source/target
models, so they are genuinely cross-model — no gap, no local re-derivation
needed.

## Gotchas encountered

None. Every cross-model primitive behaved as documented in
`Metric/PullbackCross.md`:
`Diffeomorph.mfderivToContinuousLinearEquiv`/`_coe`,
`ContMDiff.mpullback_vectorField`, `VectorField.mpullback_mlieBracket`,
`SmoothRiemannianMetric`-level lemmas — all fired identically to the same-model
case once the N-side model was switched to `J` and the fiber to `F`. First-pass
green.
