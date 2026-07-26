# PullbackNaturalityLocal.lean — local pullback naturality of metric (0,4) curvature

## Status: DONE, build-verified sorry-free (targeted `lake-locked build`, 2026-06-30).

Step C of the spherical-space-form quotient descent (plan
`plan-on-taking-a-spicy-kitten.md`, "Steps 6–7").

## Result

- `metricRm04StdAt_pullback_localDiffeo` — for a diffeomorphism `Ψ : W ≃ₘ⟮I,I⟯ V`
  between open submanifolds `W ⊆ M`, `V ⊆ N`:
  `metricRm04StdAt (pullbackMetric (g.restrictOpen V) Ψ) x = metricRm04StdAt g ((Ψ x):N)`
  on the `mfderiv I I Ψ`-pushed vectors.

## Route

Two rewrites: the GLOBAL same-model `metricRm04Std_pullback` (PullbackNaturality.lean:479)
followed by the germ-locality `metricRm04StdAt_restrictOpen` (Step B). No new math.

## Instances (the cost)

`metricRm04Std_pullback` needs `[InnerProductSpace Real E]`, `[NeZero (finrank E)]`,
and `[BoundarylessManifold I _] [IsManifold I 1 _] [IsManifold I ((∞:WithTop ℕ∞)+1) _]`
on BOTH open submanifolds `W`, `V` — added as theorem binders (no auto-Opens instances
in this tree; discharge them concretely at the Step D call site for the round
sphere/quotient, which are boundaryless + compact). `N` (the big manifold) carries the
full `[IsManifold I 1/∞+1] [T2] [SigmaCompact]` set in the variable block for the Step B
side.

## Next (Step D)

`SpaceFormQuotientMetric.lean` — descend the Γ-invariant round metric to `S³/Γ`
(`smoothMetric_of_localCoeff`, the R2 smoothness frontier), then `g_quot_constPosSec`
via this lemma + `roundMetric_sec_value`. Coupled with Step E (model strengthening
provides the covering local-section data as `Opens` diffeos matching this lemma's
`Ψ : W ≃ₘ⟮I,I⟯ V` interface).
