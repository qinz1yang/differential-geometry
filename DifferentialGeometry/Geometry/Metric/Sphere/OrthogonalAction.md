# OrthogonalAction.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, step 3. The O(n+1) sphere-isometry
backbone, shared by the homogeneity curvature argument and the Γ⊂O(n+1) quotient.

## State: COMPLETE (sorry-free)

Verified green (`lake env lean`, exit 0, no sorry/warnings). Provides, for an
ambient `e : E ≃ₗᵢ[ℝ] E` (`[FiniteDimensional ℝ E]`, `[Fact (finrank ℝ E = n+1)]`):

- `sphereMap e` / `sphereDiffeo e : sphere (0:E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0:E) 1` —
  via `Set.codRestrict` + `ContMDiff.codRestrict_sphere`; `sphereDiffeo_coe` is `rfl`.
- `mfderiv_incl_sphereDiffeo` — the chain-rule identity `dι_{φx}(dφ_x v) = e (dι_x v)`.
- `roundInner_sphereDiffeo` — round inner product preserved (via `e.inner_map_map`).
- `pullbackMetric_round_eq : pullbackMetric roundMetric (sphereDiffeo e) = roundMetric`.

## Gotchas / lessons

- `[FiniteDimensional ℝ E]` must be in the variable block (not derived from `Fact`).
  With it, `ProperSpace E` and hence `CompactSpace (sphere 0 1)` (Mathlib instance
  `Metric.sphere.compactSpace`) resolve automatically → `SigmaCompactSpace`/`T2Space`
  for `Diffeomorph.pullbackMetric` are free.
- `mdifferentiableAt` takes `n ≠ 0` (NOT `1 ≤ n`); use `have h0 : (∞:WithTop ℕ∞) ≠ 0 := by decide`.
- `mfderiv_comp` takes the point `x` as an EXPLICIT first arg: `mfderiv_comp x hg hf`.
- The `rw [← mfderiv_comp …]` higher-order match FAILS; bind the chain-rule equations
  as concrete `have e1 := mfderiv_comp x hι_φx hφ` first, then `rw [← e1, hcomp, e2]`.
- `ContinuousLinearMap.comp_apply` would not fire via `rw`/`simp` at the tangent-space
  junction; finish with `exact mfderiv_lie_apply e _ _` (defeq: `(g.comp f) v = g (f v)`).
- `mfderiv` of a linear isometry: `mfderiv_eq_fderiv` + `ContinuousLinearMap.fderiv`
  on `e.toContinuousLinearMap` (with `⇑e = ⇑e.toContinuousLinearMap` by `rfl`).
- `pullbackInner_eval` is `private` in Pullback.lean — route through the public
  `Diffeomorph.pullbackMetric_inner` via a defeq `show … (pullbackMetric …).inner …`.
  Metric equality: mirror `pullbackMetric_refl` — `unfold Diffeomorph.pullbackMetric; congr 1`
  after proving the `inner` fields equal (no metric `ext` lemma exists).

## Next (step 5) needs from here

`pullbackMetric_round_eq` + `metricRm04Std_pullback` ⇒ curvature invariance under
`sphereDiffeo` (needs the heavier sphere instances: `BoundarylessManifold (𝓡 n)`,
`IsManifold (𝓡 n) 1`, `IsManifold (𝓡 n) (∞+1)` — verify availability/`of_le`).

## 2026-07-23: faithfulness for quotient-action assembly

Added and verified `sphereDiffeo_inj`: two ambient linear isometries whose
restrictions to the unit sphere agree are equal.  The proof normalizes each
nonzero ambient vector to the unit sphere and rescales; the zero case is
immediate.

This is the faithfulness lemma needed when the conjugated universal-cover deck
action is represented by ambient orthogonal maps: the group-law equations can
be checked after applying `sphereDiffeo`, then reflected back to the ambient
maps.  The local lemma is complete; it does not itself construct the conjugated
representation or solve the global Cartan classification.
