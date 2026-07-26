# RoundProjConn.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, Step 5B (Gauss route), **Step A**.
Builds the tangential-projection connection `projConnCD` on the round sphere as a bundled
`CovariantDerivative`, for the Koszul-uniqueness identification in Step B.

## State: DONE, sorry-free, **real `lake build` verified green** (not just `lake env lean`)

`projConnCD : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))`.

## Key design decisions (don't re-derive)

- **`CovariantDerivative` needs NO smoothness field.** The structure is `toFun` +
  `isCovariantDerivativeOnUniv` (`add` + `leibniz` only). The separate class
  `ContMDiffCovariantDerivative` is NOT needed for `projConn`, because Step B identifies it
  with `metricCov` via `koszul_levi_civita_unique_of_torsionFree_metricCompatible`, which needs
  only `torsion = 0` + `IsMetricCompatible`. ⇒ the de-privatization of
  `dIncl_apply_section_contMDiff` (RoundMetric) is unnecessary.
- **Fiber model = `EuclideanSpace ℝ (Fin n)`, NOT the ambient `E`.** `CovariantDerivative I F V`
  has `F` = model space of `I`. Conflating the two `E`s gives a
  `TopologicalSpace (TotalSpace E …)` synth failure.
- **`ambDeriv` (E-valued ambient derivative) is the load-bearing trick.** `mfderiv … (dInclField Y) x`
  has codomain `TangentSpace 𝓘(ℝ,E) (dInclField Y x)` — a per-point type synonym of `E`. Adding
  two of these at *different* image points fails `HAdd`/`Module` synthesis (Lean won't reduce the
  synonym during instance search). Fix: `ambDeriv Y x := (mfderiv … : TangentSpace (𝓡 n) x →L[ℝ] E)`
  — a **codomain ascription** (defeq to the mfderiv, since `TangentSpace 𝓘(ℝ,E) p = E`), so
  `ambDeriv Y x v : E` genuinely and all sums are `E + E`.
- **Characterization-only downstream.** `dIncl_projConn : dIncl x (projConn Y x v) =
  ↑((ℝ∙↑x)ᗮ).orthogonalProjection (ambDeriv Y x v)`. Every law injects `dIncl x`
  (`mfderiv_coe_sphere_injective`) and compares in `E` — no `dIncl⁻¹`/projection bookkeeping.
- `projConn Y x := (dInclEquiv x).symm.toCLM ∘L ((ℝ∙↑x)ᗮ.orthogonalProjection ∘L ambDeriv Y x)`,
  where `dInclEquiv x : T_x ≃L (ℝ∙↑x)ᗮ` corestricts `dIncl x` (injective + range = complement)
  and is upgraded to `≃L` by `LinearEquiv.toContinuousLinearEquiv` (finite-dim).

## API gotchas hit (all resolved)

- `orthogonalProjection` is `Submodule.orthogonalProjection` → dot-form `K.orthogonalProjection :
  E →L K`. NOT a bare root identifier. Import `Mathlib.Analysis.InnerProductSpace.Projection.Basic`.
- "orthProj fixes its subspace": `↑(K.orthogonalProjection w) = w` for `w ∈ K` via
  `← Submodule.starProjection_apply` then `Submodule.starProjection_eq_self_iff.mpr`. (No
  `orthogonalProjection_eq_self_iff`.)
- `ContMDiffAt.mdifferentiableAt` wants `(hn : n ≠ 0)` here, NOT `1 ≤ n` → pass `(by simp)`.
- `ContMDiff.contMDiff_tangentMap` (ContMDiffMFDeriv.lean:308): the `m+1 ≤ n` arg via `apply …; exact
  le_top`; using it as a term `(by simp)` leaves the output level `?m` unpinned.
- `LinearEquiv.toContinuousLinearEquiv` needs `[FiniteDimensional ℝ T_x]` **and** `[T2Space T_x]`;
  the `TangentSpace (𝓡 n) x` synonym does not inherit these → `haveI … := inferInstanceAs (… (EuclideanSpace ℝ (Fin n)))`.
- **Add/Leibniz product rules** use the model-space-codomain forms that already dodge the synonym:
  `mfderiv_add` (SpecificFunctions.lean:788, `(mfderiv% (f+g) z : … →L E') = …`) for `add`;
  `fromTangentSpace_mfderiv_smul_apply` (NormedSpace.lean:373) for `leibniz`. `NormedSpace.fromTangentSpace`
  is literally the identity (`toFun v := v`), and `extDerivFun g x v = fromTangentSpace _ (mfderiv% g x v)`
  — so the leibniz `df`-term lands *exactly* as the required `extDerivFun g x v` by defeq.
- `ambDeriv_add`: prove the **CLM-level** equation `ambDeriv (Y+Y') x = ambDeriv Y x + ambDeriv Y' x`
  first (`exact h` from `mfderiv_add`), THEN apply to `v`. Rewriting `ambDeriv_apply` at the value level
  re-exposes the `TangentSpace`-typed `+` and fails.
- `dInclField_mdifferentiableAt` (the only real sub-frontier): mirror `vectorFieldActionSmooth`
  (Connection/Realization/Embedding.lean:58) — `contMDiff_tangentMap` ∘ section, then
  `mdifferentiableAt_totalSpace` + `congr_of_eventuallyEq` with `trivializationAt_model_space_apply`.

## Next (Step B): `RoundProjConnLC.lean`

`projConn.toFun = metricCov roundMetric` on differentiable sections, via the Koszul engine:
- `projConnCD.torsion = 0` (B1: `dIncl (mlieBracket X Y) = ambient D_XV − D_YU` via
  `embedDeriv_mlieBracket`/`mpullback_mlieBracket`, lands in `(ℝ∙↑x)ᗮ` so orthProj fixes it;
  `torsion_eq_zero_iff`).
- `IsMetricCompatible projConnCD roundMetric` (B2: ambient inner-product product rule, orthProj
  corrections vanish by `⟪dIncl Z, ↑x⟫ = 0`).
- Then `koszul_levi_civita_unique_of_torsionFree_metricCompatible projConnCD (metricCov g) …` with
  `leviCivitaConnectionOfMetric_isLeviCivita.2`/`_isMetricCompatible`.
