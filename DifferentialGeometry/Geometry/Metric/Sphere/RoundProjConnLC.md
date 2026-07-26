# RoundProjConnLC.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, Step 5B (Gauss route), **Step B**: `projConn ≐ metricCov
roundMetric` on differentiable sections, via Koszul uniqueness.

## State (2026-06-30): DONE, real `lake build` verified sorry-free + warning-clean

`projConn_eq_metricCov : projConn Y x v = metricCov roundMetric Y x v` for `MDiffAt (T% Y) x`.
Everything below is proved with NO sorry.

## What worked (route + key lemmas)

- **`mfderiv_innerCoordFun` / `mfderiv_inner_left`** : `mfderiv ⟪w, F·⟫ x v = ⟪w, mfderiv F x v⟫` via
  `HasMFDerivAt.comp` of the CLM `innerSL ℝ w` with `F`'s `HasMFDerivAt`. (Needs local
  `haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ,E) (F x))`; `HasMFDerivAt.comp` takes the point
  explicitly first: `hL.comp x hF`.) Closed by `rw [hfun, hcomp.mfderiv]; rfl`.
- **`dIncl_mlieBracket`** (the feared crux, turned out CLEAN): for smooth `X Y`,
  `dIncl x [X,Y] = ambDeriv Y x (X x) − ambDeriv X x (Y x)`. **NO chart/Hessian needed.** Route:
  `ext_inner_left ℝ` → test against every `w`; reuse the PROVEN `embedDeriv_mlieBracket` on
  `innerCoordFun w = ⟪w, ι·⟫`; unfold `embedDeriv = vectorFieldAction`, `extDerivFun = mfderiv`
  (both `rfl`), apply the chain rule (`mfderiv_innerCoordFun` for the first level, `mfderiv_inner_left`
  + `dInclField_mdifferentiableAt` for the second `hsecond`); evaluate `embedDeriv_mlieBracket` at `x`
  via `DFunLike.congr_fun`, `inner_sub_right`.
- **`mfderiv_inner`** (B2 product rule) : `mfderiv ⟪F·,G·⟫ x v = ⟪mfderiv F x v, G x⟫ + ⟪F x, mfderiv G x v⟫`.
  Build via `isBoundedBilinearMap_inner.hasFDerivAt (F x, G x) |>.hasMFDerivAt` composed with the pair
  `b ↦ (F b, G b)` (`hF.hasMFDerivAt.prodMk hG.hasMFDerivAt`), `(hB.comp x hpair).mfderiv`. CRITICAL:
  the final extraction `(fderivInnerCLM (F x,G x)).comp (prod) v` RESISTS `simp`/`rw` of
  `comp_apply`/`prod_apply`/`fderivInnerCLM_apply` (CLM-application reductions don't fire) — but the
  whole LHS is **definitionally** `⟪F x, dG⟫ + ⟪dF, G x⟫`, so close by `change … ; ring`. (Do NOT use
  `HasFDerivAt.inner` of fst/snd — it adds a redundant `fst.prod snd`. Use `isBoundedBilinearMap_inner`
  directly for the clean single-comp derivative.)
- **`projConn_torsion`** : `projConnCD.torsion = 0`. `funext x; ext u v`; smooth-extend `u,v` via
  `ContMDiffSection.exists_eq_at` (pin level with explicit `∃ σ : Cₛ^∞⟮…⟯` type — `(n := ∞)` arg
  conflicts with the ambient `n`); `simp [Pi.zero_apply, ContinuousLinearMap.zero_apply]`;
  `cov.torsion_apply` (takes `cov` explicitly: `(projConnCD …).torsion_apply hXd hYd`); `sub_eq_zero`;
  inject `dIncl`; `dIncl_projConn` + `dIncl_mlieBracket` + orthProj-fixes-tangent
  (`← Submodule.starProjection_apply` + `starProjection_eq_self_iff.mpr`).
- **`projConn_metricCompat`** : `IsMetricCompatible projConnCD roundMetric`. `intro Y Z x hY hZ _ v`
  (here `Y Z` are plain `Π x, T_x` — NO `⇑`); `roundMetric_inner` + `mfderiv_inner` + `dIncl_projConn`;
  `congr 1`; two orthProj-self-adjoint helpers `horth`/`horth_right` from `starProjection_inner_eq_zero`.
  NOTE: the IsMetricCompatibleOn model is `𝓘(ℝ)` not `𝓘(ℝ,ℝ)` → use `erw [hmf]`; the RHS has
  `projConnCD.toFun` (`↑projConnCD`) not `projConn` → use `erw [dIncl_projConn]`.
- **`projConn_eq_metricCov`** (Koszul assembly) :
  `koszul_levi_civita_unique_of_torsionFree_metricCompatible projConnCD (metricCov g) projConn_torsion
  htor₂ projConn_metricCompat hMC₂ hY v`. `htor₂ = funext (leviCivitaConnectionOfMetric_isTorsionFree
  g ·)`. **`hMC₂` needs `IsMetricCompatible` (bundled) but `leviCivitaConnectionOfMetric_isMetricCompatible`
  gives `IsMetricCompatible_gen`** → bridge by the `exists_eq_at` + apply-`_gen` + `rw [hWy]` pattern
  (mirrors Defs.lean:301-308; `directionalDeriv W` becomes `mfderiv … v`). `metricCov = leviCivitaConnectionOfMetric`
  is defeq, so `exact` bridges.

## API gotchas (durable)
- `HasMFDerivAt.comp` takes the **point explicitly first** (`hg.comp x hf`); `torsion_apply` takes
  `cov` explicitly; `HasFDerivAt.inner` takes `𝕜` explicitly (`hf.inner ℝ hg`).
- `ContMDiffSection.exists_eq_at`: pin the smoothness level via an explicit `∃ σ : Cₛ^∞⟮…⟯` ascription
  (the `n` param name collides with the sphere-dim `n`).
- `IsMetricCompatible` (bundled) ≠ `IsMetricCompatible_gen`; bridge with exists_eq_at + apply.
- CLM-application reductions (`comp_apply`/`prod_apply`/rfl-lemmas) sometimes silently fail to fire in
  `simp only`/`rw` here — fall back to `change … ; ring` exploiting definitional equality.

## Next (Step C): `RoundShape.lean`
Shape operator = Id + Gauss value. All inputs now present: `dIncl_projConn`, `projConn_eq_metricCov`,
`dIncl_mlieBracket`, `mfderiv_inner`/`mfderiv_inner_left`. Differentiate `⟪dInclField Y b, ↑b⟫ = 0`
⇒ `⟪ambDeriv Y x v, ↑x⟫ = −roundInner x (Y x) v`; expand `riemannCurvatureAux (metricCov g)`, substitute
projConn via Step B, Gauss ⇒ `metricRm04StdAt … = ⟪X,X⟫⟪Y,Y⟫ − ⟪X,Y⟫²`. Sign: `D_X Y = ∇_X Y − ⟪X,Y⟫·x`.
