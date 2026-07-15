# CoordRm04Bridge.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, step 4. The `(0,4)` analogue of
`metricRicciAt_apply_eq_ricciTensor` — reduces the abstract Koszul curvature to the
explicit chart-Christoffel formula, the prerequisite for the one-point sphere
curvature computation.

## State: COMPLETE (sorry-free, verified green)

`metricRm04StdAt_eq_chartRiemannCLM` :
`metricRm04StdAt g x X Y Z W = g.inner x W (chartRiemannCLM g x X Y Z)`
(needs `[I.Boundaryless]` + the usual `[SigmaCompactSpace]`/`[T2Space]`/`[BoundarylessManifold]`
/`[CompleteSpace E]`/`[NeZero (finrank)]`). **Compiled first try.**

## Route (5-lemma composition, all pre-existing)

1. `metricRm04StdAt_apply` → `metricRm04At g x (vec4 X Y Z W)`.
2. `metricRm04At g x = riemannCurvature04At g (metricCov g) (metricCov_smooth g) x` (`rfl`).
3. `riemannCurvature04At_apply_const` (Riemann/Basic/Pointwise.lean:594, `@[simp]`) →
   `g.inner x W (riemannCurvatureAux (metricCov g) (tangentConstAt x X)(…Y)(…Z) x)`.
4. `riemannCurvatureAux_tangentConst_eq_riemannOp` (MetricLeviCivitaReconcile.lean:107) →
   `g.inner x W (riemannOp (metricCov g) x X Y Z)`. Needs the instance
   `ContMDiffCovariantDerivative (metricCov g) ∞`, supplied by `haveI := LeviCivita_isContMDiff g`
   (works because `LeviCivita g` is now DEFINITIONALLY `metricCov g` in this checkout).
5. `riemannOp (metricCov g) … = riemannOp (LeviCivita g) …` (`rfl`, defeq) then
   `riemannOp_eq_chartRiemannCLM_apply` (ChartBridge/RiemannBasisIdentity.lean:554) →
   `chartRiemannCLM g x X Y Z`.

## Next (step 5B, the hard math core)

Compute `chartRiemannCLM roundMetric x₀` at a pole: `chartRiemannCLM` is built from
`chartRiemannTensor` (← `chartChristoffel` ← `chartGramOnE roundMetric`). The round
metric's chart-Gram in a stereographic chart is the conformal `(2/(1+|y|²))²δ`; at the
pole `∂g(0)=0` ⇒ `chartChristoffel(0)=0` ⇒ `chartRiemannTensor(0) = ∂Γ` only. Evaluate ⇒
`g.inner x₀ X (chartRiemannCLM x₀ X Y Y) = Gram`. The heavy piece is computing
`chartGramOnE roundMetric` from `roundInner` + the stereographic differential
(`stereoInvFunAux`, `hasFDerivAt_stereoInvFunAux_comp_coe` in Mathlib's Sphere.lean).
This is a large explicit computation — likely a dedicated session / Pro consult.
