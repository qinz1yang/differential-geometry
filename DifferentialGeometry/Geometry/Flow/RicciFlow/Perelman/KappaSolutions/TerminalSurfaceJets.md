# TerminalSurfaceJets

Supplies the `hjets` hypothesis of
`StaticSurfaceLocalCompactness.static_surface_scalar_bddAbove_of_local_normalized_jets`
for the surface factor `P.h` of a `TerminalSurfaceProduct` over the terminal slice of a
`KLim` flow. Public: `terminal_surface_factor_local_jets`.

## Route actually used

For a centre `q : P.S` with `Q = R_{P.h}(q) > 0`:

1. `x := UniversalCover.proj (P.Phi (q, 0))` and
   `TerminalProductScalar.universalCover_product_scalar_eq` give `R_{g(0)}(x) = Q`,
   i.e. `F.S.scalar 0 x = Q` definitionally (`SolutionOn.scalar` is `metricScalarAt` of
   `base.metric`).
2. `KLim.curvatureNormalizedFlow` at `(t0, Q) = (0, Q)` based at `x` is again `KLim kappa`
   with base scalar one, and its time-zero metric is *definitionally*
   `scaleMetric Q hQ (F.S.base.metric 0)` after `paraTime_zero`
   (`curvatureNormalizedSolution` → `rescaledMetric` → `scaleMetric Q _ (g (paraTime ..))`).
   Hence `NormalizedKLimSpatialJets.exists_normalized_klim_spatial_jet_constants` applies
   at `s = 0` with constants chosen before `q` (private `klim_rescaled_terminal_jet_bound`).
3. Transport of the bound down to the factor, at the point `(y, 0)`:
   `curvDerivNorm m (Q • P.h) y ≤ curvDerivNorm m gP (y,0) = curvDerivNorm m
   (liftedMetric (Q • g)) (P.Phi (y,0)) = curvDerivNorm m (Q • g) (proj (P.Phi (y,0)))`,
   where `gP = Diffeomorph.pullbackMetricCross (liftedMetric (Q • g)) P.Phi`. The three
   steps are the deferred interfaces of `UpstreamProductCurvatureJets.lean`.
4. Transport of the distance hypothesis, in the opposite direction and **proved here**:
   `d_{Q•g}(x, proj (P.Phi (y,0))) ≤ d_{liftedMetric (Q•g)}(P.Phi (q,0), P.Phi (y,0))
   = d_{gP}((q,0),(y,0)) ≤ d_{Q•P.h}(q,y) ≤ A`.

## Non-obvious points

- The pullback of the *rescaled* lifted metric is the product `Q•P.h + Q ds²`, not
  `Q•P.h + ds²`. That is why the product interface carries an explicit line scale `b`
  and is applied with `b = Q`; the alternative (an `ℝ`-rescaling diffeomorphism composed
  with `P.Phi`) was rejected as more construction for no gain.
- `(liftedMetric (scaleMetric c hc g)).inner x' v w = c * (liftedMetric g).inner x' v w`
  holds by `rfl` (private `liftedMetric_scaleMetric_inner`): `liftedMetric` is
  `inner x' := g.inner (proj x')` and `scaleMetric_inner` is `rfl`.
- `CrossModelBallTransport.crossModelBall_edist_le_of_pullback_inner` is `private`, so the
  path-length comparison is re-proved here as `edistOf_le_of_pullback_inner` and used twice:
  for `UniversalCover.proj` (`mfderiv = id` by `UniversalCover.hasMFDerivAt_proj`) and for
  the slice `y ↦ (y, s)` (`mfderiv_prod_left`).
- `rw` fails inside the product inner-product statements: the goal
  `gP.inner (z,s) (v,a) (w,c) = …` is not type-correct at `implicit` transparency
  (`TangentSpace (I.prod 𝓘(ℝ,ℝ)) (z,s)` vs `TangentSpace I z × ℝ`), so `rewrite` refuses to
  find patterns after a first rewrite. Both places are therefore closed in term mode
  (`Eq.trans`/`congrArg`) or with `exact` after the rewrites.
- `TerminalSurfaceProduct` needs only `[LocallyPathConnectedSpace F.M]`,
  `[SemilocallySimplyConnectedSpace F.M]`, `[Inhabited F.M]` on the carrier (checked with
  `#check @TerminalSurfaceProduct`), all three available as local instances without `hK`;
  `ConnectedSpace F.M` is *not* needed to state the theorem and is introduced inside the
  proofs from `hK.connected` (the covering instances used by `curvDerivNorm_liftedMetric`
  need it).
- The selected-ball hypotheses (`r`, the local scalar bound, `A + 1/2 < r√Q`) are unused:
  the constants come from the three-dimensional flow, not from a surface blow-up. They are
  kept in the public statement only to match `hjets` verbatim.

## Verification

`LEAN_NUM_THREADS=2 lake env lean` on the import-merged concatenation of the three new
files (the module `TerminalSurfaceJets.lean` itself has no artifact for
`UpstreamProductCurvatureJets` yet): 25.4 s, output only the three interface `sorry`
warnings. No error, no other warning.
