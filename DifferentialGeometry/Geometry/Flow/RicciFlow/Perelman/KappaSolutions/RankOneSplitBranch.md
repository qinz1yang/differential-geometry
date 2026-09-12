# Rank-one branch: fixed whole-flow splitting audit

## Scope and status

Documentation-only audit, 2026-09-08, in `codex/gradient-ricci-solitons`.
Parent requested a bounded review of the Chapter 18 input needed by
Chapter 23, not an implementation of Chapter 18 or Chapter 24. This new
note is the only file changed. No Lean declaration, `sorry`, competing
product/cover structure, lower-file edit, root import or commit was made.
No Lean/Lake/REPL/check/build or fresh axiom audit was run.

The shared wrapper does not claim Markdown-only files; this note is the
explicit documentation scope. Parent retains every pending Lean source.
Live WORKING_STATUS grants Chapter 23's parent the 09:38 UTC exclusive
verification window and keeps all children source-only.

**Conclusion:** the inspected native APIs do not yet supply a single
fixed universal-cover product for an entire complete ancient flow.
The nearest verified global product theorem is a static theorem. The
strong-maximum APIs found are not the complete-flow curvature-rank
trichotomy. The correct earlier obligation can be stated using existing
`PointedFlowData`, `UniversalCover`, `liftedMetric`, and `Diffeomorph`;
there is no reason to invent a new splitting hierarchy.

## Exact book boundary

`master05a.tex:28685-28785`, `sec:ksol-split-branch`,
`thm:ksol-three-dimensional-split-branch`, first invokes Chapter 18 to
obtain a fixed product

    (UniversalCover M, lifted g(t)) = (Sigma, h(t)) x (Real, ds^2).

This is before the surface classification. If the null curvature plane
occurs at terminal time zero, the proof first extends the complete
bounded-curvature flow past zero and glues by uniqueness. Native
`ancientTimeInterval.regular = Iio 0`; zero is only in the carrier.
It must not be passed as a regular time to an interior strong maximum
principle.

The invoked Chapter 18 statement is
`thm:curvature-spacetime-trichotomy`, lines 19916-20053, particularly
`eq:smp-whole-flow-product` at 19947. Its assumptions are complete,
connected, nonempty boundaryless dimension three, nonnegative curvature
operator, and a global spatial curvature bound on every compact regular
time slab. Its whole-flow upgrade explicitly depends on:

- `PC-F-COMPLETE-BOUNDED-CURVATURE-RICCI-FLOW-SHORT-TIME-EXISTENCE`;
- `PC-F-COMPLETE-RICCI-FLOW-UNIQUENESS`.

The book cites MSM 144 Appendix D, Theorems D.2-D.3, and Kotschwar's
complete bounded-curvature uniqueness theorem. Short-time existence is
needed in dimensions three and two, not merely for compact 3-manifolds.

The additional geometric mechanism is
`cor:curvature-fixed-bundle-rank-interval` (19313),
`prop:rank-one-uhlenbeck-line-fixed` (19606), and
`eq:smp-fixed-line-one-form` (20037). One Uhlenbeck gauge on the entire
interval gives a fixed physical unit parallel vector X, not only a
separate line distribution at each time. Then Ric(X,-) = 0 makes
g(t)(X,-) independent of t. One primitive, its one zero level, and the
flow of X give the same product diffeomorphism for every t. Restricting
the PDE gives the actual surface Ricci flow.

Here rank one means the curvature operator on two-forms. The cylindrical
Ricci tensor has rank two. A tensor file named `RankOneSupport` is not
evidence for this geometric assertion.

## Closest native declarations and their actual qualifications

Paths below are relative to `DifferentialGeometry/`.

### Strong maximum and nullspace pieces

- `Analysis/Parabolic/MaximumPrinciple/ParallelTensorNullDistribution.lean`:
  `parallelTensorNullDirection_of_terminal_null` (32),
  `parallelTensorNullSpace_of_terminal_null` (118), and
  `parallelTensorNullSpace_eq_transported_terminal_of_constant_finrank`
  (187). These require CompactSpace and ConnectedSpace, an explicitly
  supplied family of cone-preserving fiber transport equivalences, a
  scalarized `IsHeatPotSupersolutionOn`, the gradient/Laplacian continuity
  data, a uniform lower potential bound, and tau in Ioo 0 T. The final
  theorem takes constant kernel finrank as an input. The tensors are
  Tensor0SSpace 2 and tangent-vector left kernels. These results neither
  construct the curvature-operator null bundle nor prove its rank
  persistence, and do not produce the same physical vector X for all t.
- `Analysis/Parabolic/MaximumPrinciple/ParallelConeStrong.lean:33,104`
  and `ParallelDualConeStrong.lean:30,83` similarly require CompactSpace,
  supplied `LinearIsometricTransport`, a parallel cone family and a
  scalarized supersolution. Their smooth-metric variants remove the
  explicit continuity subgoals, not compactness or the supersolution
  obligation. They are not the missing complete noncompact producer.
- `Analysis/Parabolic/MaximumPrinciple/Tensor/Strong.lean` proves strict
  positive definiteness from strict supersolution/reaction hypotheses.
  It is not the weak-positivity equality-case rank trichotomy.
- `Geometry/Connection/ParallelTransport/PositiveSemidefiniteCone.lean:289`,
  `twoTensorNullSpace_finrank_eq_parallelTransportBetween`, really uses
  native parallel transport along a supplied C2 curve for a fixed metric.
  It compares a tensor with its transported copy. It does not establish
  that a curvature field equals that transported copy, nor compare times.

There is genuine Uhlenbeck gauge construction, so this part should not
be reported as absent: `Geometry/Flow/RicciFlow/Estimates/Uhlenbeck/`
`FrameExistence.lean:129`, `exists_uhlenbeckFrame_of_finrank`, takes an
actual SolutionOn on `RealTimeInterval.closed 0 T`, IsSolutionOn,
boundaryless I and tangent finrank three. Without CompactSpace it
constructs pointwise orthonormal bases, an identity-initial matrix iota,
the actual `FrameRicciODEInFrameOn`, and constant Gram matrix.
`solutionUhlenbeckIota_spec` is at 78; `Isometry.lean:708`,
`uhlenbeckEndomorphism_isometry`, gives the corresponding full metric
identity. The chosen bases are only pointwise; the displayed output does
not assert their spatial smoothness or provide a smooth fixed null
subbundle. It is a one-sided finite-window gauge, not the same gauge
based at one reference time over the whole ancient interval. There is
still no rank-persistence/fixed-physical-line conclusion here.

These were source inspections. No fresh verification or clean axiom
claim is inferred merely from the presence of their source/artifacts.

### Actual universal cover and lifted static metrics

- `Topology/Covering/CoveringMap.lean:238` gives
  `UniversalCover.proj_isCoveringMap`; its `simplyConnectedSpace` instance
  is at 659. `Topology/Covering/Manifold.lean` supplies the actual smooth
  cover atlas and smooth projection. The cover type is
  `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M`.
- `Geometry/Metric/UniversalCover/Metric.lean` provides
  `UniversalCover.liftedMetric`, `liftedMetric_inner_eq`, the compatible
  cover Riemannian bundle/emetric construction, and regular-space data.
- `Geometry/Metric/UniversalCover/Curvature.lean:54`,
  `metricRm_lifted`, identifies the actual four-slot metric curvature
  under the canonical cover chart tangent identification. Its
  `ricciTensor_lifted_natural` at 348 additionally takes
  `chartRiemannBasisIdentity` for the base and lifted metric. Do not
  silently omit these prerequisites when using that particular lemma.
- `Geometry/Metric/UniversalCover/Completeness.lean:532`,
  `completeSpace_of_complete`, lifts actual completeness. It requires a
  compatible complete base Riemannian metric-space context, regularity
  of the cover, and explicit base/cover enorm identifications. It returns
  CompleteSpace for `ucPseudoEMetricSpace`, not an arbitrary cover metric.
- `Geometry/Metric/UniversalCover/DeckIsometry.lean:71`, `deck_inner`,
  proves the full bilinear metric identity for the actual fundamental
  group deck action. Applying it separately to g(t) proves that every
  fixed deck transformation is an isometry for every lifted metric.

No native producer lifting an actual `SolutionOn`/`PointedFlowData` to
this cover was located. The static metric and curvature naturality APIs
are useful ingredients, not themselves a jointly regular Ricci-flow
lift. The eventual upstream product statement can refer directly to
`liftedMetric (F.S.family.metric t)` without first inventing a second
flow record for the cover; its two-dimensional factor should nevertheless
be an actual `PointedFlowData` with its own `isSolution` proof.

### Static global product: genuinely checked, but not whole-flow

`Geometry/Topology/AffineFunctionSplitting.lean:42`,
`affineFunction_splitting`, constructs the actual complete connected
zero-level surface, its model `affineFunctionKernel`, atlas, induced
metric, and a global smooth diffeomorphism. It requires a compatible
complete connected positive-dimensional boundaryless metric manifold,
an actual smooth b, unit gradient, and Hessian zero. Its output is the
full bilinear product identity with line coefficient exactly 1 and
mixed terms zero. Its note records an empty focused check, targeted
build and standard-three-axiom audit.

`Perelman/KappaSolutions/TimeZeroSplitting.lean` derives those b
hypotheses from an actual line and nonnegative Ricci, then invokes that
theorem. Its parent note records the 21.1-second empty focused check,
named build and standard-three-axiom audit; WORKING_STATUS lists commit
847ba5852. It only concerns one metric. Neither theorem produces the
one all-time b/X/one-form required above.

No native smooth product-metric constructor was found in the searched
metric/flow files. Use the existing Diffeomorph plus full bilinear
pullback identity; an Isometry for the default max metric on a Cartesian
product would be the wrong public assertion.

### Complete-flow analytic inputs remain separate

`Geometry/Flow/RicciFlow/ShortTime/Existence.lean:35`,
`ricci_flow_short_time_existence`, is all-dimensional but requires
CompactSpace. `Extension/Construction.lean:29,60` supplies compact
dimension-three uniform existence/restart with actual metric-jet inputs.
Its `ricci_flow_forward_unique` at 126 retains CompactSpace, as does
`Uniqueness/Forward/SmoothSolutions.forward_unique_of_gram`.
Even if the original base is compact, its cylindrical universal cover
is not; these hypotheses cannot be discharged by that observation.

`Extension/Construction.extend_construction_of_restart` glues supplied
restart data and assumes agreement on the overlap. It does not create
the complete restart or prove complete uniqueness.

The existing new `UpstreamForwardFlatness.complete_forward_flatness`
has one explicitly authorized upstream `sorry`: a flat slice remains
flat on a complete bounded-curvature forward slab. Its note records
elaboration and the expected sorryAx audit. It is only the stationary
flat specialization and cannot be used as product-flow uniqueness.

## Recommended exact earlier obligation, not a new declaration yet

Prefer the general Chapter 18 whole-flow trichotomy on an actual open
regular interval, followed by its terminal-inclusive ancient corollary.
For the direct Chapter 23 consumer, the following is the precise
mathematical signature of that corollary, with existing native types.
This is a design specification, not claimed Lean source or a new theorem.

Inputs:

1. `F : PointedFlowData (I := I) ancientTimeInterval`, finrank E = 3,
   with its actual manifold instances, and boundaryless I.
2. ConnectedSpace F.M; for every t <= 0, the actual
   `MetricComplete (F.atTime t)`.
3. `PointedFlowNonnegativeCurvatureOperator F t` for every t <= 0.
4. Every closed finite slab [a,b], a < b <= 0, has one C >= 0 with
   `F.rmNormSq t x <= C` for all t in [a,b] and all x. Including b = 0
   supplies the complete bounded-curvature terminal-extension input.
5. `PointedFlowNotFlat F`.
6. An actual null plane at x and some t <= 0: vectors v,w with positive
   metric Gram determinant and
   `F.S.base.rm04 t x (vec4 v w w v) = 0`.
   In dimension three this is the nonzero null-bivector alternative;
   selecting it from failure of strict curvature-operator positivity
   is a finite-dimensional algebra step, not an assumed splitting.

Output actual objects, existentially packaged without a new hierarchy:

- A finite-dimensional real inner-product model E2 of finrank 2, with its native
  smooth-manifold model I2 = `𝓘(Real,E2)` (the existing affine-function
  construction naturally gives a fixed two-dimensional kernel model).
- `G : PointedFlowData (I := I2) ancientTimeInterval`, on ONE underlying
  surface G.M, connected and simply connected, complete at every t <= 0,
  with positive Gaussian curvature at every such time. In dimension two,
  actual scalar positivity is an equivalent native way to expose this.
- ONE fixed smooth diffeomorphism

      Phi : (G.M x Real) ≃ₘ⟮I2.prod 𝓘(Real,Real), I⟯ UniversalCover F.M

  such that for every t <= 0, y in G.M, s,a,c in Real and tangent v,w,

      (liftedMetric (F.S.family.metric t)).inner (Phi (y,s))
          (mfderiv _ _ Phi (y,s) (v,a))
          (mfderiv _ _ Phi (y,s) (w,c))
        = (G.S.family.metric t).inner y v w + a*c.

The usual locally path connected/semilocally simply connected and
inhabited cover prerequisites must be instantiated from F's actual
smooth manifold and basepoint, not supplied as unexplained new geometry.
The fixed cover is the native universal cover, not an arbitrary map with
an asserted covering property. No time-dependent Phi(t) is substituted.
One can mark Phi(G.basepoint,0) at the canonical cover basepoint by
normalizing the affine function, but this marking is not needed for the
rank-one classification and need not burden its first upstream statement.

This corollary contains ONLY the earlier whole-flow splitting content.
It does not assume or conclude kappa noncollapsing, compactness/roundness
of G.M, a round cylinder, a sphere cover, or a classified deck group.
For an interior null plane the open-interval theorem suffices; the
terminal-null case additionally uses exactly the earlier complete
extension/uniqueness route above. Parent should retain this distinction
when deciding the separate Upstream leaf boundaries.

## Chapter 23 obligations after that input lands

These remain Chapter 23 work and must not be absorbed into the proposed
Chapter 18 theorem:

1. Lift actual all-scale spatial noncollapsing to the universal cover.
   This needs genuine ball capture under the local isometry and the
   Riemannian-volume comparison. `deck_inner` by itself proves neither.
2. Transfer actual curvature control to the product ball and prove

       kappa*r^3 <= Vol B_product((y,0),r)
                    <= (2*r)*Area B_surface(y,r).

   Hence the factor constant is exactly kappa/2, for every r > 0.
   Actual product Riemannian volume is required, not merely an abstract
   product-measure bound. No suitable Riemannian product-volume or
   cover-noncollapsing producer was found by the scoped native search.
   `UpstreamVolumeNaturality` is a separately open global-diffeomorphism
   volume obligation; it is not already the ball/cover/product theorem.
3. Transfer nonflatness, the actual global curvature bound and curvature
   sign to the SAME factor G, and construct the existing
   `IsAncientKappaSolution (kappa/2) G`. Do not assume this record in an
   upstream splitting statement.
4. Apply the actual Chapter 23 surface classification. The current
   `ancientKappaSurface_fixed_round_cover` consumes an actual factor
   PointedFlowData and its IsAncientKappaSolution, producing ONE sphere
   covering map for all times and the factor `2*(T-t)` with T > 0.
   Its own pending/upstream verification boundary remains as in its note.
5. Conjugate the genuine fixed deck action to the product, prove each
   deck map preserves the Ricci eigenspaces, and obtain
   `(y,s) -> (A*y, epsilon*s+c)`. Pure CylinderDeckAlgebra does not itself
   supply this geometric decomposition.
6. Establish the actual translation-quotient volume bound
   `Vol B <= pi*L*r^2` at `r = sqrt(L*rho)`,
   `rho = sqrt(T-t)`, and use noncollapsing to exclude translations.
   Then the separate algebra gives the three deck groups in
   `eq:ksol-cylinder-deck-list`; orientation exclusion is also separate.

The round metric's coefficient is exactly 2*(T-t), the static line
coefficient is 1, the factor noncollapse constant is kappa/2, and the
translation-collapse estimate has coefficient pi*L. None is an unspecified
normalization constant or a loss hidden in an interface.

## Follow-up audit: cover and surface noncollapse (2026-09-08, source only)

This is a read-only native-source audit plus this note append, while the
parent owns the verification window. The checkout remains
`codex/gradient-ricci-solitons`. No Lean source, compiler, artifact, root
import, claim or commit was changed. Native declarations below were read;
their existence is not a new axiom audit. This refines, rather than
supersedes, the uncompleted obligations above.

### Exact consumer and the available fixed product

`ModelWitness.lean:322,358` uses the actual spatial tensor predicate:
for every `FlowTime` and actual `FlowMetricBall`, the hypothesis is
`r^4 * rmNormSq <= 1` throughout the one time-slice ball, and the
conclusion is `ofReal kappa * ofReal r ^ finrank E <= B.volume`, with
`0 < kappa` separately retained. `Noncollapsing/Defs.lean:40-62`
defines that ball using `riemannianEDistOf (S.base.metric t)` and its
volume using the actual `volumeMeasureOn S.family time`. No parabolic
slab is required. The transfer must preserve this predicate, including
terminal time zero; scalar-controlled noncollapse is not a substitute.

The now-written `UpstreamAncientSplitting.lean:64`
`ancient_fixed_universal_cover_product_of_null_plane` returns the SAME
actual `G : PointedFlowData (I := real-two-model) ancientTimeInterval`,
connectedness, simple connectedness, complete slices, positive scalar,
and ONE actual cross-model `Phi : G.M x Real -> UniversalCover F.M`.
Its full bilinear identity holds for every `t <= 0`. It does not return
noncollapse or a global scalar bound for G. Its one explicit earlier
Chapter 18 obligation is not proof of those Chapter 23 consequences.

At a fixed t, construct the genuine product metric without any new
metric-existence assumption by

    gP := Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (F.S.family.metric t)) Phi.

`Geometry/Metric/PullbackCross.lean:144,217` gives the actual smooth
metric and its inner-product formula. The upstream identity then gives
`gP.inner (y,s) (v,a) (w,c) = h.inner y v w + a*c`, where
`h = G.S.family.metric t`. This avoids importing the separate open
`CurveShortening.exists_coverProductMetric` constructor. The product
model's default norm is not an assertion about the Riemannian distance.

### Cover: proved pieces and the precise missing gluing

Native producers, with their actual qualifications:

- `Topology/Covering/CoveringMap.lean:238`,
  `UniversalCover.proj_isCoveringMap`, and
  `Topology/Covering/Manifold.lean:213`, `proj_contMDiff`, give the
  genuine topological covering and smooth projection. Manifold/basepoint
  assumptions supply local path connectedness, semilocal simple
  connectedness and inhabitation as in `UpstreamAncientSplitting`.
- `Geometry/Metric/UniversalCover/Completeness.lean:50`,
  `hasMFDerivAt_proj`, identifies the actual differential with the model
  identity. `Metric.lean:98`, `liftedMetric_inner_eq`, identifies the
  actual fiber metrics. These are exact local metric isometry data.
- `Completeness.lean:101` contains the PRIVATE proof
  `proj_pathELength_eq` for actual C1 curves on `[0,1]`. Its hypotheses
  explicitly identify both tangent enorms with the square roots of the
  given metrics. It cannot be called as a public API or generalized in
  place in this lane. `:148`, `proj_lipschitzWith_one`, is public but
  additionally installs the compatible base Riemannian emetric and
  uses the actual cover `ucPseudoEMetricSpace`. It proves only
  `d_base(proj x,proj y) <= d_cover(x,y)`.
- `Geometry/Metric/UniversalCover/Curvature.lean:54`,
  `metricRm_lifted`, is the actual four-slot curvature identity, with
  identical model vectors and no chart-Riemann-identity assumption.
  In contrast the later `ricciTensor_lifted_natural` requires explicit
  `chartRiemannBasisIdentity` hypotheses. For this task, transport the
  four-slot tensor first and use an actual orthonormal basis to deduce
  its exact squared norm; do not add those extra chart identities.
- Mathlib `Topology/Homotopy/Lifting.lean:259-262` gives the actual
  continuous `IsCoveringMap.liftPath`, its projection equation and
  its initial value. It does not directly give C1 regularity or length.

The first missing geometric statement is the SAME-radius open-ball
surjectivity

    proj '' B_lift(x,r) = B_g(proj x,r),   r > 0.

The easy inclusion is already supported by the differential/length
proof above. For the reverse inclusion, choose a C1 base path of length
less than r, lift the actual path, prove its C1 regularity locally using
the covering's smooth inverse sheets, and identify lengths by the
differential identity. Mathlib `IsLocalDiffeomorphAt.localInverse_*`
(`Geometry/Manifold/LocalDiffeomorph.lean:184-232`) supplies the inverse
identities and smoothness once projection is packaged as a local
diffeomorphism. Its packaging can also use the existing cover charts.
`DistanceScaling.edistOf_iInf` at line 42 provides a route entirely in
actual metric lengths, avoiding unrelated ambient distance instances.
This open-ball argument does not need minimizing geodesics or even
metric completeness; the covering property lifts the whole compact
parameter path. Cover completeness remains relevant to other clauses.

The second missing statement is actual Riemannian-volume domination,

    volume_g (proj '' U) <= volume_lift U

for an open U (the lifted ball suffices). A local isometry alone is not
a global measure-preserving map: overlapping sheets may have arbitrary
multiplicity. Prove equality on injective smooth sheets using actual
chart-density/parameter-image integration; cover U by countably many
such sheets and disjointify the SOURCE pieces. Image subadditivity then
gives the inequality. Disjointifying only target pieces does not by
itself provide a measured source partition.

The concrete integration producer is
`Analysis/Integration/Measure/ParamEvaluation.lean:1192`,
`riemannianVolumeMeasure_image_param_eq`: an actual C1 partial
diffeomorphism from the model, a measurable parameter set inside its
source, and the integral of `ofReal (paramDensity g Psi)` against
`modelHaar`. The preceding `paramDensity_eq_abs_det_mul_chartDensity`
at line 249 supports the Jacobian calculation. No native cover-image
volume or cover-noncollapse endpoint was found in the scoped search.
`UpstreamVolumeNaturality.volumeMeasurePreserving_pullbackMetric` is
already an explicit earlier integration sorry; it is global and
SAME-model, so it neither directly applies to this noninjective cover
nor directly to the cross-model Phi. It must not silently stand in for
the missing sheet gluing or a cross-model naturality theorem.

After ball surjectivity and the exact curvature-norm identity, curvature
control on a lifted ball descends to every point of its base ball.
Apply `F`'s actual noncollapse there and then the volume inequality.
This proves static lifted noncollapse with the SAME kappa for every t;
no new `PointedFlowData` lift or cover-flow hierarchy is necessary just
to prove the factor's existing noncollapse field.

### Product: sharp constants, nearby proof, and remaining geometry

The smallest useful next leaf is the actual projection/distance/ball
calculation for the gP above (or for any actual smooth gP with the same
bilinear identity). It is near the checked native proof in
`Geometry/Topology/AffineZeroLevelCompleteness.lean:35`:
PRIVATE `edistOf_le_of_differential_contracting` maps actual C1 paths,
uses `mfderiv_comp_apply`, and compares the nonnegative square-root
integrands in `edistOf_iInf`. Duplicate its short proof in a NEW lane
leaf; do not edit or expose the private lower lemma in place.

The product identity immediately bounds the squared tangent length of
`Prod.fst` by gP. For `Prod.snd`, it bounds the ordinary squared real
derivative by gP. The same length argument therefore proves, sharply,

    d_h(y,z) <= d_gP((y,s),(z,u)),
    |s-u| <= d_gP((y,s),(z,u)),
    B_gP((y,0),r) subset B_h(y,r) x (-r,r).

State the distances using `riemannianEDistOf` (and `ENNReal.ofReal`
for the real distance) until compatible metric instances are actually
installed. The first two projections, or the equivalent projections
composed with `Phi.symm`, can also prove global-pullback distance
invariance by the same path argument in both directions. No exact
Pythagorean formula or global geodesic construction is needed here.
This small route is described only; no new implementation was started.

The remaining PRODUCT producers are genuine geometric work:

1. Actual Riemann curvature of gP is the pullback of h in its four
   horizontal slots and vanishes when any slot is vertical. Consequently
   its actual norm squared is exactly the surface norm squared. The
   four-slot connection computation is still required from the
   bilinear product identity; it does not follow merely from equal
   dimensions or the scalar norm estimate. Native global/local curvature
   pullback transport can move the already-proved tensor through Phi,
   but does not prove the product tensor decomposition itself.
2. The actual volume measure of gP is
   `(riemannianVolumeMeasure h).prod volume`. Derive this from the block
   product Gram matrix on genuine product coordinate charts and the
   parameter-image formula above, then glue locally. `chartModelBasis`
   on `E x Real` is chosen independently, so it is NOT definitionally
   the product of the two chosen bases. Account for this basis change
   and `modelHaar` normalization; a bare `Matrix.det_fromBlocks_zero₂₁` rewrite
   does not close that obligation.

Important negative result: the existing
`Extinction/CurveShortening/Product.lean:174` does have an actual
`exists_coverProductMetric`, but it is an explicit sorry. Moreover
`ProductGeometry.lean:181,220`,
`coverProduct_iterCov_rm04_apply` and `coverProduct_iterCov_normSq`,
are direct sorries in the current source (confirmed by its note).
They are not checked product-curvature producers to reuse as proofs,
and the circle/quotient development is outside this lane's ownership.
No Riemannian product-volume identity was found there.

Once (1), (2), and the cover transfer are genuinely available,
`measure_mono`, Mathlib `Measure.prod_prod` (Prod.lean:231) and the
actual Lebesgue interval volume give, in ENNReal,

    ofReal kappa * ofReal r ^ 3
      <= volume_gP (B_gP((y,0),r))
      <= ofReal (2*r) * volume_h (B_h(y,r)).

Cancel the finite strictly positive `ofReal (2*r)` to obtain exactly
`ofReal (kappa/2) * ofReal r ^ 2 <= volume_h (B_h(y,r))`.
Keep volumes extended-real throughout: even if finite ball volume has
not yet been established, this cancellation is valid and no unsafe
`.toReal` is needed. The geometric inclusion is where the factor 2
comes from, not an unspecified dimensional volume constant.

Finally, the upstream output already provides G's connectedness,
completeness and positive scalar. Nonflatness follows from the existing
`pointedFlowNotFlat_of_scalar_ne_zero`. The same product curvature
identity must still transport F's curvature-operator sign and global
scalar bound to G before assembling `IsAncientKappaSolution (kappa/2) G`.
The checked `SurfaceRmAlgebra.metricRm_normSq_eq_scalar_sq_of_finrank_two`
and its square-root version prove `|Rm_h|^2=R_h^2`, with coefficient 1;
they do not alone provide the missing comparison with F. No noncollapse,
curvature inheritance, volume bound or resulting kappa-solution record
has been inserted as a new interface in this audit.
