# Surface classification: exact dependency route

This is a file-specific research/handoff note for the entropy-backward-limit
paragraph of `thm:ksol-two-dimensional-classification`, not a competing
Chapter 23 plan. The current KAPPA_COMPACTNESS_PLAN was read. No pending or
lower file was changed, and no Lean/Lake/REPL, build, or commit was run.

## Native objects and true earlier-chapter frontiers

- `CanonicalNeighborhood/ModelWitness.lean:358`,
  `CanonicalNeighborhood.IsAncientKappaSolution kappa F`, is dimension-generic
  on actual PointedFlowData. It stores positive kappa, carrier Iic 0, regular
  Iio 0, connectedness, complete slices, nonnegative curvature operator, one
  global scalar bound, all-scale noncollapsing and nonflatness. The Ricci-flow
  equation is in F.isSolution. For this theorem specialize the existing
  finite model dimension to two; do not create a new surface-kappa hierarchy.
- `Geometry/RicciSoliton/Defs.lean:18`,
  `Geometry.isGradientRicciSoliton g f sigma`, is the actual tensor equation
  Ric + Hess f = (sigma/2) g for a smooth potential. Basic.lean supplies
  `scalar_add_laplacian`, `scalar_add_delta`, `dScalar_eq_two_ricci_grad`,
  and `exists_hamilton_constant`. The current source/PLAN contains only
  those fundamental identities, not complete 2D shrinker classification.
- The book's earlier `thm:complete-two-dimensional-shrinker-classification`
  (chapter `ch:three-dimensional-shrinkers`) gives Gaussian, round sphere,
  and round projective plane. In the nonflat branch it gives compactness
  and constant positive scalar curvature. This is genuinely earlier work,
  not a Chapter 24 dependency and not provided by the current soliton equation.
- Chapter 22's `thm:red-asymptotic-shrinker` supplies actual pointed blow-down
  flow convergence, a smooth potential obeying the shrinker equation,
  completeness, nonflatness, nonnegative curvature and noncollapsing. At
  backward time theta=1, its equation has sigma=1 in the native convention.
  Choosing a sequence tau_i->infinity and low-reduced-length centers q_i
  does NOT follow merely from ordinary metric/flow compactness.
- The supplied branch was inspected read-only at
  refs/remotes/ch23-audit/perelman-l-geometry (fbf766dc1). Its
  L_GEOMETRY_STATUS and latest L_GEOMETRY_PLAN entries explicitly leave
  geometric no-mass-loss and the P3 asymptotic shrinker unproved. The remaining
  named mathematical obstruction is moving-sequence common compact
  confinement/equicoercivity, equivalently the uniform moving-center
  quadratic/coercive common-tail input. P2 has actual fixed-space test and
  reverse-tail machinery (`redDensity_cc_lim`, `canon_ball_capture`,
  `redSrc_tail_le`) and complete-flow attainment/measurability
  (`exists_lSegAtt_rm`, `redDensity_meas_rm`), but these are not the shrinker.
  Some older LGeometry source is present in dev; its absent status file and
  the unmerged branch must not be conflated. No new import or merge was made.
- Scalar positivity in current KappaSolutions/ScalarPositive is explicitly
  dimension THREE (`ancientKappa_scalar_pos`, line 234). It does not close
  R>0 for surfaces. The surface use needs the earlier scalar strong maximum
  principle/nonflatness argument and correct terminal-time continuity. The
  earlier complete-forward-flatness obligation is also not silently closed.

## Chapter 23's own geometric and analytic assembly

1. Apply the genuine Chapter 22 shrinker theorem and the earlier 2D shrinker
   classification. Select the theta=1 slice of the exact blow-down sequence
   tau_i^-1 h(-tau_i). Translate the actual flow comparison maps to their
   existing PointedRiemannianCGMaps slice, not an arbitrary convergence map.
2. `CompactLimitGlobalization.compactLimit_eventually_globalizes` is already
   landed/verified in the parent record. From compact limit and connected
   approximants it returns eventual full source/target, an actual global
   Diffeomorph agreeing with BOTH pointed-map functions and basepoint, and
   CompactSpace for the selected approximant. As its underlying manifold
   is the original Sigma, one index suffices to install compactness of Sigma.
   This proves global smooth comparison, not metric equality or entropy
   invariance.
3. For each resulting actual Diffeomorph e_i, put
   g_i = e_i^*(tau_i^-1 h(-tau_i)) on the fixed compact limit. The existing
   `HCGCompactness.metricScalarAt_pullback` in
   `Metric/Convergence/CovariantDerivativePullback.lean:839` proves the true
   scalar naturality under global native Diffeomorph. It retains both
   boundaryless-manifold structures and the relevant smoothness instances.
4. A genuine Riemannian volume change-of-variables theorem is still needed
   to prove surfaceEntropy(g_i)=surfaceEntropy(tau_i^-1 h(-tau_i)). Native
   `Measure/Invariance.lean` proves chart transition and partition-of-unity
   independence, not yet this global Diffeomorph pushforward identity.
   `ParamEvaluation.lintegral_image_paramChartMap_mul_chartDensity_eq` and
   `chartLocalMeasure_lintegral_image_param_eq_t2` are concrete local building
   blocks. Searches found no current exported global
   MeasurePreserving(e, volume(pullback g), volume(g)) producer. Do not replace
   it with an assumed measure-preserving map or an assumed entropy identity.
5. `SurfaceEntropyBasic.surfaceEntropy_scaleMetric` supplies exact constant
   rescaling invariance in dimension two; `totalScalarCurvature_scaleMetric`
   gives invariance of C. Both are source-ready, not yet verified in this
   research pass. Scalar naturality + the true volume pushforward will give
   diffeomorphism invariance of both C and entropy.
6. Prove entropy continuity under the actual globally pulled-back smooth
   metric convergence on the fixed compact limit. Needed concrete outputs:
   scalar convergence, volume-density convergence, area convergence, and
   dominated convergence for R_i log(R_i A_i). The positive round-limit
   scalar and positive limiting area give eventual uniform positive lower
   bounds, so log causes no singularity. Compact smooth convergence gives
   uniform upper bounds. A finite chart/POU or fixed-density measure argument
   is required. `SmoothCGHConverges.scalar_converges` in Foundations/PointedMaps
   is genuine pointwise scalar transport; by itself it is not an integral
   convergence theorem and must not be treated as uniform domination.
7. Identify the limit minimum with the SAME C of the original flow. One may
   use Gauss--Bonnet and the actual Diffeomorph, but it is not necessary here:
   prove totalScalarCurvature is conserved along the surface flow using
   R_t=Delta R+R^2, (dmu)_t=-R dmu and integral Delta R=0; combine actual
   diffeomorphism/scaling invariance and total-scalar convergence. Then
   C_limit=C and the round-limit entropy equals C log C by the static equality
   clause. This produces `eq:ksol-surface-entropy-backward-limit` without a
   hidden Euler-characteristic identification.
8. Chapter 23 must still derive the entropy time derivative and monotonicity
   from this specific functional. SurfaceRicciAlgebra and SurfaceEntropySquares
   now contain source-written surface Ricci/Bochner/square calculations;
   SurfaceEntropyPoissonPairing supplies compatibility and pairing, not
   Poisson existence. The earlier smooth mean-zero Poisson producer remains
   needed. `volumeVariation_hasDerivAt` has an all-real-time regularity API
   (FamilyDefs lines 48 and 76), despite its name: localize/extend near each
   interior time rather than imposing global smoothness on an ancient interval.
   Continuity at t=0 must close AntitoneOn on Iic 0, not merely Iio 0.
9. The independent `SurfaceEntropyRigidity` leaf applies the actual static
   minimum to actual surfaceEntropy. A backward subsequence reaching C log C
   plus forward AntitoneOn suffices: for fixed t, eventually -tau_i<=t and
   N(t)<=N(-tau_i); taking that limit and the lower bound proves equality.
   No separate construction of the full t->-infinity limit is needed. Its
   equality clause gives spatially constant actual scalar curvature for
   EVERY t<=0, not only along the selected sequence. This is conditional
   on the exact still-needed entropy producer hypotheses, not classification.

## Remaining after scalar constancy

Chapter 23 still integrates A'=-C and the tensor ODE h_t=-R h to obtain
T=A(0)/C>0, R(t)=1/(T-t), and h(t)=((T-t)/T)h(0). The fixed covering and
round deck-group classification then use earlier uniformization/space-form
and covering/topology results. Neither scalar constancy nor a round limit
alone proves one fixed covering for every time. No Chapter 24 theorem is
used by this entropy route.
