import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureLimitGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureLimitConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureLimitNoncollapse
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Invariance

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]

theorem highCurvatureFlowSequence_ancient_kappa_limit
    {T theta kappa : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hconnected : ConnectedSpace P.limit.M)
    (hkappa : 0 < kappa) (hbelow : SpatiallyKappaNoncollapsedBelowScale S kappa 1)
    (N : ℕ → ℕ)
    (F : ∀ n, ℕ → ℝ → SmoothRiemannianMetric I3 (metricSourceOpenSubset P.maps n))
    (hsource : ∀ n i, (metricSourceOpenSubset P.maps n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n i s (y : metricSourceOpenSubset P.maps n) (v w : TangentSpace I3 y),
      (F n i s).inner y v w =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (i + N n))).S.base.metric s).inner
          (P.maps.partialDiffeomorph (i + N n) y)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w))
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M)
    (hG0 : G 0 = P.limit.metric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    (hconv : ∀ n, ∀ K : Set (metricSourceOpenSubset P.maps n), IsCompact K →
      ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
        ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p (F n (rho i - N n) s)
            ((G s).restrictOpen (metricSourceOpenSubset P.maps n))
            (P.limit.metric.restrictOpen (metricSourceOpenSubset P.maps n)) < epsilon) :
    let L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval := {
      M := P.limit.M
      basepoint := P.limit.basepoint
      S := { base.metric := G }
      isSolution := hGsol }
    IsAncientKappaSolution kappa L ∧ PointedFlowScalarAtBase L 1 ∧
      PointedFlowScalarBounded L 1 := by
  let L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval := {
    M := P.limit.M
    basepoint := P.limit.basepoint
    S := { base.metric := G }
    isSolution := hGsol }
  have hgeom := highCurvatureFlowSequence_ancient_limit_geometry
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar P N F hsource hmetric
    rho hrho G hG0 hGsol hconv
  have hpointed := highCurvatureFlowSequence_ancient_limit_pointed_convergence
    hT S hS x t htmem htpos hpos P N F hsource hmetric rho hrho G hconv
  have hbase : PointedFlowScalarAtBase L 1 := by
    change metricScalarAt (G 0) P.limit.basepoint = 1
    rw [hG0]
    apply metricScalar_base_eq_one_of_canonical_metricConvergence P.maps
    · intro K hK
      have hc := P.convergence.metrics.converges K hK 2
      rwa [show P.convergence.metrics.domain =
        CanonicalMetricCompactness.canonicalSourceData P.maps from funext hcanonical] at hc
    · exact fun i => highCurvatureFlowSequence_scalar_at_base
        hT S hS x t htmem htpos hpos (P.subseq i)
  have hbound : PointedFlowScalarBounded L 1 := fun s hs y => (hgeom s hs).2.1 y
  refine ⟨⟨hkappa, rfl, rfl, hconnected, ?_, ?_, ⟨1, hbound⟩, ?_, ?_⟩, hbase, hbound⟩
  · intro s hs
    exact (hgeom s hs).2.2.complete
  · intro s hs y n c v w
    have hop := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (G s) y (by simp [ThreeSpace])).mpr ((hgeom s hs).1 y)
    have hq := mem_algebraicCurvatureOperatorNonnegativeCone.mp hop n c v w
    change 0 ≤ ∑ i, ∑ j, c i * c j * metricRm04 (G s) y (vec4 (v i) (w i) (w j) (v j))
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt_coe,
      tensor04StandardAt, metricRm04_apply] using hq
  · intro time B hcurv
    obtain ⟨Psi, _hPsi, C, hC⟩ := hpointed time time.property
    have hnc := highCurvatureFlowSequence_noncollapsed_of_pointed_convergence
      hT S hS x t htmem htpos hpos htheta htlower hscalar hkappa hbelow time time.property
      (P.subseq ∘ rho) (P.strictMono.tendsto_atTop.comp hrho.tendsto_atTop)
      { P.limit with metric := G time } Psi C hC (hgeom time time.property).2.2.complete
    refine ⟨hkappa, ?_⟩
    rw [FlowMetricBall.volume_eq_riemannianVolumeMeasure, FlowMetricBall.set_eq_riemannianBallOf]
    have hvol := hnc B.center B.radius (mem_univ _) B.radius_pos hcurv
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    simpa only [hdim, ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow B.radius_pos.le] using hvol
  · apply pointedFlowNotFlat_of_scalar_ne_zero L (t := 0) (by simp) L.basepoint
    change L.S.scalar 0 L.basepoint ≠ 0
    rw [show L.S.scalar 0 L.basepoint = 1 from hbase]
    exact one_ne_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
