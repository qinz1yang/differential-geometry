import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

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
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I3 M)]

theorem exists_highCurvatureFlowSequence_terminal_metric_limit
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) :
    ∃ P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      ConnectedSpace P.limit.M ∧
      (∀ n, IsCompact (closure (P.maps.source n))) ∧
      (∀ n, IsConnected (P.maps.source n)) ∧
      (∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) ∧
      MetricSourceCapture P.maps ∧
      SecLower P.limit.metric 0 Set.univ ∧
      metricScalarAt (I := I3) P.limit.metric P.limit.basepoint = 1 ∧
      (∀ y : P.limit.M, metricScalarAt (I := I3) P.limit.metric y ≤ 1) := by
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  have hcomplete : SeqMetricComplete (X.atTime 0) := by
    refine ⟨fun i => ?_⟩
    let : CompactSpace (X.term i).M := ‹CompactSpace M›
    exact (RiemannianMetricComplete.of_compact ((X.term i).S.base.metric 0)).complete
  have hconn : ∀ i, ConnectedSpace ((X.atTime 0).obj i).M :=
    fun _ => ‹ConnectedSpace M›
  have hderiv := highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar 0
  obtain ⟨rho, hrho, hinj⟩ := highCurvatureFlowSequence_hasInjRadiusAt_eventually
    hT S hS x t htmem htpos hpos hmax hscalar
  obtain ⟨P, hcanonical, hreference, hconnected, hcompact, hsourceconn, hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      (X.atTime 0) hcomplete hconn
      (by
        intro R hR p
        refine ⟨max 0 (shiLocalUniformBound 3 p 16 4 * 16), le_max_left _ _, ?_⟩
        filter_upwards [hderiv] with i hi
        intro y _hy
        exact (hi p 0 (by simp) y).trans (le_max_right _ _))
      (by
        intro r _hr
        exact ⟨rho, hrho, hinj.mono fun i hi y _hy => hi y⟩)
  have hconv : ∀ K : Set P.limit.M, IsCompact K →
      metricSourceConvergesOn P.maps
        (CanonicalMetricCompactness.canonicalSourceData P.maps) K 2 := by
    intro K hK
    have hd : P.convergence.metrics.domain =
        CanonicalMetricCompactness.canonicalSourceData P.maps := funext hcanonical
    rw [← hd]
    exact P.convergence.metrics.converges K hK 2
  have hcapture : MetricSourceCapture P.maps := by
    apply metricSourceCapture_of_metric_lower_crossModel P.maps P.limit_complete
      (L := 2) (by norm_num)
    intro R _hR
    have hclosed : IsCompact (riemannianClosedBallOf P.limit.metric P.limit.basepoint R) :=
      RiemannianMetricComplete.closedEBall_isCompact
        ⟨MetricComplete.complete P.limit P.limit_complete⟩ P.limit.basepoint R
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
      P.convergence.metrics hreference _ hclosed (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop N] with i hi
    refine ⟨(hN i hi).1, ?_⟩
    intro y hy v
    have h := (abs_le.mp ((hN i hi).2 y hy v)).1
    have hnn := inner_self_nonneg P.limit.metric y v
    change P.limit.metric.inner y v v ≤ 2 ^ 2 *
      ((X.atTime 0).obj (P.subseq i)).metric.inner
        (P.maps.map i y) (mfderiv I3 I3 (P.maps.map i) y v)
        (mfderiv I3 I3 (P.maps.map i) y v)
    nlinarith
  obtain ⟨Phi, hPhi, hpinching⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      (I := I3) hT S hS (by simp [ThreeSpace])
  have hpin : ∀ i (y : ((X.atTime 0).obj i).M),
      curvatureOperatorLowerBoundAt ((X.atTime 0).obj i).metric y
        (metricAlgebraicCurvatureTensorAt ((X.atTime 0).obj i).metric y)
        (rescalePinchingFunction (S.scalar (t i) (x i)) Phi
          (metricScalarAt ((X.atTime 0).obj i).metric y)) := by
    intro i y
    have hzero : 0 ∈ (highCurvatureInterval hT S x t htpos hpos i).carrier :=
      ⟨neg_nonpos.mpr (mul_pos (htpos i) (hpos i)).le, le_rfl⟩
    have hpar := phiAlmostNonnegative_paraSolution (I := I3) S (hpos i) (htmem i) hpinching
    have h : curvatureOperatorLowerBoundAt ((X.term i).S.base.metric 0) y
        ⟨(X.term i).S.base.rm04 0 y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I3) ((X.term i).S.base.metric 0) y⟩
        (rescalePinchingFunction (S.scalar (t i) (x i)) Phi ((X.term i).S.scalar 0 y)) :=
      hpar 0 (highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem i hzero) y
    have hval : ((X.term i).S.base.rm04 (0 : ℝ)) y =
        metricRm04At ((X.term i).S.base.metric 0) y := by
      simp only [SolutionFamily.rm04]
      exact metricRm04_apply _ _
    have hK : (X.term i).S.scalar (0 : ℝ) y =
        metricScalarAt ((X.term i).S.base.metric 0) y := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar]
    simp only [FlowSequence.atTime, PointedFlowData.atTime, SolutionOn.family_metric]
    intro n c v w
    have hh := h n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      hval, hK] at hh ⊢
    exact hh
  have hnonnegative : SecLower P.limit.metric 0 Set.univ := by
    have hn := sectional_nonnegative_of_pointed_admissible_pinching
      P.convergence.metrics hcanonical hPhi (fun i => S.scalar (t i) (x i)) hpos
      (hscalar.comp P.strictMono.tendsto_atTop) hpin
    intro y _ v w
    have hvec : (fun i => ![v, w, w, v] i) = DifferentialGeometry.Geometry.Curvature.vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [DifferentialGeometry.Geometry.Curvature.vec4]
    simpa only [SecLower, zero_mul, metricRm04StandardAt_apply, hvec] using hn y v w
  refine ⟨P, hcanonical, hconnected, hcompact, hsourceconn, hnested,
    hcapture, hnonnegative, ?_, ?_⟩
  · exact metricScalar_base_eq_one_of_canonical_metricConvergence P.maps hconv
      (fun i => highCurvatureFlowSequence_scalar_at_base
        hT S hS x t htmem htpos hpos (P.subseq i))
  · apply metricScalar_le_one_of_canonical_metric_convergence
      (X.atTime 0) P.limit P.maps P.strictMono hconv
    filter_upwards with i y
    exact highCurvatureFlowSequence_scalar_le_one_of_pastMaximum
      hT S hS x t htmem htpos hpos hmax i 0
      ⟨neg_nonpos.mpr (mul_pos (htpos i) (hpos i)).le, le_rfl⟩ y

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
