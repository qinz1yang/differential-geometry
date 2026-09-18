import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure

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

private theorem exists_highCurvatureFlowSequence_metric_compact_limit
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
      ∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1) := by
  let X := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0
  have hcomplete : SeqMetricComplete X := by
    refine ⟨fun i => ?_⟩
    let _ : CompactSpace (X.obj i).M := ‹CompactSpace M›
    exact (RiemannianMetricComplete.of_compact (X.obj i).metric).complete
  have hspatial := highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar 0
  have hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop, HasLocalCurvDerivBound (X.obj i) (X.obj i).basepoint R p C := by
    intro R hR p
    refine ⟨shiLocalUniformBound 3 p 16 4 * 16,
      mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) (by norm_num), ?_⟩
    filter_upwards [hspatial] with i hi
    intro y hy
    exact hi p 0 ⟨by norm_num, le_rfl⟩ y
  obtain ⟨rho, hrho, hinj⟩ := highCurvatureFlowSequence_hasInjRadiusAt_eventually
    hT S hS x t htmem htpos hpos hmax hscalar
  obtain ⟨P, hcanonical, _, hgeometry⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      X hcomplete (fun _ => ‹ConnectedSpace M›) hjets
      (fun _ _ => ⟨rho, hrho, hinj.mono fun _ hi y _ => hi y⟩)
  exact ⟨P, hcanonical, hgeometry⟩


theorem exists_highCurvatureFlowSequence_noncollapsed_metric_limit
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ)
        (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
        (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
        (∀ i s, s ∈ Icc 0 (t i) → ∀ y : M, S.scalar s y ≤ S.scalar (t i) (x i)) →
        (∀ᶠ i in atTop, theta ≤ t i) →
        Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop →
        ∃ P : MetricCompactLimit
            ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
          ConnectedSpace P.limit.M ∧
          (∀ n, IsCompact (closure (P.maps.source n))) ∧
          (∀ n, IsConnected (P.maps.source n)) ∧
          (∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) ∧
          metricScalarAt P.limit.metric P.limit.basepoint = 1 ∧
          (∀ y : P.limit.M, metricScalarAt P.limit.metric y ∈ Icc (0 : ℝ) 1) ∧
          (∀ (y : P.limit.M) (v w : TangentSpace I3 y),
            0 ≤ metricRm04StandardAt P.limit.metric y v w w v) ∧
          MetricNoncollapsed P.limit kappa univ := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) hT S hS hdim (rho := 1) one_pos
  obtain ⟨Phi, hPhi, hpinching⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen hT S hS hdim
  refine ⟨kappa, hkappa, ?_⟩
  intro theta htheta x t htmem htpos hpos hmax htlower hscalar
  obtain ⟨P, hcanonical, hconnected, hcompact, hsourceconn, hnested⟩ :=
    exists_highCurvatureFlowSequence_metric_compact_limit
      hT S hS x t htmem htpos hpos hmax htheta htlower hscalar
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  have hconv : ∀ K : Set P.limit.M, IsCompact K → metricSourceConvergesOn
      P.maps (CanonicalMetricCompactness.canonicalSourceData P.maps) K 2 := by
    intro K hK
    have hc := P.convergence.metrics.converges K hK 2
    rwa [show P.convergence.metrics.domain =
      CanonicalMetricCompactness.canonicalSourceData P.maps from funext hcanonical] at hc
  have hbase : metricScalarAt P.limit.metric P.limit.basepoint = 1 :=
    metricScalar_base_eq_one_of_canonical_metricConvergence P.maps hconv
      (fun i => highCurvatureFlowSequence_scalar_at_base
        hT S hS x t htmem htpos hpos (P.subseq i))
  have hupper : ∀ y : P.limit.M, metricScalarAt P.limit.metric y ≤ 1 := by
    apply metricScalar_le_one_of_canonical_metric_convergence
      (X.atTime 0) P.limit P.maps P.strictMono hconv
    exact Eventually.of_forall fun i =>
      highCurvatureFlowSequence_scalar_le_one_of_pastMaximum
        hT S hS x t htmem htpos hpos hmax i 0
        ⟨neg_nonpos.mpr (mul_pos (htpos i) (hpos i)).le, le_rfl⟩
  have hsec : ∀ (y : P.limit.M) (v w : TangentSpace I3 y),
      0 ≤ metricRm04StandardAt P.limit.metric y v w w v := by
    apply sectional_nonnegative_of_pointed_admissible_pinching
      P.convergence.metrics hcanonical hPhi (fun i => S.scalar (t i) (x i)) hpos
      (hscalar.comp P.strictMono.tendsto_atTop)
    intro i y
    have hp := phiAlmostNonnegative_paraSolution S (hpos i) (htmem i) hpinching
      0 (by simpa only [Set.mem_ofPred_eq, parabolicTime, zero_div, add_zero] using htmem i) y
    exact hp
  have hlower (y : P.limit.M) : 0 ≤ metricScalarAt P.limit.metric y := by
    classical
    obtain ⟨b, hb⟩ := Tensor0SBundle.exists_orthonormal_basis P.limit.metric y
    rw [KappaSolutions.metricScalarAt_eq_sum_sum_rm04_of_orthonormal P.limit.metric b hb]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hsec y (b j) (b i)
  refine ⟨P, hcanonical, hconnected, hcompact, hsourceconn, hnested, hbase,
    fun y => ⟨hlower y, hupper y⟩, hsec, ?_⟩
  have hscales : Tendsto (fun i => Real.sqrt (S.scalar (t (P.subseq i)) (x (P.subseq i))))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (hscalar.comp P.strictMono.tendsto_atTop)
  have hn := KappaSolutions.tensor_noncollapsed_of_pointed_canonical_convergence_of_expanding_scales
    P.convergence.metrics hcanonical P.limit_complete kappa
    (fun i => Real.sqrt (S.scalar (t i) (x i))) hscales (by
      intro i p r hr hrscale hcurv
      let B : FlowMetricBall
          (parabolicSolution S (t i) (S.scalar (t i) (x i)) (hpos i) (htmem i))
          ⟨0, by simpa only [parabolicInterval, RealTimeInterval.closedOpen, Set.mem_ofPred_eq, parabolicTime, zero_div, add_zero]
            using htmem i⟩ := ⟨p, r, hr⟩
      have hn := parabolic_spatial_noncollapse S (t i)
        (S.scalar (t i) (x i)) (hpos i) (htmem i) kappa 1 hbelow
      have hvol := (hn.2 _ B (by simpa only [mul_one] using hrscale.le) hcurv).2
      exact hvol)
  intro y r _ hr hcurv
  simpa only [hdim, ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hr.le] using
    hn y r hr hcurv

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
