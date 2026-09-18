import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureLocalBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
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

theorem highCurvatureFlowSequence_hasInjRadiusAt_eventually_on_closed_ball
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S.base.metric 0)
        (x i) R,
        HasInjRadiusAt
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).atTime 0)
          y rho := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) hT S hS hdim (rho := 1) one_pos
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hkappa
  obtain ⟨C, hC, hbounds⟩ := exists_high_curvature_rescaled_curvature_bounds.{u}
  obtain ⟨Q0, hQ0, hbound⟩ := hbounds M T hT S hS o (R + 1) 0 (by linarith) le_rfl
  let r : ℝ := (C (R + 1) + 1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by linarith [hC (R + 1)])
  have hr1 : r ≤ 1 := (inv_le_one₀ (by linarith [hC (R + 1)])).mpr (by linarith [hC (R + 1)])
  have hrc : r * C (R + 1) ≤ 1 := by
    calc
      _ ≤ r * (C (R + 1) + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.le
      _ = 1 := inv_mul_cancel₀ (by linarith [hC (R + 1)])
  have hscaled : r ^ 4 * C (R + 1) ≤ 1 := by
    calc
      _ = r ^ 3 * (r * C (R + 1)) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ hr.le hr1 3) hrc
        (mul_nonneg hr.le (hC (R + 1)).le) (by norm_num)
      _ = 1 := by norm_num
  refine ⟨iota * r, mul_pos hiota hr, ?_⟩
  filter_upwards [hscalar.eventually_ge_atTop Q0, hscalar.eventually_ge_atTop 1] with i hQi hQone
  intro y hy
  let F := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i
  let P := parabolicSolution S (t i) (S.scalar (t i) (x i)) (hpos i) (htmem i)
  have hzero : (0 : ℝ) ∈ (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
      (t i) (S.scalar (t i) (x i)) (htmem i)).carrier := by
    simpa only [parabolicInterval, RealTimeInterval.closedOpen, Set.mem_ofPred_eq,
      parabolicTime_zero] using htmem i
  let B : FlowMetricBall P ⟨0, hzero⟩ := ⟨y, r, hr⟩
  have hcurv : ∀ z ∈ riemannianBallOf (F.S.base.metric 0) y r,
      r ^ 4 * Tensor0SBundle.normSq0S (F.S.base.metric 0) z 4
        (metricRm04At (F.S.base.metric 0) z) ≤ 1 := by
    intro z hz
    have hz' : z ∈ riemannianClosedBallOf (F.S.base.metric 0) (x i) (R + 1) := by
      calc
        _ ≤ riemannianEDistOf (F.S.base.metric 0) (x i) y +
            riemannianEDistOf (F.S.base.metric 0) y z := riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal R + ENNReal.ofReal 1 :=
          add_le_add hy (hz.le.trans (ENNReal.ofReal_le_ofReal hr1))
        _ = ENNReal.ofReal (R + 1) := (ENNReal.ofReal_add hR zero_le_one).symm
    have h := (hbound (x i) (t i) (htmem i) hQi).2
      0 (by norm_num) 0 (by norm_num) z hz'
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg hr.le 4)).trans hscaled
  have hcontrol : B.IsSpatiallyRmControlled := hcurv
  have hnoncollapse := parabolic_spatial_noncollapse S (t i)
    (S.scalar (t i) (x i)) (hpos i) (htmem i) kappa 1 hbelow
  have hscale : B.radius ≤ Real.sqrt (S.scalar (t i) (x i)) * 1 := by
    have hsqrt : 1 ≤ Real.sqrt (S.scalar (t i) (x i)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQone
    exact hr1.trans (by simpa only [mul_one] using hsqrt)
  have hvol := (hnoncollapse.2 ⟨0, hzero⟩ B hscale hcontrol).2
  have hvol' : ENNReal.ofReal (kappa * r ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 F.M (F.S.base.metric 0)
        (riemannianBallOf (F.S.base.metric 0) y r) := by
    rw [ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hr.le]
    exact hvol
  let : CompactSpace F.M := ‹CompactSpace M›
  exact hasInjRadiusAt_of_expMap_injOn (F.atTime 0) y (mul_pos hiota hr)
    (hinj F.M (F.S.base.metric 0) (RiemannianMetricComplete.of_compact _) y r hr hcurv hvol')

theorem exists_highCurvatureFlowSequence_metric_limit
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
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
  obtain ⟨C, hC, hbounds⟩ := exists_high_curvature_rescaled_curvature_derivative_bounds.{u}
  have hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop, HasLocalCurvDerivBound (X.obj i) (X.obj i).basepoint R p C := by
    intro R hR p
    obtain ⟨Q0, hQ0, hbound⟩ := hbounds M T hT S hS o R 0 hR le_rfl
    refine ⟨C R p, (hC R p).le, ?_⟩
    filter_upwards [hscalar.eventually_ge_atTop Q0] with i hi
    intro y hy
    exact (hbound (x i) (t i) (htmem i) hi).2 0 (by norm_num) 0 (by norm_num) y hy p
  obtain ⟨P, hcanonical, _, hgeometry⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      X hcomplete (fun _ => ‹ConnectedSpace M›) hjets (fun r hr =>
        highCurvatureFlowSequence_hasInjRadiusAt_eventually_on_closed_ball
          hT S hS o x t htmem htpos hpos hscalar hr.le)
  exact ⟨P, hcanonical, hgeometry⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
