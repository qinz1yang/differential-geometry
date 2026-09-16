import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem hasInjRadiusAt_of_expMap_injOn
    (X : PointedRiemannianManifold.{u, 0, 0} (I := I3)) (p : X.M)
    {rho : ℝ} (hpos : 0 < rho)
    (hinj : Set.InjOn (fun v : TangentSpace I3 p =>
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I3) X.metric p v)
      {v | Real.sqrt (X.metric.inner p v v) < rho}) :
    HasInjRadiusAt X p rho := by
  refine ⟨hpos, fun hcomplete => ?_⟩
  let _ : IsManifold I3 1 X.M :=
    IsManifold.of_le (I := I3) (M := X.M) (n := ∞) (by decide)
  let _ : Bundle.RiemannianBundle (fun y : X.M => TangentSpace I3 y) := X.riemBundle
  let _ : (y : X.M) → InnerProductSpace ℝ (TangentSpace I3 y) := X.riemInner
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun y : X.M => TangentSpace I3 y) := X.riemBundle_cont
  let _ : EMetricSpace X.M := X.emetricSpace
  let _ : CompleteSpace X.M := MetricComplete.complete X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I3 y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I3) X.metric y w
  change ENNReal.ofReal rho ≤ intrinsicInjRadius X.metric hEnorm p
  apply le_intrInjRadius
  change Set.InjOn (intrinsicFramedExp X.metric hEnorm p) (Metric.eball 0 (ENNReal.ofReal rho))
  rw [Metric.eball_ofReal]
  intro v hv w hw heq
  apply (normalFrame X.metric p).injective
  apply hinj
  · simp only [Set.mem_ofPred_eq, normalFrame_sqrt]
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  · simp only [Set.mem_ofPred_eq, normalFrame_sqrt]
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  · simpa only [intrinsicFrame_apply,
      ← Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic (I := I3) X.metric hEnorm p]
      using heq

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I3 M)]

theorem highCurvatureFlowSequence_hasInjRadiusAt_eventually_on_carrier
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ i in atTop,
      ∀ s ∈ (highCurvatureInterval hT S x t htpos hpos i).carrier,
      ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).M,
        HasInjRadiusAt
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).atTime s)
          y rho := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) hT S hS hdim (rho := 1) one_pos
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hkappa
  refine ⟨iota * (1 / 4), mul_pos hiota (by norm_num), ?_⟩
  have hrm := highCurvatureFlowSequence_rmNormSq_eventually_le_of_past_scalar_maximum
    hT S hS x t htmem htpos hpos hmax hscalar
  filter_upwards [hrm, hscalar.eventually_ge_atTop 1] with i hi hQi s hs y
  let F := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i
  let P := parabolicSolution (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) (htmem i)
  have hsP : s ∈ (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
      (t i) (S.scalar (t i) (x i)) (htmem i)).carrier :=
    highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem i hs
  let B : FlowMetricBall P ⟨s, hsP⟩ := ⟨y, 1 / 4, by norm_num⟩
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    have h := hi s hs z
    change (1 / 4 : ℝ) ^ 4 * F.rmNormSq s z ≤ 1
    norm_num
    linarith
  have hnoncollapse := parabolic_spatial_noncollapse (I := I3) S (t i)
    (S.scalar (t i) (x i)) (hpos i) (htmem i) kappa 1 hbelow
  have hscale : B.radius ≤ Real.sqrt (S.scalar (t i) (x i)) * 1 := by
    have hsqrt : 1 ≤ Real.sqrt (S.scalar (t i) (x i)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQi
    change (1 / 4 : ℝ) ≤ _
    linarith
  have hvol := (hnoncollapse.2 ⟨s, hsP⟩ B hscale hcontrol).2
  have hcurv : ∀ z ∈ riemannianBallOf (I := I3) (F.S.base.metric s) y (1 / 4),
      (1 / 4 : ℝ) ^ 4 * Tensor0SBundle.normSq0S (I := I3) (F.S.base.metric s) z 4
        (metricRm04At (F.S.base.metric s) z) ≤ 1 := by
    intro z hz
    exact hcontrol z hz
  have hvol' : ENNReal.ofReal (kappa * (1 / 4 : ℝ) ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 F.M (F.S.base.metric s)
        (riemannianBallOf (I := I3) (F.S.base.metric s) y (1 / 4)) := by
    rw [ENNReal.ofReal_mul hkappa.le,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    convert hvol using 1
    rfl
  let : CompactSpace F.M := ‹CompactSpace M›
  have hcomplete : RiemannianMetricComplete (F.S.base.metric s) :=
    RiemannianMetricComplete.of_compact _
  exact hasInjRadiusAt_of_expMap_injOn (F.atTime s) y (mul_pos hiota (by norm_num))
    (hinj F.M (F.S.base.metric s) hcomplete y (1 / 4) (by norm_num) hcurv hvol')


theorem highCurvatureFlowSequence_hasInjRadiusAt_eventually
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ i in atTop,
      ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).M,
        HasInjRadiusAt
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).atTime 0)
          y rho := by
  obtain ⟨rho, hrho, hbound⟩ :=
    highCurvatureFlowSequence_hasInjRadiusAt_eventually_on_carrier
      hT S hS x t htmem htpos hpos hmax hscalar
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hbound] with i hi
  exact hi 0 ⟨neg_nonpos.mpr (mul_pos (htpos i) (hpos i)).le, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
