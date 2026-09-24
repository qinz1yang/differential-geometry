import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ExpandingIntervals
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientConvergenceSubsequence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff _root_.Topology ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]

theorem highCurvatureFlowSequence_isAncientKappaSolution_of_convergesOn
    {T theta kappa : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (hkappa : 0 < kappa) (hbelow : SpatiallyKappaNoncollapsedBelowScale S kappa 1)
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (hconnected : ConnectedSpace P.M) (hcomplete : MetricComplete P)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0) P f)
    (g : ℝ → SmoothRiemannianMetric I3 P.M) (hzero : g 0 = P.metric)
    (hbase : metricScalarAt P.metric P.basepoint = 1)
    (hflow : IsSolutionOn (flowOn ancientTimeInterval g))
    (hconv : ConvergesOn F (flowOn ancientTimeInterval g)) :
    IsAncientKappaSolution kappa (flowOfMetric ancientTimeInterval P g hflow) ∧
      PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P g hflow) 1 ∧
      PointedFlowScalarBounded (flowOfMetric ancientTimeInterval P g hflow) 1 := by
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let L := flowOfMetric ancientTimeInterval P g hflow
  let SL := flowOn ancientTimeInterval g
  obtain ⟨Phi, hPhi, hpinching⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      (I := I3) hT S hS (by simp [ThreeSpace])
  have hpin : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (S.scalar (t i) (x i)) Phi) := by
    intro i s hs y
    exact phiAlmostNonnegative_paraSolution (I := I3) S (hpos i) (htmem i)
      hpinching s (highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem i hs) y
  have hbound : ∀ᶠ i in atTop, ∀ s ∈ (X.interval i).carrier,
      ∀ y : (X.term i).M, (X.term i).S.scalar s y ≤ 1 := by
    filter_upwards with i s hs y
    exact highCurvatureFlowSequence_scalar_le_one_of_pastMaximum
      hT S hS x t htmem htpos hpos hmax i s hs y
  have hsec : ∀ s ∈ ancientTimeInterval.carrier, SecLower (g s) 0 Set.univ := by
    intro s hs
    exact hconv.secLower_zero_of_admissible_pinching hf hPhi
      (fun i => S.scalar (t i) (x i)) hpos hscalar hpin hs
  have hscal : PointedFlowScalarBounded L 1 := by
    intro s hs y
    exact ⟨hconv.scalar_nonneg_of_admissible_pinching hf hPhi
      (fun i => S.scalar (t i) (x i)) hpos hscalar hpin hs y,
      hconv.scalar_le_of_eventually_le hf hbound hs y⟩
  have hrm : ∀ s ∈ ancientTimeInterval.carrier, ∀ y : P.M,
      FlowMetricBall.rmNormSq SL s y ≤ 3 := by
    intro s hs y
    simpa only [one_pow, mul_one] using
      hconv.rmNormSq_le_of_admissible_pinching_of_scalar_le hf hPhi
        (fun i => S.scalar (t i) (x i)) hpos hscalar hpin hbound hs y
  have hcomplete_zero : RiemannianMetricComplete (g 0) := by
    rw [hzero]
    exact ⟨MetricComplete.complete P hcomplete⟩
  have hcomplete_all : ∀ s ∈ ancientTimeInterval.carrier,
      MetricComplete (L.atTime s) := by
    intro s hs
    have hs0 : s ≤ 0 := hs
    have hc : RiemannianMetricComplete (g s) :=
      complete_of_curvature_bound SL hflow ancient_carrier_window ancient_regular_window
        (fun r hr y => hrm r hr.2 y)
        (show s ∈ Icc s 0 from ⟨le_rfl, hs0⟩)
        (show (0 : ℝ) ∈ Icc s 0 from ⟨hs0, le_rfl⟩) hcomplete_zero
    exact hc.complete
  have hnc : PointedFlowNoncollapsedAllScales L kappa := by
    intro time B hB
    obtain ⟨C, hcanonical⟩ := hconv.exists_canonical_metric_convergence time.2
    have hsource : ∀ᶠ i in atTop,
        MetricNoncollapsed ((X.atTime (time : ℝ)).obj i) kappa
          (Ioc 0 (Real.sqrt (S.scalar (t i) (x i)))) := by
      filter_upwards [high_curvature_interval_eventually_contains_closed_window
        hT S x t htpos hpos htheta htlower hscalar (-(time : ℝ))] with i hi
      have htime : (time : ℝ) ∈ (X.interval i).carrier :=
        hi.1 ⟨by simp, time.2⟩
      simpa only [mul_one] using highCurvatureFlowSequence_metricNoncollapsed
        hT S hS x t htmem htpos hpos hbelow i (time : ℝ) htime
    have hmetric : MetricNoncollapsed (L.atTime (time : ℝ)) kappa Set.univ :=
      by
        intro z r _hrscale hr hcurvature
        let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
        have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
        have hvolume := KappaSolutions.tensor_noncollapsed_of_eventually_pointed_canonical_convergence
          C hcanonical (hcomplete_all (time : ℝ) time.2) kappa
          (by
            intro radius hradius
            filter_upwards [hf.tendsto_atTop.eventually hsource,
              ((Real.tendsto_sqrt_atTop.comp hscalar).comp hf.tendsto_atTop).eventually
                (eventually_ge_atTop radius)] with i hi hri y hcurv
            have hv := hi y radius ⟨hradius, hri⟩ hradius hcurv
            simpa only [hdim, ← ENNReal.ofReal_pow hradius.le,
              ← ENNReal.ofReal_mul hkappa.le] using hv)
          z r hr hcurvature
        simp only [hdim, ← ENNReal.ofReal_pow hr.le,
          ← ENNReal.ofReal_mul hkappa.le] at hvolume
        with_unfolding_all exact hvolume
    refine ⟨hkappa, ?_⟩
    have hvolume := hmetric B.center B.radius (mem_univ _) B.radius_pos hB
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim, ← ENNReal.ofReal_pow B.radius_pos.le,
      ← ENNReal.ofReal_mul hkappa.le]
    exact hvolume
  have hop : ∀ s ∈ ancientTimeInterval.carrier,
      PointedFlowNonnegativeCurvatureOperator L s := by
    intro s hs y n c v w
    have ho := (secLower_iff_curvatureOperatorLowerBoundAt (g s)
      (by simp [ThreeSpace]) 0 Set.univ).mp (hsec s hs) y (mem_univ y) n c v w
    simp only [neg_zero, zero_mul, add_zero,
      algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] at ho ⊢
    with_unfolding_all exact ho
  have hb : PointedFlowScalarAtBase L 1 := by
    change metricScalarAt (g 0) P.basepoint = 1
    rw [hzero]
    exact hbase
  exact ⟨isAncientKappaSolution_of_limit L hkappa rfl rfl hconnected
    hcomplete_all hop hscal hnc hb, hb, hscal⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Topology

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

theorem maximal_point_slab_compactness_at_past_maximum
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    MaximalPointSlabCompactnessAtPastMaximum hT S hS o := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) hT S hS hdim (rho := 1) one_pos
  refine ⟨kappa, hkappa, ?_⟩
  intro theta htheta x t htpos htmem hpos htlower hscalar hmax
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  have htlow : ∀ᶠ i in atTop, theta ≤ t i := Filter.Eventually.of_forall htlower
  obtain ⟨P, hcanonical, hconnected, hprecompact, hsourceconn, hnested,
    hcapture, hnonnegative, hbase, _hscalarbound⟩ :=
    exists_highCurvatureFlowSequence_terminal_metric_limit
      hT S hS x t htmem htpos hpos hmax htheta htlow hscalar
  have hzero : ∀ i, 0 ∈ (X.interval i).carrier := by
    intro i
    exact ⟨neg_nonpos.mpr (mul_pos (htpos i) (hpos i)).le, le_rfl⟩
  have hwindow : ∀ A : ℝ, ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (X.interval i).carrier ∧ Ioo (-A) 0 ⊆ (X.interval i).regular :=
    high_curvature_interval_eventually_contains_closed_window
      hT S x t htpos hpos htheta htlow hscalar
  have hcurv := highCurvatureFlowSequence_rmNormSq_eventually_le_of_past_scalar_maximum
    hT S hS x t htmem htpos hpos hmax hscalar
  obtain ⟨bf, hsrc, htgt, ⟨co⟩⟩ :=
    P.exists_halfLineMetricConvergenceData_of_expanding_windows
      hcanonical hconnected hprecompact hsourceconn hnested hcapture hnonnegative
      hzero hwindow hcurv
  have hflow := P.isSolutionOn_of_halfLineMetricConvergenceData
    hcanonical hconnected hprecompact hsourceconn hnested hcapture hnonnegative
    hzero hwindow hcurv co
  have hconv := P.convergesOn_of_halfLineMetricConvergenceData
    hcanonical hconnected hprecompact hsourceconn hnested hcapture hnonnegative
    hzero hwindow hcurv co
  have hgzero := P.terminal_metric_eq_of_halfLineMetricConvergenceData hcanonical hzero co
  let L := flowOfMetric ancientTimeInterval P.limit co.gInf hflow
  let G := subsequenceMaps P.maps co.φ co.strictMono
  have hGconn : ∀ i, IsPreconnected (G.partialDiffeomorph i).source :=
    fun i => (hsourceconn (co.φ i)).2
  obtain ⟨k, hk, ori, hor⟩ :=
    exists_subsequence_preserves_tangentOrientation G hGconn (fun _ => o)
  let H := subsequenceMaps G k hk
  have hconvH : ConvergesOn H (flowOn ancientTimeInterval co.gInf) :=
    convergesOn_subsequence hconv hk
  let phi : ℕ → ℕ := (P.subseq ∘ co.φ) ∘ k
  have hphi : StrictMono phi := (P.strictMono.comp co.strictMono).comp hk
  let F : PointedRiemannianConvergenceMaps (X.atTime 0) (L.atTime 0) phi :=
    X.sliceMaps H co.gInf 0
  obtain ⟨hanc, hb, _hbounded⟩ := highCurvatureFlowSequence_isAncientKappaSolution_of_convergesOn
    hT S hS x t htmem htpos hpos hmax htheta htlow hscalar hkappa hbelow
    P.limit hconnected P.limit_complete phi hphi H co.gInf hgzero hbase hflow hconvH
  refine ⟨L, phi, F, hphi, hanc, hb, ?_, ?_, ?_, ori, ?_⟩
  · intro s hs
    obtain ⟨C, hC⟩ := hconvH.exists_canonical_metric_convergence hs
    refine ⟨X.sliceMaps H co.gInf s, ?_⟩
    intro K hK
    have h := C.converges K hK 2
    rwa [show C.domain = CanonicalMetricCompactness.canonicalSourceData
      (X.sliceMaps H co.gInf s) from funext hC] at h
  · intro K hK A hA order eta heta
    exact (hconvH K hK (-A) 0 (neg_nonpos.mpr hA.le)
      (fun _ hs => hs.2) order eta heta).mono fun _ hi => hi.2
  · intro r hr
    exact (co.strictMono.comp hk).tendsto_atTop.eventually (hcapture r hr)
  · intro i y hy
    exact hor i y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
