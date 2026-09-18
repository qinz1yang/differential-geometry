import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
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
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem highCurvatureFlowSequence_noncollapsed_of_pointed_convergence
    {T theta kappa : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (hkappa : 0 < kappa) (hbelow : SpatiallyKappaNoncollapsedBelowScale S kappa 1)
    (s : ℝ) (hs : s ≤ 0) (f : ℕ → ℕ) (hf : Tendsto f atTop atTop)
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (Psi : PointedRiemannianConvergenceMaps
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime s) P f)
    (C : MetricConvergenceData Psi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i)
    (hcomplete : MetricComplete P) :
    MetricNoncollapsed P kappa univ := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscales : Tendsto (fun i => Real.sqrt (S.scalar (t (f i)) (x (f i))))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (hscalar.comp hf)
  have htime : ∀ᶠ i in atTop, s ∈ (highCurvatureInterval hT S x t htpos hpos (f i)).carrier := by
    have hw := high_curvature_interval_eventually_contains_closed_window
      hT S x t htpos hpos htheta htlower hscalar (-s)
    filter_upwards [hf.eventually hw] with i hi
    exact hi.1 ⟨by simp, hs⟩
  have hn := KappaSolutions.tensor_noncollapsed_of_eventually_pointed_canonical_convergence
    C hcanonical hcomplete kappa (by
      intro r hr
      filter_upwards [htime, hscales.eventually_gt_atTop r] with i hi hir
      intro p hcurv
      let B : FlowMetricBall
          (parabolicSolution S (t (f i)) (S.scalar (t (f i)) (x (f i))) (hpos (f i)) (htmem (f i)))
          ⟨s, highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem (f i) hi⟩ := ⟨p, r, hr⟩
      have hn := parabolic_spatial_noncollapse S (t (f i))
        (S.scalar (t (f i)) (x (f i))) (hpos (f i)) (htmem (f i)) kappa 1 hbelow
      exact (hn.2 _ B (by simpa only [mul_one] using hir.le) hcurv).2)
  intro y r _ hr hcurv
  simpa only [hdim, ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hr.le] using
    hn y r hr hcurv

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
