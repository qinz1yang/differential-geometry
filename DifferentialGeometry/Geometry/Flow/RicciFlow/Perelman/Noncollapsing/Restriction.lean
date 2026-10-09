import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem SpatiallyKappaNoncollapsedBelowScale.restrictOpen
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : ℝ}
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) :
    letI : SigmaCompactSpace U := hU.sigmaCompactSpace
    SpatiallyKappaNoncollapsedBelowScale (solutionOnRestrictOpen S U) kappa rho := by
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  refine ⟨h.1, ?_⟩
  intro t B hr hRm
  let B' : FlowMetricBall S t := ⟨B.center.val, B.radius, B.radius_pos⟩
  have hset : B'.set = (Subtype.val : U → M) '' B.set :=
    riemannianBallOf_eq_image_restrictOpen_of_isClosed (S.base.metric t) U hU B.center B.radius
  have hpre : B.set = (Subtype.val : U → M) ⁻¹' B'.set := by
    rw [hset, preimage_image_eq _ Subtype.val_injective]
  have hsubset : B'.set ⊆ U := by
    rw [hset]
    rintro y ⟨x, _, rfl⟩
    exact x.property
  have hRm' : B'.IsSpatiallyRmControlled := by
    intro y hy
    rw [hset] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hsec : metricRm04 (I := I) (M := U) ((S.base.metric t).restrictOpen U) x =
        metricRm04 (I := I) (M := M) (S.base.metric t) x.val := by
      ext slots
      have heq := metricRm04_restrictOpen_eval (I := I) (S.base.metric t) U x slots
      simp only [mfderiv_subtype_val_apply] at heq
      exact heq
    have hnorm : FlowMetricBall.rmNormSq (solutionOnRestrictOpen S U) t x =
        FlowMetricBall.rmNormSq S t x.val := by
      change normSq0S ((S.base.metric t).restrictOpen U) x 4
          (metricRm04 ((S.base.metric t).restrictOpen U) x) =
        normSq0S (S.base.metric t) x.val 4 (metricRm04 (S.base.metric t) x.val)
      rw [normSq0S_restrictOpen_apply, hsec]
    simpa only [hnorm] using hRm x hx
  have hvol : B.volume = B'.volume := by
    have hmeas : MeasurableSet B'.set := by
      have hd : Continuous (fun y : M ↦
          riemannianEDistOf (S.base.metric t) B'.center y) := by
        simpa only [riemannianEDistOf] using
          continuous_riemannianEDist (S.base.metric t) B'.center
      exact (isOpen_lt hd continuous_const).measurableSet
    change riemannianVolumeMeasure (I := I) (M := U) ((S.base.metric t).restrictOpen U)
        B.set = riemannianVolumeMeasure (I := I) (M := M) (S.base.metric t) B'.set
    rw [hpre]
    exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      (S.base.metric t) U hmeas hsubset
  have hnc := h.2 t B' hr hRm'
  exact ⟨hnc.1, hvol ▸ hnc.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
