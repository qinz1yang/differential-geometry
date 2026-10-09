import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleInitialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryChartDistance
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPositiveRayDistance
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryRayDomain
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
Actual inward pole rays are initially minimizing for the original corner metric.
The complete chart metric supplies the local radial lower bound; the upper bound comes from
length in the genuine interior metric and the original pole limit.
-/

set_option autoImplicit false

noncomputable section

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open Bundle Filter Manifold MeasureTheory Set TopologicalSpace
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientComplete : CompleteSpace E] [ambientDimension : NeZero (Module.finrank ℝ E)]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

omit ambientComplete in
theorem boundaryCompleteFlow_radial_small
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (hcomplete : RiemannianMetricComplete G)
    (y v : E) (hunit : G.inner y v v = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ {t : ℝ}, 0 ≤ t → t < r →
      riemannianEDistOf G y (boundaryPoleFlowFamily G y v t) = ENNReal.ofReal t := by
  letI : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : T2Space E := inferInstance
  letI : SigmaCompactSpace E := inferInstance
  letI : TopologicalSpace.MetrizableSpace E :=
    Manifold.metrizableSpace (I := 𝓘(ℝ, E)) (M := E)
  letI : T3Space E := inferInstance
  letI : PseudoEMetricSpace E :=
    (DifferentialGeometry.inducedEMetricSpace (I := 𝓘(ℝ, E)) G).toPseudoEMetricSpace
  letI : UniformSpace E := ‹PseudoEMetricSpace E›.toUniformSpace
  have hcompleteE : CompleteSpace E := hcomplete.complete
  letI : CompleteSpace E := hcompleteE
  letI : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨by intro x z; rfl⟩
  let hEnorm : IsMetricNorm G := isMetricNorm_of_riemannianBundle (I := 𝓘(ℝ, E)) G
  obtain ⟨r, hr, hradial⟩ := radial_riemannianEDist_eq_of_small
    (I := 𝓘(ℝ, E)) G hEnorm y
  refine ⟨r, hr, ?_⟩
  intro t ht htr
  have hflow : boundaryPoleFlowFamily G y v t =
      expMapIntrinsic G hEnorm y (t • (v : TangentSpace 𝓘(ℝ, E) y)) := by
    unfold boundaryPoleFlowFamily
    let vT : TangentSpace 𝓘(ℝ, E) y := v
    calc
      (G.geodesicFlow (⟨y, vT⟩ : TangentBundle 𝓘(ℝ, E) E) t).proj =
          intrinsicGeodesic G hEnorm y vT t :=
        Bundle.ContMDiffRiemannianMetric.proj_geodesicFlow_eq_intrinsicGeodesic
          G hEnorm y vT t
      _ = intrinsicGeodesic G hEnorm y (t • vT) 1 := by
        rw [← intrinsicGeodesic_smul (I := 𝓘(ℝ, E)) G hEnorm y vT t]
      _ = expMapIntrinsic G hEnorm y (t • vT) := rfl
  calc
    riemannianEDistOf G y (boundaryPoleFlowFamily G y v t) =
        riemannianEDist (𝓘(ℝ, E)) y (boundaryPoleFlowFamily G y v t) :=
      riemannianEDistOf_eq_riemannianEDist (I := 𝓘(ℝ, E)) G hEnorm y _
    _ = riemannianEDist (𝓘(ℝ, E)) y
        (expMapIntrinsic G hEnorm y (t • (v : TangentSpace 𝓘(ℝ, E) y))) :=
      congrArg (riemannianEDist (𝓘(ℝ, E)) y) hflow
    _ = ENNReal.ofReal t := hradial hunit ht htr

omit ambientComplete ambientDimension modelBoundary in
theorem boundaryOriginal_chartRadial_lowerBound
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hpO : extChartAt I p p ∈ O)
    (hmetric : ∀ y ∈ (O : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart g p y v w)
    (γ : ℝ → M) (F : ℝ → E)
    (rBirth : ℝ) (hrBirth : 0 < rBirth)
    (hcoord : ∀ t, 0 < t → t < rBirth → extChartAt I p (γ t) = F t)
    (hupper : ∀ t, 0 < t → t < rBirth →
      riemannianEDistOf g p (γ t) ≤ ENNReal.ofReal t)
    (rRadial : ℝ) (hrRadial : 0 < rRadial)
    (hradial : ∀ t, 0 ≤ t → t < rRadial →
      riemannianEDistOf G (extChartAt I p p) (F t) = ENNReal.ofReal t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rBirth ∧ ∀ t, 0 < t → t < r →
      riemannianEDistOf g p (γ t) = ENNReal.ofReal t := by
  obtain ⟨rChart, hrChart, hchart⟩ := exists_boundaryChart_edist_le g G p O hpO hmetric
  let r := min rChart rRadial
  let r' := min rBirth r
  have hr : 0 < r' := lt_min hrBirth (lt_min hrChart hrRadial)
  refine ⟨r', hr, min_le_left _ _, ?_⟩
  intro t ht htR
  have htBirth : t < rBirth := lt_of_lt_of_le htR (min_le_left _ _)
  have htRadialOuter : t < r := lt_of_lt_of_le htR (min_le_right _ _)
  have htChart : t < rChart := lt_of_lt_of_le htRadialOuter (min_le_left _ _)
  have htRadial : t < rRadial := lt_of_lt_of_le htRadialOuter (min_le_right _ _)
  have hball : γ t ∈ riemannianClosedBallOf g p rChart := by
    change riemannianEDistOf g p (γ t) ≤ ENNReal.ofReal rChart
    exact (hupper t ht htBirth).trans (ENNReal.ofReal_le_ofReal (le_of_lt htChart))
  have hpball : p ∈ riemannianClosedBallOf g p rChart := by
    change riemannianEDistOf g p p ≤ ENNReal.ofReal rChart
    rw [riemannianEDistOf_self]
    exact (ENNReal.ofReal_pos.mpr hrChart).le
  have hchartLower := hchart p hpball (γ t) hball
  rw [hcoord t ht htBirth] at hchartLower
  have hGdist := hradial t ht.le htRadial
  exact le_antisymm (hupper t ht htBirth) (hGdist.symm.le.trans hchartLower)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
