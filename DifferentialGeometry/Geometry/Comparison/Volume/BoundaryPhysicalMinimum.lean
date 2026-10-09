import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryUnitPhysicalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhysicalDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryAlivePrefixMinimum
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleInitialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhasePhysicalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonBirthPhase
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPoleContinuity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseRadialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseBirthDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthGramDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthAngularContinuation
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleGramLimit
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthTangentMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
Actual original unit pole rays bound all existing positive physical prefix distances.
An original terminal distance minimum yields every native positive subsegment minimum.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]


private theorem physicalMinimum_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_physical_minimum (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalMinimum_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            G.inner (extChartAt I p p) v v = 1 →
            ∃ δ : ℝ, 0 < δ ∧ ∃ a ∈ Ioo 0 δ,
              ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E,
                v ∈ W ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ t ∈ Ioo 0 δ, (v, t) ∈ V ∧ (σ v, t - a) ∈ k.geodesicFlowDomain) ∧
                Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
                  (𝓝[>] (0 : ℝ)) (𝓝 p) ∧
                (∀ e : Fin 2 → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  Tendsto (fun t : ℝ => curveDensity k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) ∧
                ∀ T : ℝ, (σ v, T - a) ∈ k.geodesicFlowDomain →
                  0 < T ∧
                  (∀ t ∈ Ioc 0 T, (σ v, t - a) ∈ k.geodesicFlowDomain) ∧
                  (∀ t ∈ Ioc 0 T, DifferentialGeometry.riemannianEDistOf g p
                    ((boundaryPhasePoint k σ v (t - a) : U) : M) ≤ ENNReal.ofReal t) ∧
                  (DifferentialGeometry.riemannianEDistOf g p
                      ((boundaryPhasePoint k σ v (T - a) : U) : M) = ENNReal.ofReal T →
                    (∀ t ∈ Ioc 0 T, DifferentialGeometry.riemannianEDistOf g p
                      ((boundaryPhasePoint k σ v (t - a) : U) : M) = ENNReal.ofReal t) ∧
                    (∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s ≤ t →
                      DifferentialGeometry.riemannianEDistOf g
                        ((boundaryPhasePoint k σ v (s - a) : U) : M)
                        ((boundaryPhasePoint k σ v (t - a) : U) : M) =
                          ENNReal.ofReal (t - s)) ∧
                    ∀ s ∈ Ioc 0 T, ∀ t ∈ Ioc 0 T, s ≤ t →
                      ∀ η : ℝ → U, ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc s t) →
                        η s = boundaryPhasePoint k σ v (s - a) →
                        η t = boundaryPhasePoint k σ v (t - a) →
                        arcLength k (fun r => boundaryPhasePoint k σ v (r - a)) s t ≤
                          arcLength k η s t) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    physicalMinimum_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  have hp : I.IsBoundaryPoint p := by
    change extChartAt I p p ∈ frontier (range I)
    rw [hb, ← range_modelBoundaryParam I]
    exact mem_range_self b
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hlaunch⟩ :=
    exists_boundary_unit_physical_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin hunit
  obtain ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hlimit, hframe⟩ :=
    hlaunch v hin hunit
  refine ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hlimit, ?_⟩
  intro T hT
  have hdomain := boundaryPhase_positive_physical_domain g p hp
    σ W hσ v hv δ a hδ ha (fun t ht => (hbirth t ht).2) hPole
  have hpositive : 0 < T := hdomain.1 T hT
  have hwhole (t : ℝ) (ht : t ∈ Ioc 0 T) :
      (σ v, t - a) ∈ k.geodesicFlowDomain := hdomain.2 t T ht.1 ht.2 hT
  have hsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1
      (fun r => boundaryPhasePoint k σ v (r - a)) (Ioc 0 T) := by
    intro t ht
    exact ((hframe t (hwhole t ht)).1.of_le (by simp)).contMDiffWithinAt
  have hspeed (t : ℝ) (ht : t ∈ Ioo 0 T) :
      k.inner (boundaryPhasePoint k σ v (t - a))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun r => boundaryPhasePoint k σ v (r - a)) t 1)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun r => boundaryPhasePoint k σ v (r - a)) t 1) = 1 :=
    (hframe t (hwhole t ⟨ht.1, ht.2.le⟩)).2.2.1
  have hupper := (boundaryInterior_positive_ray_distance g p
    (fun r => boundaryPhasePoint k σ v (r - a)) T hsmooth hspeed hPole).2
  refine ⟨hpositive, hwhole, hupper, ?_⟩
  intro hminimum
  exact boundaryInterior_alive_prefix_minimum g p
    (fun r => boundaryPhasePoint k σ v (r - a)) T hpositive hsmooth hspeed hPole hminimum

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
