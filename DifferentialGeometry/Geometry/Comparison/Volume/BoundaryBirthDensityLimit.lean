import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthMetricFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleGramLimit
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram

/-!
The same original true-interior angular family has density divided by t squared tending to one.
The boundary point stays outside the true interior; actual positive birth transports the limit.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthDensity_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_density_limit (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthDensity_infty_ne_zero (M := M)
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
          (∀ q ∈ V, (ρ q : M) = (extChartAt I p).symm
            (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            ∀ w : E,
              IsJacobiAt k (fun t => ρ (q.1, t))
                (fun t => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 t w) q.2 ∧
              ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                (fun t => (⟨ρ (q.1, t), boundaryJointJacobiLinear
                  (I := 𝓘(ℝ, E)) ρ q.1 t w⟩ : TangentBundle 𝓘(ℝ, E) U)) q.2) ∧
          (∀ q ∈ V, ∀ w z : E,
            k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
              (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
              G.inner (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)
                (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 w)
                (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 z)) ∧
          (∀ q ∈ V, ∀ e : Fin 2 → E,
            curveDensity k (fun t => ρ (q.1, t))
              (fun i t => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 t (e i)) q.2 =
              curveDensity G (boundaryPoleFlowFamily G (extChartAt I p p) q.1)
                (fun i t => boundaryPoleJacobiLinear G (extChartAt I p p) q.1 t (e i)) q.2) ∧
          (∀ v w : E, boundaryPoleJacobiLinear G (extChartAt I p p) v 0 w = 0 ∧
            covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) v)
              (fun t => boundaryPoleJacobiLinear G (extChartAt I p p) v t w) 0 = w) ∧
          (∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, (v, t) ∈ V ) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∀ e : Fin 2 → E,
              (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
              Tendsto (fun t : ℝ => curveDensity k (fun s => ρ (v, s))
                (fun i s => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v s (e i)) t / t ^ 2)
                (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthDensity_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hgram, hdensity, hinit, hbirth⟩ :=
    exists_boundary_common_metric_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hgram, hdensity, hinit, hbirth, ?_⟩
  intro v hin e hON
  obtain ⟨ε, hε, hV⟩ := hbirth v hin
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 ε := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with t ht htε
    exact ⟨ht, htε⟩
  have heq : (fun t : ℝ => curveDensity k (fun s => ρ (v, s))
      (fun i s => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v s (e i)) t / t ^ 2) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G (extChartAt I p p) v)
        (fun i s => boundaryPoleJacobiLinear G (extChartAt I p p) v s (e i)) t / t ^ 2) := by
    filter_upwards [hnear] with t ht
    exact congrArg (fun a : ℝ => a / t ^ 2) (hdensity (v, t) (hV t ht) e)
  exact (boundaryPoleJacobiLinear_density_div_sq_tendsto G (extChartAt I p p)
    v e hON).congr' heq.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
