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
Actual original unit inward directions produce one physical native geodesic and angular frame.
Real phase velocity and covariant transport derive all unit, perpendicular and Wronskian data.
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
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]


private theorem unitPhysical_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_unit_physical_frame (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      unitPhysical_infty_ne_zero (M := M)
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
                ∀ t : ℝ, (σ v, t - a) ∈ k.geodesicFlowDomain →
                  ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
                    (fun r => boundaryPhasePoint k σ v (r - a)) t ∧
                  HasGeodesicEquationAt k (fun r => boundaryPhasePoint k σ v (r - a)) t ∧
                  k.inner (boundaryPhasePoint k σ v (t - a))
                    (curveVelocity (I := 𝓘(ℝ, E))
                      (fun r => boundaryPhasePoint k σ v (r - a)) t)
                    (curveVelocity (I := 𝓘(ℝ, E))
                      (fun r => boundaryPhasePoint k σ v (r - a)) t) = 1 ∧
                  (∀ w : E, G.inner (extChartAt I p p) w v = 0 →
                    k.inner (boundaryPhasePoint k σ v (t - a))
                      (boundaryPhaseJacobiLinear k σ v (t - a) w)
                      (curveVelocity (I := 𝓘(ℝ, E))
                        (fun r => boundaryPhasePoint k σ v (r - a)) t) = 0 ∧
                    k.inner (boundaryPhasePoint k σ v (t - a))
                      (covDerivAlong k (fun r => boundaryPhasePoint k σ v (r - a))
                        (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w) t)
                      (curveVelocity (I := 𝓘(ℝ, E))
                        (fun r => boundaryPhasePoint k σ v (r - a)) t) = 0) ∧
                  (∀ w z : E, jacobiWronskian k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w)
                    (fun r => boundaryPhaseJacobiLinear k σ v (r - a) z) t = 0) ∧
                  ∀ w : E, IsJacobiAt k (fun r => boundaryPhasePoint k σ v (r - a))
                      (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w) t ∧
                    ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                      (fun r => (⟨boundaryPhasePoint k σ v (r - a),
                        boundaryPhaseJacobiLinear k σ v (r - a) w⟩ :
                        TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    unitPhysical_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hlaunch⟩ :=
    exists_boundary_common_pole_initial_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin hunit
  obtain ⟨δ, hδ, a, ha, σ, W, _ε, hv, _hε, hσ, _hseed, _hmatch,
    hentry, hPole, _hlift, hbirth, hlimit, hframe⟩ := hlaunch v hin
  refine ⟨δ, hδ, a, ha, σ, W, hv, hσ,
    (fun t ht => ⟨hentry t ht, (hbirth t ht).1⟩), hPole, hlimit, ?_⟩
  intro t ht
  have hphase := hframe v hv (t - a) ht
  obtain ⟨hsmooth, hgeo, hvel⟩ := boundaryPhase_physical_geodesic k W σ hσ v hv a t ht
  refine ⟨hsmooth, hgeo, ?_, ?_, ?_, ?_⟩
  · have hm := congrArg₂ (fun x z : E => k.inner (boundaryPhasePoint k σ v (t - a)) x z)
      hvel hvel
    exact hm.trans (hphase.1.trans hunit)
  · intro w hw
    have hcov := (boundaryPhase_physical_jacobi k W σ hσ v hv a w t ht).2.2
    have hp := hphase.2.1 w hw
    have hl := congrArg (fun z : E => k.inner (boundaryPhasePoint k σ v (t - a))
      (boundaryPhaseJacobiLinear k σ v (t - a) w) z) hvel
    have hr := congrArg₂ (fun x z : E => k.inner (boundaryPhasePoint k σ v (t - a)) x z)
      hcov hvel
    exact ⟨hl.trans hp.1, hr.trans hp.2⟩
  · intro w z
    have hcovw := (boundaryPhase_physical_jacobi k W σ hσ v hv a w t ht).2.2
    have hcovz := (boundaryPhase_physical_jacobi k W σ hσ v hv a z t ht).2.2
    have hl := congrArg (fun x : E => k.inner (boundaryPhasePoint k σ v (t - a)) x
      (boundaryPhaseJacobiLinear k σ v (t - a) z)) hcovw
    have hr := congrArg (fun x : E => k.inner (boundaryPhasePoint k σ v (t - a))
      (boundaryPhaseJacobiLinear k σ v (t - a) w) x) hcovz
    exact (congrArg₂ (fun x y : ℝ => x - y) hl hr).trans (hphase.2.2.1 w z)
  · intro w
    exact ⟨(boundaryPhase_physical_jacobi k W σ hσ v hv a w t ht).1,
      (boundaryPhase_physical_jacobi k W σ hσ v hv a w t ht).2.1⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
