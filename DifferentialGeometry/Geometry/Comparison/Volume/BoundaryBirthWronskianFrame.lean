import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthCovariantPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleWronskian

/-!
One actual original common pole family yields native interior smooth Jacobi angular directions.
Its native angular Wronskians vanish by the actual covariant pairing and genuine pole initial data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthWronskian_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_wronskian_frame (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthWronskian_infty_ne_zero (M := M)
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
          (∀ q ∈ V, ∀ w : E,
            IsJacobiAt k (fun r => ρ (q.1, r))
                (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2 ∧
              ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                (fun r => (⟨ρ (q.1, r), boundaryJointJacobiLinear
                  (I := 𝓘(ℝ, E)) ρ q.1 r w⟩ : TangentBundle 𝓘(ℝ, E) U)) q.2) ∧
          (∀ q ∈ V, ∀ w z : E,
            jacobiWronskian k (fun r => ρ (q.1, r))
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w)
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r z) q.2 = 0) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, (v, t) ∈ V := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthWronskian_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hbirth⟩ :=
    exists_boundary_common_pole_family g p b hb
  let y := extChartAt I p p
  have hgeo : ∀ q ∈ V, HasGeodesicEquationAt k (fun r => ρ (q.1, r)) q.2 :=
    fun q hq => (hall q hq).2.2.2
  have hpair := boundaryBirthJacobi_covariant_pairing g p G O hG V ρ hρ
    (fun q hq => ⟨(hall q hq).2.1, (hall q hq).2.2.1⟩)
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_, ?_, hbirth⟩
  · intro q hq w
    exact boundaryJointJacobiLinear_jacobi k V ρ hρ hgeo q.1 w q.2 hq
  · intro q hq w z
    let γ := fun r => ρ (q.1, r)
    let Jw := fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w
    let Jz := fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r z
    let Γ := boundaryPoleFlowFamily G y q.1
    let Pw := fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r w
    let Pz := fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r z
    have hleft := hpair q hq w z
    have hright : k.inner (γ q.2) (Jw q.2) (covDerivAlong k γ Jz q.2) =
        G.inner (Γ q.2) (covDerivAlong G Γ Pz q.2) (Pw q.2) :=
      (k.symm (γ q.2) (Jw q.2) (covDerivAlong k γ Jz q.2)).trans (hpair q hq z w)
    have hzero := boundaryPoleJacobiLinear_wronskian_zero G y q.1 w z q.2 (hall q hq).1
    change jacobiWronskian k γ Jw Jz q.2 = 0
    calc
      _ = G.inner (Γ q.2) (covDerivAlong G Γ Pw q.2) (Pz q.2) -
          G.inner (Γ q.2) (covDerivAlong G Γ Pz q.2) (Pw q.2) :=
        congrArg₂ (fun a b : ℝ => a - b) hleft hright
      _ = jacobiWronskian G Γ Pw Pz q.2 :=
        congrArg (fun a : ℝ => G.inner (Γ q.2) (covDerivAlong G Γ Pw q.2) (Pz q.2) - a)
          (G.symm (Γ q.2) (covDerivAlong G Γ Pz q.2) (Pw q.2))
      _ = 0 := hzero

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
