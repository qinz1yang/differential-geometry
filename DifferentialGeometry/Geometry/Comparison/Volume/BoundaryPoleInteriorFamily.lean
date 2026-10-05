import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPolePositiveFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseSeed
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorEquation

/-!
The entire original positive pole birth family lifts to its genuine boundaryless interior atlas.
Joint smoothness and the actual interior geodesic equation hold on one shared open domain.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
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

private theorem poleInterior_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_pole_interior_family (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      poleInterior_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ V : Opens (E × ℝ),
          (∀ t ∈ Ioo 0 ε, (v, t) ∈ V) ∧ ∃ ρ : E × ℝ → U,
            ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
            ∀ q ∈ V,
              ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
                G.geodesicFlowDomain ∧
              boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
                (O : Set E) ∩ interior (extChartAt I p).target ∧
              (ρ q : M) = (extChartAt I p).symm
                (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
              HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    poleInterior_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, ε, hε, V, hcenter, hall, hsmooth⟩ :=
    exists_boundary_pole_positive_family g p b hb v hin
  let R : E × ℝ → M := fun q => (extChartAt I p).symm
    (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)
  have henter : ∀ q ∈ V, I.IsInteriorPoint (R q) := fun q hq => (hall q hq).2.2.1
  have hmid : ε / 2 ∈ Ioo 0 ε := by constructor <;> linarith
  obtain ⟨ρ, _σ, hval, hρ, _hσ, _hseed⟩ :=
    boundary_original_phase_seed V R hsmooth henter v (ε / 2) (hcenter (ε / 2) hmid)
  refine ⟨G, hcomplete, O, hpO, hG, ε, hε, V, hcenter, ρ, hρ, ?_⟩
  intro q hq
  refine ⟨(hall q hq).1, (hall q hq).2.1, hval q hq, ?_⟩
  have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t => ρ (q.1, t)) q.2 :=
    (hρ.contMDiffAt (V.isOpen.mem_nhds hq)).comp
      (f := fun t : ℝ => (q.1, t)) q.2
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hnear : ∀ᶠ t in 𝓝 q.2, (q.1, t) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq
  have hev : (fun t => ((ρ (q.1, t) : U) : M)) =ᶠ[𝓝 q.2]
      (fun t => R (q.1, t)) := by
    filter_upwards [hnear] with t ht
    exact hval (q.1, t) ht
  have horig := HasGeodesicEquationAt.congr_of_eventuallyEq_at
    hev.eq_of_nhds hev (hall q hq).2.2.2
  exact (boundaryInteriorAtlas_geodesicEquation_iff g (fun t => ρ (q.1, t)) q.2 hslice).mpr
    horig

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
