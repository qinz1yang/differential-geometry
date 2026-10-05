import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryChartGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInwardGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryGeodesicRegularity
import DifferentialGeometry.Geometry.Geodesic.Local

/-!
Strictly inward chart velocities launch geodesic equations for the original metric
on a positive interval in the genuine interior, by local ambient metric extension.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]
  [manifoldSeparated : T2Space M]

theorem exists_boundary_inward_original_geodesic (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
    ∃ γ : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ γ 0 = extChartAt I p p ∧ HasDerivAt γ v 0 ∧
      IsGeodesicOn g (fun s => (extChartAt I p).symm (γ s)) (Ioo 0 ε) ∧
        ∀ t ∈ Ioo 0 ε, γ t ∈ interior (extChartAt I p).target := by
  obtain ⟨G, U, hpU, hG, γ, hγ0, hder, hgeo0, ε, hε, hgeo, henter⟩ :=
    exists_boundary_inward_ambient_geodesic g p b hb v hin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (DifferentialGeometry.Geometry.eventually_isGeodesicAt hgeo0)
  have htarget {t : ℝ} (ht : t ∈ Ioo 0 ε) :
      γ t ∈ interior (extChartAt I p).target := by
    have htchart := (henter t ht).1.2
    have htrange := (henter t ht).2
    rw [extChartAt_target, interior_inter,
      ((chartAt H p).open_target.preimage I.continuous_symm).interior_eq]
    exact ⟨htchart, htrange⟩
  refine ⟨γ, min ε r, lt_min hε hr, hγ0, hder, ?_, ?_⟩
  · intro t ht
    have htε : t ∈ Ioo 0 ε := ⟨ht.1, ht.2.trans_le (min_le_left ε r)⟩
    have htr : t ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans_le (min_le_right ε r)
    apply boundaryChart_geodesicEquation g p G U hG γ t
      ⟨(henter t htε).1.1, htarget htε⟩
      (ambient_geodesic_smooth G γ t (hball htr))
    exact hgeo t htε
  · intro t ht
    exact htarget ⟨ht.1, ht.2.trans_le (min_le_left ε r)⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
