import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInwardTransfer
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorLift

/-!
A strictly inward chart velocity constructs a smooth original-metric launch in the true interior.
The launch retains its actual chart derivative at the boundary and its original base point.
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
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

theorem exists_boundary_inward_original_smooth (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
    ∃ γ : ℝ → E, ∃ ε : ℝ, 0 < ε ∧ γ 0 = extChartAt I p p ∧ HasDerivAt γ v 0 ∧
      (extChartAt I p).symm (γ 0) = p ∧
      ∀ t ∈ Ioo 0 ε,
        ContMDiffAt 𝓘(ℝ) I ∞ (fun s => (extChartAt I p).symm (γ s)) t ∧
        HasGeodesicEquationAt g (fun s => (extChartAt I p).symm (γ s)) t ∧
        I.IsInteriorPoint ((extChartAt I p).symm (γ t)) := by
  obtain ⟨G, U, hpU, hG, γ, hγ0, hder, hgeo0, ε, hε, hgeo, henter⟩ :=
    exists_boundary_inward_ambient_geodesic g p b hb v hin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (DifferentialGeometry.Geometry.eventually_isGeodesicAt hgeo0)
  have htarget {t : ℝ} (ht : t ∈ Ioo 0 ε) :
      γ t ∈ interior (extChartAt I p).target := by
    rw [extChartAt_target, interior_inter,
      ((chartAt H p).open_target.preimage I.continuous_symm).interior_eq]
    exact ⟨(henter t ht).1.2, (henter t ht).2⟩
  have hstart : (extChartAt I p).symm (γ 0) = p := by
    rw [hγ0]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  refine ⟨γ, min ε r, lt_min hε hr, hγ0, hder, hstart, ?_⟩
  intro t ht
  have htε : t ∈ Ioo 0 ε := ⟨ht.1, ht.2.trans_le (min_le_left ε r)⟩
  have htr : t ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_right ε r)
  have hsmooth := ambient_geodesic_smooth G γ t (hball htr)
  have hchart : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (γ t) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      (mem_interior_iff_mem_nhds.mp (htarget htε))
  have horiginal := boundaryChart_geodesicEquation g p G U hG γ t
    ⟨(henter t htε).1.1, htarget htε⟩ hsmooth (hgeo t htε)
  have hinterior : I.IsInteriorPoint ((extChartAt I p).symm (γ t)) :=
    DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞
      (by simp) ((DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target (htarget htε))
  exact ⟨hchart.comp t hsmooth, horiginal, hinterior⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
