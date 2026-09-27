import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
  (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))

include hgram in
private theorem gramPi_full (x₀ : M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartGramPi (g p.1) x₀ p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  exact chartGramOnE_set g J x₀ hgram i j

include hgram in
theorem chartMetricJets_contDiffOn (x₀ : M) (a : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => iteratedFDeriv ℝ a (chartGramPi (g p.1) x₀) p.2)
      (J ×ˢ interior (extChartAt I x₀).target) :=
  DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn
    (G := fun t y => chartGramPi (g t) x₀ y) isOpen_interior (gramPi_full g J hgram x₀) a

include hJ hgram in
private theorem gramJet2_full (x₀ : M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => jet2 (chartGramPi (g p.1) x₀) p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  have h0 := gramPi_full g J hgram x₀
  have h1 := spatialFDeriv_contDiffOn (G := fun t y => chartGramPi (g t) x₀ y)
    hJ isOpen_interior h0
  have h2 := spatialFDeriv_contDiffOn (G := fun t y => fderiv ℝ (chartGramPi (g t) x₀) y)
    hJ isOpen_interior h1
  exact h0.prodMk (h1.prodMk h2)

private theorem gramJet2_det_ne (t : ℝ) (x₀ : M) (y : E)
    (hy : y ∈ interior (extChartAt I x₀).target) :
    (Matrix.of (jet2 (chartGramPi (g t) x₀) y).1).det ≠ 0 := by
  have hx : (extChartAt I x₀).symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (interior_subset hy)
  have he : Matrix.of (jet2 (chartGramPi (g t) x₀) y).1 =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g t) x₀ ((extChartAt I x₀).symm y) := by
    ext i j
    simp only [jet2, chartGramPi, chartGramOnE_def, Matrix.of_apply]
  rw [he]
  exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g t) x₀ hx).ne'

private theorem gramPi_static (t : ℝ) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartGramPi (g t) x₀) (interior (extChartAt I x₀).target) := by
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  exact (chartGramOnE_contDiffOn (g t) x₀ i j).mono interior_subset

include hJ hgram in
theorem chartInverseMetric_contDiffOn (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartInvGramOnE (g p.1) x₀ i j p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E => (Matrix.of (jet2 (chartGramPi (g p.1) x₀) p.2).1)⁻¹ i j)
      (J ×ˢ interior (extChartAt I x₀).target) := by
    intro p hp
    exact (contDiffAt_jetInvGram (gramJet2_det_ne g p.1 x₀ p.2 hp.2) i j).comp_contDiffWithinAt p
      (gramJet2_full g J hJ hgram x₀ p hp)
  exact hm.congr (fun p _ => (jet2_chartGram_invGram (g p.1) x₀ p.2 i j).symm)

include hJ hgram in
theorem chartChristoffel_contDiffOn (x₀ : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartChristoffel (g p.1) x₀ i j k p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      jetChristoffel (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (chartGramPi (g p.1) x₀) p.2) i j k)
      (J ×ˢ interior (extChartAt I x₀).target) := by
    intro p hp
    exact (contDiffAt_jetChristoffel (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
      (gramJet2_det_ne g p.1 x₀ p.2 hp.2) i j k).comp_contDiffWithinAt
      (f := fun q : ℝ × E => jet2 (chartGramPi (g q.1) x₀) q.2) p
      (gramJet2_full g J hJ hgram x₀ p hp)
  apply hm.congr
  intro p hp
  exact chartChristoffel_eq_jet (g p.1) x₀
    (((gramPi_static g p.1 x₀).contDiffAt (isOpen_interior.mem_nhds hp.2)).differentiableAt
      (by simp)) i j k

include hJ hgram in
theorem chartRiemann_contDiffOn (x₀ : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartRiemannTensor (g p.1) x₀ i j k l p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      jetRiemann (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (chartGramPi (g p.1) x₀) p.2) i j k l)
      (J ×ˢ interior (extChartAt I x₀).target) := by
    intro p hp
    exact (contDiffAt_jetRiemann (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
      (gramJet2_det_ne g p.1 x₀ p.2 hp.2) i j k l).comp_contDiffWithinAt p
      (gramJet2_full g J hJ hgram x₀ p hp)
  apply hm.congr
  intro p hp
  have hs := gramPi_static g p.1 x₀
  have hsa := hs.contDiffAt (isOpen_interior.mem_nhds hp.2)
  apply chartRiemann_eq_jet (g p.1) x₀ hp.2 (hsa.differentiableAt (by simp))
  · filter_upwards [isOpen_interior.mem_nhds hp.2] with y hy
    exact (hs.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
  · exact (hsa.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
end DifferentialGeometry.PDE.RicciFlow
