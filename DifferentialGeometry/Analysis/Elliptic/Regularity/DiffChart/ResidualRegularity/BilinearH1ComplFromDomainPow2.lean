import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Leibniz
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem memWkpChart_two_two_smooth_mul_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      (fun x : M => (φ : M → ℝ) x *
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  have h_uh := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g hu_h).1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) (by norm_num : (1 : ℝ≥0∞) ≤ 2) φ h_uh

theorem memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hu_h
  have h_cstep := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ u_h
  rw [h_phase2] at h_cstep
  exact h_cstep

theorem memWkpChart_two_two_smoothMulLp_preimage_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hw_h_dom
  have h_cstep := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ w_h
  rw [h_phase2, hw_h_eq] at h_cstep
  exact h_cstep

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
