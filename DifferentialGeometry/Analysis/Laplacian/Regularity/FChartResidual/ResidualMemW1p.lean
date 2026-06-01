import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.MemW1pResidualFull
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothApproxSeq.Cauchy
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothApproxSeq.Identification

/-!
# Truly unconditional `MemW1p 2` of `fChartResidual g α u_h` for
`u_h ∈ laplacianDomainPow g 2`

The hypothesis-bearing constructor
`MemW1pFChartResidualFull.fChartResidual_memW1p_unconditional`
reduces the chart-target `MemW1p 2` discharge of `fChartResidual g α u_h` to
two analytical hypotheses on the smooth approximator sequence:

* `h_cauchy`: chart-target `W^{1,2}`-Cauchy property of `smoothFChartResidual`
  along the smooth approximator sequence.
* `h_identification`: chart-target `W^{1,2}`-limit identification with
  `fChartResidual g α u_h` a.e.

Both hypotheses are discharged unconditionally by:

* `SmoothApproxSeqCauchy.smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy`
* `SmoothApproxSeqIdentification.smoothApproxSeq_smoothFChartResidual_limit_eq_fChartResidual`

Composing yields the **truly unconditional** form of the residual `MemW1p 2`
discharge.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace FChartResidualMemW1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualFull
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchy
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqIdentification

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Truly unconditional `MemW1p 2 fChartResidual`**.

For any `u_h ∈ laplacianDomainPow g 2` and any chart base point `α : M`, the
chart-pulled residual `fChartResidual g α u_h` is in `MemW1p 2
(chartTargetEuclid α)`, **with no further hypotheses**.

This is the unconditional discharge of the chart-pulled residual `MemW1p 2`
requirement.

Proof: composes the existing hypothesis-bearing constructor
`fChartResidual_memW1p_unconditional` with the unconditional discharges of its
two analytical hypotheses (`smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy`
and `smoothApproxSeq_smoothFChartResidual_limit_eq_fChartResidual`). -/
theorem fChartResidual_memW1p_truly_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  fChartResidual_memW1p_unconditional (I := I) (M := M) g α hu_h
    (smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy
      (I := I) (M := M) g α hu_h)
    (smoothApproxSeq_smoothFChartResidual_limit_eq_fChartResidual
      (I := I) (M := M) g α hu_h)

end FChartResidualMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
