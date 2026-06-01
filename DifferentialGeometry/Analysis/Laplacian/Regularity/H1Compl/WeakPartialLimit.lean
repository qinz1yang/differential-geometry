import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.GradientLipschitzBound
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.L2Inclusion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Weak partial derivatives extracted from H¹-completion approximating sequences

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and a
coordinate direction `j`, this file packages the chart-pushed weak partial
of any `u_h : H1Compl g`. The construction proceeds by promoting the linear
chart-pushed-partial map `chartPushedPartialLpLin g α j` to a continuous
linear map (via a Lipschitz bound), then extending it along the dense
uniform-inducing embedding `smoothToH1Compl` to a continuous linear map
on `H1Compl g`.

The H¹-Lipschitz bound for `chartPushedPartialLpLin g α j` is supplied as
a hypothesis to the construction, encoded in the parameter
`hLip : ChartPushedPartialLipschitz g α j`. Concrete instances of the
hypothesis are produced from the chain-rule + chart-pulled-volume identity
analysis on the chart-supported compact set `kPouCompact α`.

## Main results

* `chartPushedWeakPartialLp`: the chart-pushed weak partial as an `Lp ℝ 2`
  element (assuming the Lipschitz hypothesis).
* `chartPushedWeakPartialLp_smoothToH1Compl`: the smooth case identity.
* `chartPushedWeakPartialLp_continuous`: continuity of the resulting map.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace H1ComplWeakPartialLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitz
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- Lipschitz-witness data for the chart-pushed-partial map. The constant
`C` and the bound express the H¹-pre-norm continuity of the linear map
`chartPushedPartialLpLin g α j`. -/
structure ChartPushedPartialLipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) where
  /-- The Lipschitz constant. -/
  C : ℝ
  /-- Non-negativity of the constant. -/
  C_nonneg : 0 ≤ C
  /-- The bound on the chart-pushed-partial Lp norm. -/
  bound : ∀ v : SmoothScalar g,
    ‖chartPushedPartialLpLin (I := I) (M := M) g α j v‖ ≤ C * ‖v‖

/-- The chart-pushed-partial linear map promoted to a continuous linear
map via the Lipschitz hypothesis. -/
noncomputable def chartPushedPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushedPartialLpLin (I := I) (M := M) g α j).mkContinuous hLip.C
    hLip.bound

@[simp] lemma chartPushedPartialCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedPartialCLM (I := I) (M := M) g α j hLip v =
      chartPushedPartialLpLin (I := I) (M := M) g α j v := rfl

/-- `smoothToH1Compl` has dense range. -/
private lemma denseRange_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- `smoothToH1Compl` is uniform-inducing. -/
private lemma isUniformInducing_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

/-- The continuous linear extension of `chartPushedPartialCLM` along the
dense uniform-inducing embedding `smoothToH1Compl`. -/
noncomputable def H1ComplPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    H1Compl g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  ContinuousLinearMap.extend
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (smoothToH1Compl (I := I) (M := M) g)

@[simp] lemma H1ComplPartialCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    H1ComplPartialCLM (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialCLM (I := I) (M := M) g α j hLip v := by
  unfold H1ComplPartialCLM
  exact ContinuousLinearMap.extend_eq
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (e := smoothToH1Compl (I := I) (M := M) g)
    (denseRange_smoothToH1Compl_local (I := I) (M := M) g)
    (isUniformInducing_smoothToH1Compl_local (I := I) (M := M) g) v

/-- For `u_h : H1Compl g` and chart point `α`, the chart-pushed weak partial
is the L²-limit of the chart-pushed classical partials of any smooth
approximating sequence. The construction requires a Lipschitz witness
`hLip : ChartPushedPartialLipschitz g α j`. -/
noncomputable def chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (u_h : H1Compl g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  H1ComplPartialCLM (I := I) (M := M) g α j hLip u_h

/-- The chart-pushed weak partial agrees with the chart-pushed classical
partial on smooth scalars. -/
@[simp] theorem chartPushedWeakPartialLp_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v) := by
  unfold chartPushedWeakPartialLp
  rw [H1ComplPartialCLM_smoothToH1Compl]
  rfl

/-- The chart-pushed weak partial is a continuous function of `u_h`. -/
theorem chartPushedWeakPartialLp_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    Continuous (chartPushedWeakPartialLp (I := I) (M := M) g α j hLip) := by
  unfold chartPushedWeakPartialLp
  exact (H1ComplPartialCLM (I := I) (M := M) g α j hLip).continuous

end H1ComplWeakPartialLimit
end Laplacian
end Analysis
end DifferentialGeometry

end
