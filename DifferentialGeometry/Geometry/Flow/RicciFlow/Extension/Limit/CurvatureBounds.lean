import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Limit.Smooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.AllBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Endpoint.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Endpoint.Ricci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Restart.ShiInputs
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [T2Space M] [CompactSpace M] [BoundarylessManifold I M]
variable [SigmaCompactSpace M]

def cinftyLimitDataOfAllMBounds
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
            (S.base.rm04 t x) ≤ K)
    (hEquiv : ∃ Lambda : ℝ, 1 ≤ Lambda ∧
      ∃ t1 : ℝ, t1 ∈ Set.Ico alpha omega ∧
        ∀ s : ℝ, s ∈ Set.Ico t1 omega →
          ∀ x : M, ∀ v : TangentSpace I x,
            Lambda⁻¹ * (S.base.metric alpha).inner x v v ≤
                (S.base.metric s).inner x v v ∧
              (S.base.metric s).inner x v v ≤
                Lambda * (S.base.metric alpha).inner x v v) :
    SmoothLimitData (I := I) S.base.metric alpha omega hαω := by
  classical
  have hex := exists_endMetric (I := I) S hdim hS hbound hEquiv
  refine
    { limitMetric := hex.choose
      tendsto_left := hex.choose_spec
      ricci_match := ?_ }
  intro x v w
  exact ricci_tendsto_left (I := I) S hdim hS hbound hEquiv hex.choose hex.choose_spec x v w

def cinftyLimitDataOfSolution
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    SmoothLimitData (I := I) S.base.metric alpha omega hαω := by
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    simpa [SolutionOn.family, SolutionFamily.connection, metricCov] using
      hRm (⟨t, ht⟩ : RealTimeInterval.FlowTime
        (RealTimeInterval.closedOpen alpha omega hαω))
  have hCan := canonical_curvature_norm_sq_bounded_of_realization
    (I := I) Rm04 hRmRaw hbound
  have hK := hbound.choose_spec
  have hRic := ric_quad_le_of_solution (I := I) hRmRaw hK
  have hRicConst :
      0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt hbound.choose := by
    positivity
  have hEquiv := hell_of_solution (I := I) hS hRicConst hRic
  exact cinftyLimitDataOfAllMBounds (I := I) S hS hdim hCan hEquiv

end DifferentialGeometry.PDE.RicciFlow
