import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BBSAllMBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointRicciLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.ExtendShiInputs
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection



















































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow


open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [T2Space M] [CompactSpace M] [BoundarylessManifold I M]






def cinftyLimitData_of_allMBounds
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
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  classical
  -- `exists_endMetric` is `Prop`-valued while the goal is data, so the endpoint
  -- metric is extracted with `Exists.choose` rather than destructured.
  have hex := exists_endMetric (I := I) S hdim hS hbound hEquiv
  refine
    { limitMetric := hex.choose
      tendsto_left := hex.choose_spec
      ricci_match := ?_ }
  intro x v w
  exact ricci_tendsto_left (I := I) S hdim hS hbound hEquiv hex.choose hex.choose_spec x v w









def cinftyLimitData_of_solution
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    simpa [SolutionOn.family, SolutionFamily.connection] using
      hRm (⟨t, ht⟩ : RealTimeInterval.FlowTime
        (RealTimeInterval.closedOpen alpha omega hαω))
  have hCan := rm04_bound_can (I := I) Rm04 hRmRaw hbound
  have hK := hbound.choose_spec
  have hRic := ric_quad_le_of_soln (I := I) hRmRaw hK
  have hRicConst :
      0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt hbound.choose := by
    positivity
  have hEquiv := hell_of_soln (I := I) hS hRicConst hRic
  exact cinftyLimitData_of_allMBounds (I := I) S hS hdim hCan hEquiv

end DifferentialGeometry.PDE.RicciFlow
