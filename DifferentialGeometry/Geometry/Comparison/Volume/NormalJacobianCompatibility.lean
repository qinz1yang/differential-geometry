import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobian
import DifferentialGeometry.Geometry.Exponential.NormalChartCompatibility
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityCongruence

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch

open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem paramGramMatrix_eventuallyEq_normalGramMatrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    paramGramMatrix g B.hom =ᶠ[𝓝 x] normalGramMatrix g p :=
  paramGramMatrix_eventuallyEq g (B.eventuallyEq_expMapDiffeo hx hB)

theorem paramDensity_eventuallyEq_normalChartDensity
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    paramDensity g B.hom =ᶠ[𝓝 x] normalChartDensity g p :=
  paramDensity_eventuallyEq g (B.eventuallyEq_expMapDiffeo hx hB)

theorem paramDensity_ratio_eventuallyEq_normalJacobian
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (hB0 : (0 : E) ∈ B.hom.source) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) =ᶠ[𝓝 x] normalJacobian g p := by
  have hnum := B.paramDensity_eventuallyEq_normalChartDensity hx hB
  have hden := (B.paramDensity_eventuallyEq_normalChartDensity
    (by simpa using expMapC2Radius_pos g p) hB0).eq_of_nhds
  filter_upwards [hnum] with v hv
  change paramDensity g B.hom v / paramDensity g B.hom 0 =
    normalChartDensity g p v / normalChartDensity g p 0
  rw [hv, hden]

theorem paramDensity_ratio_eventuallyEq_normalJacobian_zero
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (hB0 : (0 : E) ∈ B.hom.source) :
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) =ᶠ[𝓝 (0 : E)] normalJacobian g p :=
  B.paramDensity_ratio_eventuallyEq_normalJacobian hB0
    (by simpa using expMapC2Radius_pos g p) hB0

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch
