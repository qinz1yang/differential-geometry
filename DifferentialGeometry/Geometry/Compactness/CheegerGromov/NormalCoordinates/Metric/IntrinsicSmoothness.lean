import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

section

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : forall x : M, forall v : TangentSpace I x, ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
theorem contDiff_intrinsicFrameMetric (p : M) :
    ContDiff Real ∞ (intrinsicFrameMetric (I := I) g hEnorm p) := by
  rw [← contDiffOn_univ]
  have hs : ContMDiffOn (𝓘(Real, E)) I ∞ (intrinsicFramedExp (I := I) g hEnorm p) Set.univ :=
    (intrinsicFrame_smooth (I := I) g hEnorm p).contMDiffOn
  have hp := Geometry.contDiffOn_pullback_metric_coefficients (I := I) g (U := Set.univ) isOpen_univ hs
  rw [show intrinsicFrameMetric (I := I) g hEnorm p =
      Geometry.pullbackMetricCoefficients g (intrinsicFramedExp (I := I) g hEnorm p) by
    ext z v w
    rw [intrinsicFrameMetric_apply, Geometry.pullbackMetricCoefficients_apply]]
  exact hp
end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
