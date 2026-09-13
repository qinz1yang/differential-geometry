import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : forall x : M, forall v : TangentSpace I x,
  ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

omit [CompleteSpace E] in
theorem IntrinsicBallChart.metric_eq_intrinsicFrameMetric
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) (hr : 0 < r) :
    EqOn ((c.toNormalBallChart (I := I) g hEnorm p hr).metric g)
      (intrinsicFrameMetric (I := I) g hEnorm p) (Metric.ball (0 : E) r) := by
  intro z hz
  ext v w
  rw [NormalBallChart.metric_apply (I := I) (p := p), intrinsicFrameMetric_apply]
  have hev : c.hom =ᶠ[nhds z] intrinsicFramedExp (I := I) g hEnorm p :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
      (fun q hq => c.hom_eq hq)
  have hD : mfderiv (modelWithCornersSelf Real E) I c.hom z =
      mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hev
  change g.inner (c.hom z)
      (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
      (mfderiv (modelWithCornersSelf Real E) I c.hom z w) =
    g.inner (intrinsicFramedExp (I := I) g hEnorm p z)
      (mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) z v)
      (mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) z w)
  rw [c.hom_eq hz, hD]

omit [CompleteSpace E] in
theorem IntrinsicBallChart.contDiffOn_intrinsicFrameMetric
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) (hr : 0 < r) :
    ContDiffOn Real ∞ (intrinsicFrameMetric (I := I) g hEnorm p) (Metric.ball (0 : E) r) := by
  have hsm : ContDiffOn Real ∞
      ((c.toNormalBallChart (I := I) g hEnorm p hr).metric g) (Metric.ball (0 : E) r) :=
    NormalBallChart.metric_cont_diff_on (I := I) g
      (c.toNormalBallChart (I := I) g hEnorm p hr) Metric.isOpen_ball
      (c.toNormalBallChart (I := I) g hEnorm p hr).smooth_to
  exact hsm.congr fun z hz =>
    (c.metric_eq_intrinsicFrameMetric (I := I) g hEnorm p hr hz).symm

omit [CompleteSpace E] in
theorem IntrinsicBallChart.contDiffAt_intrinsicFrameMetric
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) (hr : 0 < r)
    {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    ContDiffAt Real ∞ (intrinsicFrameMetric (I := I) g hEnorm p) z :=
  (c.contDiffOn_intrinsicFrameMetric (I := I) g hEnorm p hr).contDiffAt
    (Metric.isOpen_ball.mem_nhds hz)

omit [CompleteSpace E] in
theorem IntrinsicBallChart.metricEquivOn_of_intrinsicFrameMetric
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) (hr : 0 < r)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
        intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ 2 * ‖v‖ ^ 2) :
    (c.toNormalBallChart (I := I) g hEnorm p hr).MetricEquivOn g (Metric.ball (0 : E) r) := by
  intro z hz v
  rw [c.metric_eq_intrinsicFrameMetric (I := I) g hEnorm p hr hz]
  exact h z hz v

omit [CompleteSpace E] in
theorem IntrinsicBallChart.metricDerivBound_of_intrinsicFrameMetric
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) (hr : 0 < r)
    (q : Nat) {C : Real}
    (h : ∀ z ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv Real q (intrinsicFrameMetric (I := I) g hEnorm p) z‖ ≤ C) :
    (c.toNormalBallChart (I := I) g hEnorm p hr).MetricDerivBound g
      (Metric.ball (0 : E) r) q C :=
  NormalBallChart.MetricDerivBound.of_eq_on (I := I) g Metric.isOpen_ball
    (c.metric_eq_intrinsicFrameMetric (I := I) g hEnorm p hr) h

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
