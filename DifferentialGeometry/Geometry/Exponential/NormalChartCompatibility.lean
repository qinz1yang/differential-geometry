import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.ExpInvBranch
import DifferentialGeometry.Geometry.Exponential.RawIntrinsicC2

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

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

theorem eventuallyEq_expMapDiffeo
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    (fun v => B.hom v) =ᶠ[𝓝 x] expMapDiffeo g p := by
  have hball : x ∈ Metric.ball (0 : E) (expMapC2Radius g p) := by simpa using hx
  filter_upwards [B.hom.open_source.mem_nhds hB, Metric.isOpen_ball.mem_nhds hball] with v hv hvball
  have hvsmall : ‖v‖ < expMapC2Radius g p := by simpa using hvball
  rw [expMapDiffeo_apply_eq g p (mem_expMapDiffeo_source_of_norm_lt_radius g p hvsmall)]
  exact (B.hom_eq hv).symm.trans (exp_eq_intr_of_c2 g hEnorm p hvsmall).symm

theorem inv_eventuallyEq_normalChartAt
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source) :
    B.inv =ᶠ[𝓝 (expMapIntrinsic g hEnorm p (show TangentSpace I p from x))] normalChartAt g p := by
  let q := expMapIntrinsic g hEnorm p (show TangentSpace I p from x)
  have hq : q ∈ B.dom := by
    rw [show q = B.hom x from B.hom_eq hB]
    exact B.hom.map_source hB
  have hinv : B.inv q = x := B.left_inv hB
  have hc : ContinuousAt B.inv q :=
    (B.inv_inf q hq).contMDiffAt (B.hom.open_target.mem_nhds hq) |>.continuousAt
  have hball : B.inv q ∈ Metric.ball (0 : E) (expMapC2Radius g p) := by
    rw [hinv]
    simpa using hx
  have hsmall : ∀ᶠ y in 𝓝 q, B.inv y ∈ Metric.ball (0 : E) (expMapC2Radius g p) :=
    hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hball)
  filter_upwards [B.hom.open_target.mem_nhds hq, hsmall] with y hy hysmall
  have hnorm : ‖B.inv y‖ < expMapC2Radius g p := by simpa using hysmall
  have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p hnorm
  have hexp : expMapDiffeo g p (B.inv y) = y :=
    (expMapDiffeo_apply_eq g p hsrc).trans ((exp_eq_intr_of_c2 g hEnorm p hnorm).trans (B.right_inv hy))
  have hleft : normalChartAt g p (expMapDiffeo g p (B.inv y)) = B.inv y :=
    (expMapDiffeo g p).left_inv hsrc
  rw [hexp] at hleft
  exact hleft.symm

theorem eventuallyEq_expMapDiffeo_zero
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source) :
    (fun v => B.hom v) =ᶠ[𝓝 (0 : E)] expMapDiffeo g p :=
  B.eventuallyEq_expMapDiffeo (by simpa using expMapC2Radius_pos g p) hB

theorem inv_eventuallyEq_normalChartAt_centre
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source) :
    B.inv =ᶠ[𝓝 p] normalChartAt g p := by
  have h := B.inv_eventuallyEq_normalChartAt (by simpa using expMapC2Radius_pos g p) hB
  rw [← exp_eq_intr_of_c2 g hEnorm p (u := 0) (by simpa using expMapC2Radius_pos g p)] at h
  change B.inv =ᶠ[𝓝 (expMap g p (0 : TangentSpace I p))] normalChartAt g p at h
  rw [expMap_zero] at h
  exact h

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch
