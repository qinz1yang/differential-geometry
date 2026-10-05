import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart

/-!
# The LC85 slim sphere-or-torus packet

Blueprint LC85 (`def:collapse-slim-packet`, master207A:30962): a slim chart (`SlimChart`: the actual
splitting, the adapted coordinate `η` with LFR19's clauses, the enclosure, the proper buffered
restriction trivial over the interval, the cutoff) together with the fibre type: the ENTIRE zero
fibre `{x ∈ B(p, L) | η x = 0}` is connected and homeomorphic to `S²` or to `T²`
(LFR20 item 2; the smooth types come from LFR17 for the model factor).

Producer (sequence form, modulo LFR14 data): `eventually_nonempty_slimPacket`
(`SlimPacketApplications.lean`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC85 slim sphere-or-torus packet** at normalized scale: a slim chart whose entire zero fibre
in `B(p, 10⁶Δ)` is connected and homeomorphic to `S²` or `T²`. -/
structure SlimPacket (g : SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (Δ σ : ℝ)
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β)
    extends SlimChart g hEnorm Δ σ α where
  /-- The entire zero fibre is connected. -/
  zeroLevel_connected : ConnectedSpace {x // x ∈ ball p (10 ^ 6 * Δ) ∧ coord x = 0}
  /-- The entire zero fibre is a sphere or a torus. -/
  zeroLevel_type :
    Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ coord x = 0} ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
      Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ coord x = 0} ≃ₜ
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))

end DifferentialGeometry.Geometry.Collapse
