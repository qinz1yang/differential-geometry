import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Metric.Basic

/-!
# Consumers of CM2.a and CM2.b

The segment theorem for a smooth metric (`r = ⊤`, a `SmoothRiemannianMetric` regarded as
finite-order, definitionally) and Hopf–Rinow for a complete `C³` metric (`r = 2`, the lowest
covered order).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [NeZero (Module.finrank ℝ E)]

/-- Smooth metric: every unit-speed metric segment is `t ↦ exp_{c 0} (t • u)`, `|u| = 1`. -/
theorem exists_expMap_eq_of_segment_of_smooth
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {c : ℝ → M} {ℓ : ℝ}
    (hseg : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) :
    ∃ u : E, g.inner (c 0) u u = 1 ∧ ∀ t ∈ Icc 0 ℓ,
      (⟨c 0, t • u⟩ : TangentBundle I M) ∈ g.expDomain ∧
      c t = g.expMap (⟨c 0, t • u⟩ : TangentBundle I M) :=
  exists_expMap_eq_of_segment (r := ⊤) g (by exact_mod_cast le_top) hnorm hseg

/-- Hopf–Rinow for a complete `C³` metric. -/
theorem hopfRinow_finite_of_C3 [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    ProperSpace M ∧ g.geodesicFlowDomain = univ ∧
      ∀ x y : M, ∃ u : E, g.inner x u u = 1 ∧
        ∀ t ∈ Icc 0 (dist x y), dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = t ∧
          g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y :=
  hopfRinow_finite (r := 2) g le_rfl hnorm

end Bundle.ContMDiffRiemannianMetric
