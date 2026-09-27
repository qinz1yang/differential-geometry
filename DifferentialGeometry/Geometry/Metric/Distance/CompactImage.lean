import DifferentialGeometry.Topology.EMetricSpace.CompactImage
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

section

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal Manifold ContDiff

namespace DifferentialGeometry

open Bundle
open scoped Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [RegularSpace M]

theorem exists_uniform_riemannianEDistOf_bound_of_compact_preconnected
    {A : Type*} [TopologicalSpace A] [CompactSpace A] [PreconnectedSpace A]
    (g : SmoothRiemannianMetric I M) (f : C(A, M)) (a : A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : A,
      riemannianEDistOf g (f b) (f a) ≤ ENNReal.ofReal R := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact EMetric.exists_uniform_edist_bound_of_compact_preconnected f.continuous a

theorem exists_uniform_riemannianEDistOf_bound_on_loop
    (g : SmoothRiemannianMetric I M) (γ : Topology.freeLoop M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ θ : Topology.loopCircle,
      riemannianEDistOf g (γ θ) (γ 0) ≤ ENNReal.ofReal R :=
  exists_uniform_riemannianEDistOf_bound_of_compact_preconnected g γ 0

end DifferentialGeometry

end

end
