import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Bundle Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_metricSpace_closedBall
    (g : SmoothRiemannianMetric I M) (q : M) {r : ℝ} :
    ∃ m : MetricSpace (riemannianClosedBallOf g q r),
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (riemannianClosedBallOf g q r)) ∧
      ∀ x y : riemannianClosedBallOf g q r,
        @dist _ m.toDist x y = (riemannianEDistOf g x y).toReal := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hfin : ∀ x y : riemannianClosedBallOf g q r, edist x y ≠ ⊤ := by
    intro x y
    change riemannianEDistOf g (x : M) (y : M) ≠ ⊤
    apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    calc riemannianEDistOf g (x : M) (y : M)
        ≤ riemannianEDistOf g (x : M) q + riemannianEDistOf g q (y : M) :=
          riemannianEDistOf_triangle g _ _ _
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
        rw [riemannianEDistOf_comm g (x : M) q]
        exact add_le_add x.property y.property
  let m := EMetricSpace.toMetricSpace hfin
  exact ⟨m, rfl, fun _ _ => rfl⟩

end DifferentialGeometry.Geometry.Riemannian
