import DifferentialGeometry.Topology.Covering.Basepoint
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.Pullback.Cross

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  {a b : M}

theorem pullbackMetric_changeBasepointDiffeomorph
    (g : SmoothRiemannianMetric I M) (γ : Path.Homotopic.Quotient b a) :
    Diffeomorph.pullbackMetricCross
        (let _ : Inhabited M := ⟨b⟩; liftedMetric g) (changeBasepointDiffeomorph I γ) =
      (let _ : Inhabited M := ⟨a⟩; liftedMetric g) := by
  let Phi := changeBasepointDiffeomorph I γ
  have hd (x : @UniversalCover M _ ⟨a⟩) :
      mfderiv I I Phi x = ContinuousLinearMap.id ℝ E := by
    let _ : Inhabited M := ⟨a⟩
    have ha := (hasMFDerivAt_proj (I := I) x).mfderiv
    let _ : Inhabited M := ⟨b⟩
    have hb := hasMFDerivAt_proj (I := I) (Phi x)
    have hc := mfderiv_comp x hb.mdifferentiableAt
      (Phi.mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) x)
    rw [hb.mfderiv] at hc
    erw [ContinuousLinearMap.id_comp] at hc
    exact hc.symm.trans ha
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner]
  change g.inner x.1 (mfderiv I I Phi x v) (mfderiv I I Phi x w) = g.inner x.1 v w
  rw [hd]
  rfl

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
