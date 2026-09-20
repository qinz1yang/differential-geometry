import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Bundle.FiberBundleHausdorff
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uF uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

def PointedRiemannianManifold.transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} I) (e : E ≃L[ℝ] F) :
    PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e) where
  M := P.M
  topology := P.topology
  charted := P.charted
  smooth := inferInstance
  t2 := P.t2
  sigmaCompact := P.sigmaCompact
  t2TangentBundle := inferInstance
  basepoint := P.basepoint
  metric := P.metric.transContinuousLinearEquiv e

def PointedRiemannianSeq.transContinuousLinearEquiv
    (X : PointedRiemannianSeq.{u, uE, uH} I) (e : E ≃L[ℝ] F) :
    PointedRiemannianSeq.{u, uF, uH} (I.transContinuousLinearEquiv e) where
  obj i := (X.obj i).transContinuousLinearEquiv e

def PointedRiemannianManifold.ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    PointedRiemannianManifold.{u, uE, uH} I := by
  let _ : IsManifold I ∞ P.M :=
    (ModelWithCorners.isManifold_transContinuousLinearEquiv_iff I e P.M ∞).mp P.smooth
  exact {
    M := P.M
    topology := P.topology
    charted := P.charted
    smooth := inferInstance
    t2 := P.t2
    sigmaCompact := P.sigmaCompact
    t2TangentBundle := inferInstance
    basepoint := P.basepoint
    metric := Diffeomorph.pullbackMetricCross P.metric
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I P.M e) }

theorem PointedRiemannianManifold.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F) (P : PointedRiemannianManifold.{u, uF, uH} (I.transContinuousLinearEquiv e)) :
    (P.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  let _ : IsManifold I ∞ M :=
    (ModelWithCorners.isManifold_transContinuousLinearEquiv_iff I e M ∞).mp smooth
  have hg : (Diffeomorph.pullbackMetricCross g
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e)).transContinuousLinearEquiv e = g := by
    rw [SmoothRiemannianMetric.transContinuousLinearEquiv, Diffeomorph.pullbackMetricCross_trans]
    have heq : (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm.trans
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e) =
          _root_.Diffeomorph.refl (I.transContinuousLinearEquiv e) M ∞ := by ext x; rfl
    rw [heq, Diffeomorph.pullbackMetricCross_refl]
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1


theorem PointedRiemannianManifold.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (P : PointedRiemannianManifold.{u, uE, uH} I) (e : E ≃L[ℝ] F) :
    (P.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = P := by
  rcases P with @⟨M, topology, charted, smooth, sigmaCompact, t2, t2Tangent, base, g⟩
  let _ := topology
  let _ := charted
  let _ := smooth
  let _ := sigmaCompact
  let _ := t2
  have hg := g.pullback_transContinuousLinearEquiv e
  dsimp only [PointedRiemannianManifold.ofTransContinuousLinearEquiv,
    PointedRiemannianManifold.transContinuousLinearEquiv]
  congr 1

theorem PointedRiemannianManifold.transContinuousLinearEquiv_surjective
    (e : E ≃L[ℝ] F) :
    Function.Surjective (fun P : PointedRiemannianManifold.{u, uE, uH} I =>
      P.transContinuousLinearEquiv e) :=
  fun P => ⟨P.ofTransContinuousLinearEquiv e, P.transContinuousLinearEquiv_ofTransContinuousLinearEquiv e⟩


end DifferentialGeometry.CheegerGromovCompactness
