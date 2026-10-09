import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import DifferentialGeometry.Geometry.Comparison.BallCapture

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance inverseCaptureComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance inverseCaptureLimitTopology : TopologicalSpace L.M := L.topology
private local instance inverseCaptureLimitCharted : ChartedSpace H L.M := L.charted
private local instance inverseCaptureLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance inverseCaptureLimitOne : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
private local instance inverseCaptureLimitT2 : T2Space L.M := L.t2
private local instance inverseCaptureLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance inverseCaptureApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance inverseCaptureApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance inverseCaptureApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance inverseCaptureApproxOne (k : ℕ) :
    IsManifold I 1 (X.obj k).M :=
  IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
private local instance inverseCaptureApproxT2 (k : ℕ) :
    T2Space (X.obj k).M := (X.obj k).t2
private local instance inverseCaptureApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

theorem pointed_metric_eventually_inverse_ball_capture
    (z : L.M) {R r factor : ℝ} (hr : 0 ≤ r) (hfactor : 1 < factor)
    (hbuffer : factor * r < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric z R))
    (hconv : metricSourceConvergesOn Φ
      (CanonicalMetricCompactness.canonicalSourceData Φ)
      (riemannianClosedBallOf L.metric z R) 0) :
    ∀ᶠ k in atTop, riemannianClosedBallOf L.metric z R ⊆ Φ.source k ∧
      ∀ y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) r,
        y ∈ (Φ.partialDiffeomorph k).target ∧
        (Φ.partialDiffeomorph k).symm y ∈ Φ.source k ∧
        (Φ.partialDiffeomorph k).symm y ∈
          riemannianClosedBallOf L.metric z (factor * r) ∧
        Φ.map k ((Φ.partialDiffeomorph k).symm y) = y := by
  have hfactorpos : 0 < factor := zero_lt_one.trans hfactor
  have hfactorSq : 1 < factor ^ 2 := by nlinarith
  have hfactorSqPos : 0 < factor ^ 2 := sq_pos_of_pos hfactorpos
  let delta : ℝ := 1 - (factor ^ 2)⁻¹
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact sub_pos.mpr ((inv_lt_one₀ hfactorSqPos).2 hfactorSq)
  filter_upwards [pointed_metric_eventually_quadratic_bounds hcompact hconv hdelta] with k hk
  refine ⟨hk.1, ?_⟩
  intro y hy
  have hlower (x : L.M) (hx : x ∈ riemannianClosedBallOf L.metric z R)
      (v : TangentSpace I x) :
      L.metric.inner x v v ≤ factor ^ 2 *
        (X.obj (subseq k)).metric.inner (Φ.map k x)
          (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x v) := by
    have h := (hk.2 x hx v).1
    have hsmall : (factor ^ 2)⁻¹ * L.metric.inner x v v ≤
        (X.obj (subseq k)).metric.inner (Φ.map k x)
          (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x v) := by
      simpa only [delta, sub_sub_cancel] using h
    calc
      _ = factor ^ 2 * ((factor ^ 2)⁻¹ * L.metric.inner x v v) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hfactorSqPos), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hfactorSqPos.le
  obtain ⟨hytarget, hyball⟩ :=
    PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
      L.metric (X.obj (subseq k)).metric (Φ.partialDiffeomorph k) z
      hr hfactorpos hbuffer hcompact hk.1 hlower y hy
  exact ⟨hytarget, (Φ.partialDiffeomorph k).map_target' hytarget,
    hyball, (Φ.partialDiffeomorph k).right_inv' hytarget⟩

end DifferentialGeometry.CheegerGromovCompactness

end
