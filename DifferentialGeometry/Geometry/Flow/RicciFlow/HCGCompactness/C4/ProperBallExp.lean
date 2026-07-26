import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric

/-!
# Proper metric balls and exponential images

Bridges between the realized proper metric used by the compactness construction
and the intrinsic normal-coordinate radii supplied by Gauss-lemma geometry.
-/

noncomputable section

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- A realized proper-metric closed ball below the radial normal radius is the
framed exponential image of any larger Euclidean model ball. -/
theorem properBall_to_exp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (ms : MetricSpace Y.M)
    (hreal : ∀ x y : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       edist x y) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
       dist x y))
    {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hσ : R < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := ms
    Metric.closedBall c R ⊆
      framedExpMap (I := I) Y.metric c '' Metric.ball 0 σ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  intro q hq
  have hdistLe : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := hreal c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hsmall :
      (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdistLe.trans_lt hR
  obtain ⟨v, _hvTarget, _hvDomain, hvLen, hqEq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  let z : E := (normalFrame (I := I) Y.metric c).symm
    (show TangentSpace I c from v)
  have hzFrame : normalFrame (I := I) Y.metric c z =
      (show TangentSpace I c from v) := by
    dsimp only [z]
    exact (normalFrame (I := I) Y.metric c).apply_symm_apply _
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖z‖ = Real.sqrt (Y.metric.inner c
        (show TangentSpace I c from v) (show TangentSpace I c from v)) := by
      calc
        ‖z‖ = Real.sqrt (Y.metric.inner c
            (normalFrame (I := I) Y.metric c z)
            (normalFrame (I := I) Y.metric c z)) :=
          (normalFrame_sqrt (I := I) Y.metric c z).symm
        _ = Real.sqrt (Y.metric.inner c
            (show TangentSpace I c from v) (show TangentSpace I c from v)) := by
          rw [hzFrame]
    rw [hnorm, hvLen, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdistLe.trans_lt hσ
  · calc
      framedExpMap (I := I) Y.metric c z =
          expMap (I := I) Y.metric c (normalFrame (I := I) Y.metric c z) := rfl
      _ = expMap (I := I) Y.metric c (show TangentSpace I c from v) :=
        congrArg (expMap (I := I) Y.metric c) hzFrame
      _ = q := hqEq.symm

/-- The orthonormally framed exponential sends the Euclidean `8 * lam` ball
into the realized physical `16 * lam` ball. -/
theorem exp_sigma_maps
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (ms : MetricSpace Y.M)
    (hreal : ∀ p q : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       edist p q) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
       dist p q))
    (x : Y.M) {lam : Real}
    (hGp :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      8 * lam ≤ expRadiusGp (I := I) Y.metric x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := ms
    Set.MapsTo
      (framedExpMap (I := I) Y.metric x)
      (Metric.ball 0 (8 * lam)) (Metric.ball x (16 * lam)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := ms
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ y : Y.M, ∀ v : TangentSpace I y,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v)) := by
    intro y v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  rw [Metric.mem_ball]
  have hzGp : ‖z‖ < expRadiusGp (I := I) Y.metric x := hz.trans_le hGp
  have hzC2 : ‖(show E from normalFrame (I := I) Y.metric x z)‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hzGp
  have hedLe := edist_exp_le_radius (I := I) Y.metric x
    (show E from normalFrame (I := I) Y.metric x z) hEnorm hzC2
  have hed :
      riemannianEDist I x
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z)) =
        ENNReal.ofReal
          (dist x (expMap (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z))) := by
    have h := hreal x
      (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hdistSqrt :
      dist x (expMap (I := I) Y.metric x
        (normalFrame (I := I) Y.metric x z)) ≤
        Real.sqrt (Y.metric.inner x
          (normalFrame (I := I) Y.metric x z)
          (normalFrame (I := I) Y.metric x z)) := by
    rw [hed] at hedLe
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hedLe
  rw [framedExpMap_apply]
  calc
    dist (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z)) x =
        dist x (expMap (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z)) := dist_comm _ _
    _ ≤ Real.sqrt (Y.metric.inner x
        (normalFrame (I := I) Y.metric x z)
        (normalFrame (I := I) Y.metric x z)) := hdistSqrt
    _ = ‖z‖ := normalFrame_sqrt (I := I) Y.metric x z
    _ < 16 * lam := by
      have hlam : 0 < lam := by nlinarith [norm_nonneg z]
      nlinarith

end HCGCompactness
end DifferentialGeometry
