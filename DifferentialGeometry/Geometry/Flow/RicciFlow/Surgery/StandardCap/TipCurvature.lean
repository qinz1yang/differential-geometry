import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Curvature.LocalIsometry
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section
open Bundle Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem metricRm04_tip (p : S3) {x : E3} (hxr : ‖x‖ < roundNormalRadius p)
    (hxa : ‖x‖ < transitionStart) (v w : E3) :
    metricRm04StandardAt metric x v w w v =
      (1 / 2 : ℝ) * (metric.inner x v v * metric.inner x w w - (metric.inner x v w) ^ 2) := by
  let U : Opens E3 := ⟨Metric.ball 0 (min (roundNormalRadius p) transitionStart), Metric.isOpen_ball⟩
  let Φ := roundNormalDiffeomorph p
  have hU : (U : Set E3) ⊆ Φ.source := by
    intro y hy
    apply ball_subset_roundNormalDiffeomorph_source p
    exact Metric.ball_subset_ball (min_le_left _ _) hy
  let V : Opens S3 := ⟨Φ '' (U : Set E3), image_opens_isOpen Φ hU⟩
  let Ψ : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ V := PartialDiffeomorph.toOpensDiffeo Φ hU
  let h : SmoothRiemannianMetric (𝓡 3) S3 := scaleMetric 2 (by norm_num) roundMetric
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)
  have hΦ : (Φ : E3 → S3) = roundNormalMap p := funext (roundNormalDiffeomorph_apply p)
  have hΨd (y : U) (u : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) (Ψ : U → V) y u =
        mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) (y : E3) u := by
    rw [show Ψ = PartialDiffeomorph.toOpensDiffeo Φ hU from rfl,
      PartialDiffeomorph.mfderiv_toOpensDiffeo, hΦ]
  have heq (y : U) (u z : TangentSpace (𝓡 3) y) :
      metric.inner (y : E3) u z = h.inner (Ψ y : S3)
        (mfderiv (𝓡 3) (𝓡 3) (Ψ : U → V) y u)
        (mfderiv (𝓡 3) (𝓡 3) (Ψ : U → V) y z) := by
    have hy : ‖(y : E3)‖ < min (roundNormalRadius p) transitionStart := by
      simpa only [U, Opens.mem_mk, Metric.mem_ball, dist_zero_right] using y.property
    rw [hΨd, hΨd]
    change metric.inner (y : E3) u z = 2 * roundMetric.inner (roundNormalMap p (y : E3))
      (mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) (y : E3) u)
      (mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) (y : E3) z)
    exact (metric_inner_round p (hy.trans_le (min_le_left _ _))
      (hy.le.trans (min_le_right _ _)) u z).trans
      (roundNormalMetric_inner p (hy.trans_le (min_le_left _ _)) u z)
  let xu : U := ⟨x, by simpa only [U, Opens.mem_mk, Metric.mem_ball, dist_zero_right] using lt_min hxr hxa⟩
  let A : TangentSpace (𝓡 3) (Ψ xu : S3) := by
    exact mfderiv (𝓡 3) (𝓡 3) (Ψ : U → V) xu v
  let B : TangentSpace (𝓡 3) (Ψ xu : S3) := by
    exact mfderiv (𝓡 3) (𝓡 3) (Ψ : U → V) xu w
  have hr : metricRm04StandardAt metric x v w w v = metricRm04StandardAt h (Ψ xu : S3) A B B A :=
    metricRm04StdAt_of_pullback_on_opens metric h U V Ψ heq xu v w w v
  have hs : metricRm04StandardAt h (Ψ xu : S3) A B B A =
      2 * metricRm04StandardAt (roundMetric (E := E4) (n := 3)) (Ψ xu : S3) A B B A :=
    metricRmStandard_scale 2 (by norm_num) roundMetric (Ψ xu : S3) A B B A
  have hsec := roundMetric_sec_value (Ψ xu : S3) A B
  have hv : metric.inner x v v = 2 * roundMetric.inner (Ψ xu : S3) A A := heq xu v v
  have hw : metric.inner x w w = 2 * roundMetric.inner (Ψ xu : S3) B B := heq xu w w
  have hvw : metric.inner x v w = 2 * roundMetric.inner (Ψ xu : S3) A B := heq xu v w
  calc
    _ = 2 * (roundMetric.inner (Ψ xu : S3) A A * roundMetric.inner (Ψ xu : S3) B B -
        roundMetric.inner (Ψ xu : S3) A B * roundMetric.inner (Ψ xu : S3) A B) :=
      hr.trans (hs.trans (congrArg (fun t : ℝ => 2 * t) hsec))
    _ = _ := by rw [hv, hw, hvw]; ring

theorem sectionalCurvature_tip (p : S3) {x : E3}
    (hxr : ‖x‖ < roundNormalRadius p) (hxa : ‖x‖ < transitionStart) (v w : E3)
    (hvw : metric.inner x v v * metric.inner x w w - (metric.inner x v w) ^ 2 ≠ 0) :
    sectionalCurvature metric x v w = 1 / 2 := by
  exact (sectionalCurvature_eq_metricRm04StandardAt_div metric x v w).trans
    ((congrArg (fun t : ℝ => t /
      (metric.inner x v v * metric.inner x w w - (metric.inner x v w) ^ 2))
      (metricRm04_tip p hxr hxa v w)).trans (mul_div_cancel_right₀ _ hvw))

theorem metricRm04_zero (v w : E3) :
    metricRm04StandardAt metric 0 v w w v =
      (1 / 2 : ℝ) * (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2) := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  simpa only [metric_inner_zero] using
    metricRm04_tip p (x := 0) (by simpa using roundNormalRadius_pos p)
      (by simpa using transitionStart_pos) v w

theorem sectionalCurvature_zero (v w : E3)
    (hvw : ⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    sectionalCurvature metric 0 v w = 1 / 2 := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact sectionalCurvature_tip p (x := 0) (by simpa using roundNormalRadius_pos p)
    (by simpa using transitionStart_pos) v w (by simpa only [metric_inner_zero] using hvw)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
