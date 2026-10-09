import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Volume
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

/-!
# CH12-S18 / V1a, group B: local (non-complete) ball-image lemmas

Local versions of `eventually_edist_map_le_on_closed_ball` and
`eventually_ball_subset_image_closed_ball` of `Pointed/Convergence/BallImage.lean`: the hypothesis
`MetricComplete P` is replaced by compactness of the one closed ball actually used.
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

omit [I.Boundaryless] in
theorem PointedRiemannianConvergenceMaps.eventually_edist_map_le_local_S18
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (p : P.M) {r R L : ℝ} (hr : 0 ≤ r) (hbuf : 3 * r < R) (hL : 1 < L)
    (hK : IsCompact (riemannianClosedBallOf P.metric p R)) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p R ⊆ F.source i ∧
      ∀ x ∈ riemannianClosedBallOf P.metric p r,
        ∀ y ∈ riemannianClosedBallOf P.metric p r,
          riemannianEDistOf (X.obj (phi i)).metric (F.map i x) (F.map i y) ≤
            ENNReal.ofReal L * riemannianEDistOf P.metric x y := by
  have heps : 0 < L ^ 2 - 1 := by nlinarith
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href _ hK
    (L ^ 2 - 1) heps
  filter_upwards [eventually_ge_atTop N] with i hi
  refine ⟨(hN i hi).1, fun x hx y hy => ?_⟩
  have hupper : ∀ z ∈ riemannianClosedBallOf P.metric p R, ∀ v : TangentSpace I z,
      (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) ≤
        L ^ 2 * P.metric.inner z v v := by
    intro z hz v
    have herr := (abs_le.mp ((hN i hi).2 z hz v)).2
    nlinarith
  exact edistOf_map_le_of_metric_upper_on_buffered_ball
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i) p x y hr hbuf
    (by linarith : 0 < L) (hN i hi).1 hupper hx hy

omit [I.Boundaryless] in
theorem PointedRiemannianConvergenceMaps.eventually_ball_subset_image_local_S18
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (p : P.M) {A R L : ℝ}
    (hL : 1 < L) (hmargin : L * A < R)
    (hK : IsCompact (riemannianClosedBallOf P.metric p R)) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p R ⊆ F.source i ∧
      riemannianBallOf (X.obj (phi i)).metric (F.map i p) A ⊆
        F.map i '' riemannianClosedBallOf P.metric p R := by
  let _ : TopologicalSpace.MetrizableSpace P.M := _root_.Manifold.metrizableSpace I P.M
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith)
  have heps : 0 < 1 - (L ^ 2)⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hLsq).mpr (by nlinarith))
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href _ hK
    (1 - (L ^ 2)⁻¹) heps
  filter_upwards [eventually_ge_atTop N] with i hi
  let _ : TopologicalSpace.MetrizableSpace (X.obj (phi i)).M :=
    _root_.Manifold.metrizableSpace I (X.obj (phi i)).M
  refine ⟨(hN i hi).1, ?_⟩
  apply PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i)
    (r := (R - L * A) / 2) (C := L) (by linarith) hK (hN i hi).1
  · intro z hz v
    have hh := (abs_le.mp ((hN i hi).2 z hz v)).1
    have hquad : (L ^ 2)⁻¹ * P.metric.inner z v v ≤
        (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) := by
      linarith
    calc
      _ = L ^ 2 * ((L ^ 2)⁻¹ * P.metric.inner z v v) := by
        rw [← mul_assoc, mul_inv_cancel₀ hLsq.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hquad (sq_nonneg L)
  · change riemannianEDistOf P.metric p p < ENNReal.ofReal ((R - L * A) / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · linarith

end DifferentialGeometry.CheegerGromovCompactness
