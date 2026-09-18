import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

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

theorem PointedRiemannianConvergenceMaps.eventually_edist_map_le_on_closed_ball
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (p : P.M) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 1 < L) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p A ⊆ F.source i ∧
      ∀ x ∈ riemannianClosedBallOf P.metric p A,
        ∀ y ∈ riemannianClosedBallOf P.metric p A,
          riemannianEDistOf (X.obj (phi i)).metric (F.map i x) (F.map i y) ≤
            ENNReal.ofReal L * riemannianEDistOf P.metric x y := by
  have hmetricComplete : RiemannianMetricComplete (I := I) P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  let K := riemannianClosedBallOf (I := I) P.metric p (3 * A + 1)
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact p (3 * A + 1)
  have heps : 0 < L ^ 2 - 1 := by nlinarith
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K hK
    (L ^ 2 - 1) heps
  filter_upwards [eventually_ge_atTop N] with i hi
  have hin : riemannianClosedBallOf (I := I) P.metric p A ⊆ K :=
    fun _ hx => hx.trans (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨hin.trans (hN i hi).1, fun x hx y hy => ?_⟩
  have hupper : ∀ z ∈ K, ∀ v : TangentSpace I z,
      (X.obj (phi i)).metric.inner (F.map i z)
          (mfderiv I I (F.map i) z v) (mfderiv I I (F.map i) z v) ≤
        L ^ 2 * P.metric.inner z v v := by
    intro z hz v
    have herr := (abs_le.mp ((hN i hi).2 z hz v)).2
    nlinarith
  exact edistOf_map_le_of_metric_upper_on_buffered_ball
    P.metric (X.obj (phi i)).metric (F.partialDiffeomorph i) p x y hA
    (by linarith : 3 * A < 3 * A + 1) (by linarith : 0 < L)
    (hN i hi).1 hupper hx hy

theorem PointedRiemannianConvergenceMaps.eventually_image_closed_ball_subset
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) (p : P.M) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 1 < L) :
    ∀ᶠ i in atTop, riemannianClosedBallOf P.metric p A ⊆ F.source i ∧
      F.map i '' riemannianClosedBallOf P.metric p A ⊆
        riemannianClosedBallOf (X.obj (phi i)).metric (F.map i p) (L * A) := by
  filter_upwards [F.eventually_edist_map_le_on_closed_ball C href hcomplete p hA hL]
    with i hi
  refine ⟨hi.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hp : p ∈ riemannianClosedBallOf P.metric p A := by
    change riemannianEDistOf P.metric p p ≤ ENNReal.ofReal A
    rw [riemannianEDistOf_self]
    exact bot_le
  calc
    _ ≤ ENNReal.ofReal L * riemannianEDistOf P.metric p x := hi.2 p hp x hx
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal A := mul_le_mul' le_rfl hx
    _ = ENNReal.ofReal (L * A) := (ENNReal.ofReal_mul (by linarith : 0 ≤ L)).symm


theorem PointedRiemannianConvergenceMaps.exists_eventually_image_compact_subset_ball
    [PreconnectedSpace P.M]
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P) {K : Set P.M} (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ i in atTop, K ⊆ F.source i ∧
      F.map i '' K ⊆
        riemannianClosedBallOf (X.obj (phi i)).metric (X.obj (phi i)).basepoint A := by
  have hcont : Continuous (fun x : P.M =>
      (riemannianEDistOf P.metric P.basepoint x).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal
      (riemannianEDistOf_ne_top P.metric P.basepoint x)).comp
      (Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint).continuousAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_right B 0]
  have hKR : K ⊆ riemannianClosedBallOf P.metric P.basepoint R := by
    intro x hx
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top P.metric P.basepoint x)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hR.le]
    exact (hB ⟨x, hx, rfl⟩).trans (by dsimp only [R]; linarith [le_max_left B 0])
  refine ⟨2 * R, by positivity, ?_⟩
  filter_upwards [F.eventually_image_closed_ball_subset C href hcomplete P.basepoint
    hR.le (by norm_num : (1 : ℝ) < 2)] with i hi
  refine ⟨hKR.trans hi.1, ?_⟩
  have hbase : F.map i P.basepoint = (X.obj (phi i)).basepoint := F.basepoint_map i
  rw [← hbase]
  exact (Set.image_mono hKR).trans hi.2

end DifferentialGeometry.CheegerGromovCompactness
