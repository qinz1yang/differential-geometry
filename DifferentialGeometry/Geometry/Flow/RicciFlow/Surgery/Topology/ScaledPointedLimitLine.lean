import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.SeparatingSegments
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.SeparatedSidePoint
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_line_of_scaled_pointed_limit_of_separating_set
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∀ {f : ℕ → ℕ}, StrictMono f → ∀ {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
      (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F),
      (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      MetricComplete P → ConnectedSpace P.M →
    ∀ (S V W : ∀ n, Set ((H n).stageAt (t n)).Carrier), (∀ n, IsOpen (V n)) →
      (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) → ∀ {B : ℝ}, 0 ≤ B →
    (∀ n, ∀ z ∈ S n,
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) z ≤
        ENNReal.ofReal (B / Real.sqrt (R n))) →
    (∀ A : ℝ, B < A → ∀ᶠ n in atTop,
      riemannianClosedBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (3 * A / Real.sqrt (R n)) \ S n ⊆ V n ∪ W n ∧
      ∃ p ∈ V n, ∃ q ∈ W n,
        ENNReal.ofReal (A / Real.sqrt (R n)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) p ∧
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) p <
          ENNReal.ofReal (3 * A / Real.sqrt (R n)) ∧
        ENNReal.ofReal (A / Real.sqrt (R n)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) q ∧
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) q <
          ENNReal.ofReal (3 * A / Real.sqrt (R n))) →
    ∃ line : ℝ → P.M, ∀ a b : ℝ,
      riemannianEDistOf P.metric (line a) (line b) = ENNReal.ofReal |a - b| := by
  intro X f hf P F C hcan hPc hconn S V W hV hW hVW B hB hS hpoints
  let g : ∀ n, SmoothRiemannianMetric ThreeModel ((H n).stageAt (t n)).Carrier :=
    fun n => (H n).stageMetric ((H n).activeStage (t n)) (t n)
  have hsq : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hR n)
  have hscaled : ∀ n (z : ((H n).stageAt (t n)).Carrier),
      riemannianEDistOf (scaleMetric (R n) (hR n) (g n)) (y n) z =
        ENNReal.ofReal (Real.sqrt (R n)) * riemannianEDistOf (g n) (y n) z := fun n z =>
    edistOf_scale (R n) (hR n) (g n) (y n) z
  have hmulA : ∀ n (a : ℝ), ENNReal.ofReal (Real.sqrt (R n)) *
      ENNReal.ofReal (a / Real.sqrt (R n)) = ENNReal.ofReal a := by
    intro n a
    rw [← ENNReal.ofReal_mul (hsq n).le, mul_div_cancel₀ _ (hsq n).ne']
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcan]
    rfl
  exact exists_pointed_metric_line_of_eventual_minimizing_segments_intersecting_bounded_sets C
    href hPc hconn (fun k => S (f k)) hB
    (fun k z hz => by
      change riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) z ≤ _
      rw [hscaled (f k), ← hmulA (f k) B]
      gcongr
      exact hS (f k) z hz)
    (fun A hBA => by
      filter_upwards [hf.tendsto_atTop.eventually (hpoints A hBA)] with k hk
      obtain ⟨hcov, p₀, hp₀, q₀, hq₀, hpa, hpc, hqa, hqc⟩ := hk
      have hA0 : 0 ≤ A := hB.trans hBA.le
      have hBA' : B / Real.sqrt (R (f k)) < A / Real.sqrt (R (f k)) :=
        div_lt_div_of_pos_right hBA (hsq (f k))
      have hbB : 0 ≤ B / Real.sqrt (R (f k)) := div_nonneg hB (hsq (f k)).le
      have hcov' : riemannianBallOf (g (f k)) (y (f k)) (3 * A / Real.sqrt (R (f k))) \
          S (f k) ⊆ V (f k) ∪ W (f k) := fun z hz =>
        hcov ⟨show riemannianEDistOf (g (f k)) (y (f k)) z ≤ _ from le_of_lt hz.1, hz.2⟩
      obtain ⟨p, hp, hpd⟩ :=
        Geometry.Metric.exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g (f k))
        (hV (f k)) (hW (f k)) (hVW (f k)) hbB hBA' (hS (f k)) hcov' hp₀ hpa hpc
      obtain ⟨q, hq, hqd⟩ :=
        Geometry.Metric.exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g (f k))
        (hW (f k)) (hV (f k)) (hVW (f k)).symm hbB hBA' (hS (f k))
        (by rw [union_comm]; exact hcov') hq₀ hqa hqc
      have hpX : riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) p =
          ENNReal.ofReal A := by
        rw [hscaled (f k), hpd, hmulA]
      have hqX : riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) q =
          ENNReal.ofReal A := by
        rw [hscaled (f k), hqd, hmulA]
      have hballX : riemannianClosedBallOf (scaleMetric (R (f k)) (hR (f k)) (g (f k)))
          (y (f k)) (3 * A) = riemannianClosedBallOf (g (f k)) (y (f k))
            (3 * A / Real.sqrt (R (f k))) := by
        rw [← riemannianClosedBallOf_scaleMetric (R (f k)) (hR (f k)) (g (f k)) (y (f k))
          (3 * A / Real.sqrt (R (f k))), mul_div_cancel₀ _ (hsq (f k)).ne']
      obtain ⟨γ, hγ0, hγ1, hγs, hγmem, hγmin⟩ :=
        exists_distance_parametrized_minimizer_in_closedBall
          (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) p q hA0 hpX.le hqX.le
          (isClosed_le (continuous_riemannianEDist _ _) continuous_const).isCompact
      refine ⟨γ, _, ENNReal.toReal_nonneg, hγmin, ?_, ?_, ?_⟩
      · by_contra hmiss
        simp only [not_exists, not_and] at hmiss
        have hZ : γ '' Icc 0 (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k)))
            p q).toReal ⊆ V (f k) ∪ W (f k) := by
          rintro _ ⟨s, hs, rfl⟩
          refine hcov ⟨?_, hmiss s hs⟩
          rw [← hballX]
          exact hγmem s hs
        rcases (isPreconnected_Icc.image γ hγs.continuousOn).subset_or_subset (hV (f k))
            (hW (f k)) (hVW (f k)) hZ with hZV | hZW
        · exact disjoint_left.mp (hVW (f k))
            (hγ1 ▸ hZV ⟨_, ⟨ENNReal.toReal_nonneg, le_rfl⟩, rfl⟩) hq
        · exact disjoint_left.mp (hVW (f k)) hp
            (hγ0 ▸ hZW ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩, rfl⟩)
      · change (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k))
          (γ 0)).toReal = A
        rw [hγ0, hpX, ENNReal.toReal_ofReal hA0]
      · change (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k))
          (γ _)).toReal = A
        rw [hγ1, hqX, ENNReal.toReal_ofReal hA0])

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
