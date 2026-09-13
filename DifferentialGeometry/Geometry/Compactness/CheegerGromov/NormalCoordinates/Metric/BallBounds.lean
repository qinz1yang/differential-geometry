import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.FramedBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
  (metricCoerciveConst le_metricCoerciveConst metricCoerciveConst_le)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance seqBallBoundsFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance seqBallBoundsFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

structure SeqBallNormalCoordMetricBounds
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  metricC : Nat -> Nat -> Real
  metricC_nonneg : forall n p : Nat, 0 <= metricC n p
  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x
  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))
  metric_deriv :
    forall (n p j : Nat), n + p <= j ->
      forall x : (X.obj j).M,
        (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
         letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
         letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
         riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
           ENNReal.ofReal (n : Real)) ->
        NormalCoordMetricDerivBound (I := I) (X.obj j) x
          (Metric.ball (0 : E) (radius j x)) p (metricC n p)

namespace SeqBallNormalCoordMetricBounds

omit [NeZero (Module.finrank Real E)] in
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X) (f : Nat -> Nat)
    (hf : forall j : Nat, j <= f j) :
    SeqBallNormalCoordMetricBounds (I := I) (X.subseq f) where
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => h.radius (f k) x
  radius_pos := fun k x => h.radius_pos (f k) x
  metric_equiv := by
    intro k x
    with_unfolding_all
      exact h.metric_equiv (f k) x
  metric_deriv := by
    intro n p j hnj x hx
    with_unfolding_all
      exact h.metric_deriv n p (f j) (le_trans hnj (hf j)) x hx

omit [NeZero (Module.finrank Real E)] in
def of_normalCoordMetricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) :
    SeqBallNormalCoordMetricBounds (I := I) X where
  metricC := fun _ p => h.metricC p
  metricC_nonneg := fun _ p => h.metricC_nonneg p
  radius := h.radius
  radius_pos := h.radius_pos
  metric_equiv := h.metric_equiv
  metric_deriv := by
    intro n p j _hnj x _hx
    with_unfolding_all
      exact h.metric_deriv j p x

omit [NeZero (Module.finrank Real E)] in
theorem metric_deriv_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    {n p j : Nat} (hnj : n + p <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real))) :
    NormalCoordMetricDerivBound (I := I) (X.obj j) x
      (Metric.ball (0 : E) (h.radius j x)) p (h.metricC n p) :=
  h.metric_deriv n p j hnj x hx

omit [NeZero (Module.finrank Real E)] in
theorem metric_deriv_basepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    {n p j : Nat} (hnj : n + p <= j) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     NormalCoordMetricDerivBound (I := I) (X.obj j) (X.obj j).basepoint
       (Metric.ball (0 : E) (h.radius j (X.obj j).basepoint)) p (h.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  refine h.metric_deriv n p j hnj _ ?_
  rw [riemannianEDistOf_self]
  simp

omit [NeZero (Module.finrank Real E)] in
theorem c2RadiusNormalBallChart_metricDerivBound
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    {n p j : Nat} (hnj : n + p <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real))) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (c2RadiusNormalBallChart (I := I) (X.obj j) x).MetricDerivBound
       (X.obj j).metric (Metric.ball (0 : E) (h.radius j x)) p (h.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have h0 := h.metric_deriv_le (I := I) hnj hx
  simpa only [NormalCoordMetricDerivBound,
    Geometry.Riemannian.NormalCoordinates.NormalBallChart.MetricDerivBound,
    c2_radius_normal_ball_chart_metric] using h0

theorem half_le_metricCoerciveConst
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) :=
       (X.obj k).t2TangentBundle
     (1 / 2 : Real) <= metricCoerciveConst (I := I) (X.obj k).metric x) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have h0 : (0 : E) ∈ Metric.ball 0 (h.radius k x) := by
    rw [Metric.mem_ball, dist_self]
    exact h.radius_pos k x
  apply le_metricCoerciveConst (I := I)
  intro v
  rw [← normal_coord_metric_zero (I := I) (X.obj k) x]
  exact (h.metric_equiv k x 0 h0 v).1

theorem half_le_metric_inner
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) :=
       (X.obj k).t2TangentBundle
     ∀ v : E, (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (X.obj k).metric.inner x v v) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  intro v
  have h1 : (1 / 2 : Real) ≤ metricCoerciveConst (I := I) (X.obj k).metric x :=
    h.half_le_metricCoerciveConst k x
  have h2 := metricCoerciveConst_le (I := I) (X.obj k).metric x v
  nlinarith [sq_nonneg ‖v‖, h1, h2]

omit [NeZero (Module.finrank Real E)] in
theorem fderiv_apply_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    {n j : Nat} (hnj : n + 1 <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real)))
    {z : E} (hz : z ∈ Metric.ball (0 : E) (h.radius j x)) (u v w : E) :
    ‖fderiv Real (normalCoordMetric (I := I) (X.obj j) x) z u v w‖ <=
      h.metricC n 1 * ‖u‖ * ‖v‖ * ‖w‖ := by
  let D := fderiv Real (normalCoordMetric (I := I) (X.obj j) x) z
  let T := iteratedFDeriv Real 1 (normalCoordMetric (I := I) (X.obj j) x) z
  have hT : ‖T‖ ≤ h.metricC n 1 := h.metric_deriv n 1 j hnj x hx z hz
  have hDu : ‖D u‖ ≤ h.metricC n 1 * ‖u‖ := by
    calc
      ‖D u‖ = ‖T (fun _ : Fin 1 ↦ u)‖ := by
        simp only [D, T, iteratedFDeriv_one_apply]
      _ ≤ ‖T‖ * ∏ _ : Fin 1, ‖u‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖u‖ := by simp
      _ ≤ h.metricC n 1 * ‖u‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg u)
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ (D u) v w
    _ ≤ (h.metricC n 1 * ‖u‖) * ‖v‖ * ‖w‖ := by
      gcongr
    _ = h.metricC n 1 * ‖u‖ * ‖v‖ * ‖w‖ := rfl

omit [NeZero (Module.finrank Real E)] in
theorem koszul_vec_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallNormalCoordMetricBounds (I := I) X)
    {n j : Nat} (hnj : n + 1 <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real)))
    {z : E} (hz : z ∈ Metric.ball (0 : E) (h.radius j x)) (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv j x).coercive hz)
        (fderiv Real (normalCoordMetric (I := I) (X.obj j) x) z) v w‖ ≤
      3 * h.metricC n 1 * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszul_vec_norm_le
    ((h.metric_equiv j x).coercive hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv j x z hz u).1)
    (fderiv Real (normalCoordMetric (I := I) (X.obj j) x) z)
    (C := h.metricC n 1) (h.metricC_nonneg n 1)
    (h.fderiv_apply_le hnj hx hz) v w
  norm_num at hraw ⊢
  ring_nf at hraw ⊢
  exact hraw

end SeqBallNormalCoordMetricBounds

structure SeqBallFramedCoordMetricBounds
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  A : Real
  A_pos : 0 < A
  metricC : Nat -> Nat -> Real
  metricC_nonneg : forall n p : Nat, 0 <= metricC n p
  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x
  radius_le_A : forall (k : Nat) (x : (X.obj k).M), radius k x <= A
  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
       letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
       letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
       riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x <=
         ENNReal.ofReal A) ->
      FramedCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))
  metric_deriv :
    forall (n p j : Nat), n + p <= j ->
      forall x : (X.obj j).M,
        (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
         letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
         letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
         riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
           ENNReal.ofReal (min A (n : Real))) ->
        FramedCoordMetricDerivBound (I := I) (X.obj j) x
          (Metric.ball (0 : E) (radius j x)) p (metricC n p)

namespace SeqBallFramedCoordMetricBounds

omit [NeZero (Module.finrank Real E)] in
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X) (f : Nat -> Nat)
    (hf : forall j : Nat, j <= f j) :
    SeqBallFramedCoordMetricBounds (I := I) (X.subseq f) where
  A := h.A
  A_pos := h.A_pos
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => h.radius (f k) x
  radius_pos := fun k x => h.radius_pos (f k) x
  radius_le_A := fun k x => h.radius_le_A (f k) x
  metric_equiv := by
    intro k x hx
    with_unfolding_all
      exact h.metric_equiv (f k) x hx
  metric_deriv := by
    intro n p j hnj x hx
    with_unfolding_all
      exact h.metric_deriv n p (f j) (le_trans hnj (hf j)) x hx

omit [NeZero (Module.finrank Real E)] in
def of_framedCoordMetricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : FramedCoordMetricBounds (I := I) X) :
    SeqBallFramedCoordMetricBounds (I := I) X where
  A := h.A
  A_pos := h.A_pos
  metricC := fun _ p => h.metricC p
  metricC_nonneg := fun _ p => h.metricC_nonneg p
  radius := h.radius
  radius_pos := h.radius_pos
  radius_le_A := h.radius_le_A
  metric_equiv := by
    intro k x hx
    with_unfolding_all
      exact h.metric_equiv k x hx
  metric_deriv := by
    intro n p j _hnj x hx
    with_unfolding_all
      exact h.metric_deriv j p x
        (hx.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))

omit [NeZero (Module.finrank Real E)] in
theorem metric_deriv_basepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X)
    {n p j : Nat} (hnj : n + p <= j) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     FramedCoordMetricDerivBound (I := I) (X.obj j) (X.obj j).basepoint
       (Metric.ball (0 : E) (h.radius j (X.obj j).basepoint)) p (h.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  refine h.metric_deriv n p j hnj _ ?_
  rw [riemannianEDistOf_self]
  simp

theorem framedNormalBallChart_metricDerivBound
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X)
    {n p j : Nat} (hnj : n + p <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (min h.A (n : Real)))) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (framedNormalBallChart (I := I) (X.obj j) x).MetricDerivBound
       (X.obj j).metric (Metric.ball (0 : E) (h.radius j x)) p (h.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  exact
    (framed_normal_ball_chart_metricDerivBound_iff (I := I) (X.obj j) x
      (Metric.ball (0 : E) (h.radius j x)) p (h.metricC n p)).mpr
      (h.metric_deriv n p j hnj x hx)

end SeqBallFramedCoordMetricBounds

end CheegerGromovCompactness
end DifferentialGeometry
