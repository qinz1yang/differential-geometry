import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.DefsReplay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseChartReplayBlock

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter Topology
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace SeqBallNormalChartData

omit [CompleteSpace E] in
def radiusProfileFloor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) : Real :=
  d.ratio * hd.mu R

omit [CompleteSpace E] in
def shellRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (s R : Real) : Real :=
  s * d.radiusProfileFloor R

omit [CompleteSpace E] in
theorem radiusProfileFloor_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) :
    0 < d.radiusProfileFloor R :=
  mul_pos d.ratio_pos (hd.mu_pos R)

omit [CompleteSpace E] in
theorem shellRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {s R : Real} (hs : 0 < s) :
    0 < d.shellRadius s R :=
  mul_pos hs (d.radiusProfileFloor_pos R)

omit [CompleteSpace E] in
theorem radiusProfileFloor_le_chart_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {j : Nat} {x : (X.obj j).M} {R : Real}
    (hR : hd.dist j x (X.obj j).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    d.radiusProfileFloor R ≤ (d.chart j x).radius := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  rw [radiusProfileFloor, d.radius_eq j x]
  exact mul_le_mul_of_nonneg_left (hd.mu_antitone hR) d.ratio_pos.le

omit [CompleteSpace E] in
theorem shellRadius_lt_chart_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {j : Nat} {x : (X.obj j).M} {s R : Real}
    (hR : hd.dist j x (X.obj j).basepoint ≤ R) (hs : s < 1) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    d.shellRadius s R < (d.chart j x).radius := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hX : 0 < d.ratio * hd.mu R := mul_pos d.ratio_pos (hd.mu_pos R)
  rw [shellRadius, radiusProfileFloor, d.radius_eq j x]
  calc
    s * (d.ratio * hd.mu R) < 1 * (d.ratio * hd.mu R) :=
      mul_lt_mul_of_pos_right hs hX
    _ ≤ d.ratio * hd.mu (hd.dist j x (X.obj j).basepoint) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left (hd.mu_antitone hR) d.ratio_pos.le

omit [CompleteSpace E] in
theorem phaseRadius_eq_shellRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (R : Real) :
    d.phaseRadius R = d.shellRadius (1 / 4) R := by
  rw [phaseRadius, shellRadius, radiusProfileFloor]
  ring

omit [CompleteSpace E] in
theorem ball_phaseRadius_subset_shellRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {R s : Real} (hs : 1 / 4 ≤ s) :
    Metric.ball (0 : E) (d.phaseRadius R) ⊆ Metric.ball (0 : E) (d.shellRadius s R) := by
  apply Metric.ball_subset_ball
  have hX : 0 < d.ratio * hd.mu R := mul_pos d.ratio_pos (hd.mu_pos R)
  rw [phaseRadius, shellRadius, radiusProfileFloor]
  nlinarith [hX]

omit [CompleteSpace E] in
theorem exists_metricBounds_shellRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ (n : Real))
    {R s : Real} (hR : hd.dist j x (X.obj j).basepoint ≤ R) (hs0 : 0 < s) (hs1 : s < 1) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
      b.radius = d.shellRadius s R ∧
        ∀ q : Nat, n + q ≤ j → b.C q = d.metricC n q := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  exact exists_metricBounds_of_lt_radius (I := I) d hreal x hn (d.shellRadius s R)
    (d.shellRadius_pos hs0) (d.shellRadius_lt_chart_radius hR hs1)

omit [CompleteSpace E] in
theorem exists_metricBounds_radiusProfileFloor_of_offShell
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ (n : Real))
    {R : Real} (hR : hd.dist j x (X.obj j).basepoint ≤ R)
    (CF : Nat → Real) (hCF : ∀ q : Nat, 0 ≤ CF q)
    (hshell : ∀ q : Nat, n + q ≤ j → d.metricC n q ≤ CF q)
    (hfull : ∀ q : Nat, ¬ n + q ≤ j →
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
      (d.chart j x).MetricDerivBound (X.obj j).metric
        (Metric.ball (0 : E) (d.radiusProfileFloor R)) q (CF q)) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
       b.radius = d.radiusProfileFloor R ∧
       (∀ q : Nat, n + q ≤ j → b.C q = d.metricC n q) ∧
       ∀ q : Nat, b.C q ≤ CF q) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hsub : Metric.ball (0 : E) (d.radiusProfileFloor R) ⊆
      Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball (d.radiusProfileFloor_le_chart_radius hR)
  have hx : riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
      ENNReal.ofReal (n : Real) :=
    InjectivityRadiusDecay.riemannianEDistOf_basepoint_le_of_dist_le (I := I) hreal hn
  refine ⟨
    { C := fun q => if n + q ≤ j then d.metricC n q else CF q
      C_nonneg := fun q => ?_
      radius := d.radiusProfileFloor R
      radius_pos := d.radiusProfileFloor_pos R
      equiv := fun z hz v => d.metric_equiv j x z (hsub hz) v
      deriv := fun q z hz => ?_ }, rfl, ?_, ?_⟩
  · by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using d.metricC_nonneg n q
    · simpa only [hq, if_false] using hCF q
  · by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using d.metric_deriv n q j hq x hx z (hsub hz)
    · simpa only [hq, if_false] using hfull q hq z hz
  · intro q hq
    simp only [hq, if_true]
  · intro q
    by_cases hq : n + q ≤ j
    · simpa only [hq, if_true] using hshell q hq
    · simp only [hq, if_false]
      exact le_rfl

omit [CompleteSpace E] in
theorem exists_metricBounds_radiusProfileFloor_of_boundedGeometry
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d₀ : BoundedGeometryNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M) (hn : hd.dist j x (X.obj j).basepoint ≤ (n : Real))
    {R : Real} (hR : hd.dist j x (X.obj j).basepoint ≤ R) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     ∃ b : (((SeqBallNormalChartData.of_boundedGeometryNormalChartData
       (I := I) d₀).chart j x).MetricBounds (X.obj j).metric),
       b.radius = d₀.ratio * hd.mu R ∧ ∀ q : Nat, b.C q ≤ d₀.metricC q) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hfull : ∀ q : Nat, ¬ n + q ≤ j →
      (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
       letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
       letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
       letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
       ((SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d₀).chart j x
         ).MetricDerivBound (X.obj j).metric
         (Metric.ball (0 : E) (d₀.ratio * hd.mu R)) q (d₀.metricC q)) := by
    intro q _ z hz
    have hsub : Metric.ball (0 : E) (d₀.ratio * hd.mu R) ⊆
        Metric.ball (0 : E)
          ((SeqBallNormalChartData.of_boundedGeometryNormalChartData
            (I := I) d₀).chart j x).radius :=
      Metric.ball_subset_ball (radiusProfileFloor_le_chart_radius (I := I)
        (SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d₀) hR)
    exact d₀.metric_deriv j q x z (hsub hz)
  obtain ⟨b, hb, -, hC⟩ :=
    exists_metricBounds_radiusProfileFloor_of_offShell (I := I)
      (SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d₀)
      hreal x hn hR d₀.metricC d₀.metricC_nonneg (fun q _ => le_rfl) hfull
  exact ⟨b, hb, hC⟩

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
