import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.StaircaseBase
import DifferentialGeometry.Analysis.Calculus.Compactness.EventuallyBounded

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]


namespace SeqBallFramedCoordMetricBounds

def trimRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X) {rho : Real} (hrho : 0 < rho) :
    SeqBallFramedCoordMetricBounds (I := I) X where
  A := h.A
  A_pos := h.A_pos
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => min (h.radius k x) rho
  radius_pos := fun k x => lt_min (h.radius_pos k x) hrho
  radius_le_A := fun k x => (min_le_left _ _).trans (h.radius_le_A k x)
  metric_equiv := by
    intro k x hx
    exact fun z hz v =>
      h.metric_equiv k x hx z (Metric.ball_subset_ball (min_le_left _ _) hz) v
  metric_deriv := by
    intro n p j hnj x hx
    exact fun z hz =>
      h.metric_deriv n p j hnj x hx z (Metric.ball_subset_ball (min_le_left _ _) hz)

omit [NeZero (Module.finrank Real E)] in
theorem metric_deriv_one_of_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X)
    {n j : Nat} (hnj : n + 1 <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (min h.A (n : Real)))) :
    FramedCoordMetricDerivBound (I := I) (X.obj j) x
      (Metric.ball (0 : E) (h.radius j x)) 1 (h.metricC n 1) :=
  h.metric_deriv n 1 j hnj x hx

end SeqBallFramedCoordMetricBounds

namespace StaircaseMetricCompactBase

omit [CompleteSpace E] in
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : StaircaseMetricCompactBase (I := I) X)
    (f : Nat -> Nat) (hf : StrictMono f) :
    StaircaseMetricCompactBase (I := I) (X.subseq f) where
  decay := b.decay.subseq f
  pack := fun D hD => (b.pack D hD).subseq f
  volume := b.volume.subseq f
  dist_eq := by
    funext k x y
    change b.volume.dist (f k) x y = b.decay.dist (f k) x y
    rw [b.dist_eq]
  realizes := b.realizes.subseq f
  normalBounds := b.normalBounds.subseq f (fun j => hf.id_le j)
  normalRadius := b.normalRadius.subseq f

end StaircaseMetricCompactBase

end CheegerGromovCompactness
end DifferentialGeometry
