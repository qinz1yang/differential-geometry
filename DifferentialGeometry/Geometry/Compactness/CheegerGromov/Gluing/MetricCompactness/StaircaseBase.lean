import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.Assumptions
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.BallRadiusProfile
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.BallBounds
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
variable [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance staircaseBaseFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance staircaseBaseFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

structure StaircaseMetricCompactBase
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  decay : InjectivityRadiusDecay (I := I) X
  pack : forall D : Real, 0 < D -> decay.PackingBound D
  volume : BallMultiplicityBound (I := I) X
  dist_eq : volume.dist = decay.dist
  realizes : decay.RealizesDistance
  normalBounds : SeqBallFramedCoordMetricBounds (I := I) X
  normalRadius : BallRadiusProfile (I := I) decay normalBounds.radius

namespace StaircaseMetricCompactBase

def toSeed
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : StaircaseMetricCompactBase (I := I) X) :
    MetricCompactSeed (I := I) X where
  decay := b.decay
  packAll := b.pack
  volume := b.volume
  dist_eq := b.dist_eq
  realizes := b.realizes

instance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} :
    Coe (StaircaseMetricCompactBase (I := I) X) (MetricCompactSeed (I := I) X) :=
  ⟨toSeed⟩

theorem metricCoerciveRatio_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : StaircaseMetricCompactBase (I := I) X) :
    0 < b.normalRadius.metricCoerciveRatio :=
  BallRadiusProfile.metricCoerciveRatio_pos (I := I) b.normalRadius

def ofFramedCoordMetricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (decay : InjectivityRadiusDecay (I := I) X)
    (pack : forall D : Real, 0 < D -> decay.PackingBound D)
    (volume : BallMultiplicityBound (I := I) X)
    (dist_eq : volume.dist = decay.dist)
    (realizes : decay.RealizesDistance)
    (normalBounds : FramedCoordMetricBounds (I := I) X)
    (normalRadius : BallRadiusProfile (I := I) decay normalBounds.radius) :
    StaircaseMetricCompactBase (I := I) X where
  decay := decay
  pack := pack
  volume := volume
  dist_eq := dist_eq
  realizes := realizes
  normalBounds := SeqBallFramedCoordMetricBounds.of_framedCoordMetricBounds (I := I)
    normalBounds
  normalRadius := normalRadius

end StaircaseMetricCompactBase

namespace SeqBallFramedCoordMetricBounds

omit [NeZero (Module.finrank Real E)] in
theorem fderiv_bound_shift
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : SeqBallFramedCoordMetricBounds (I := I) X)
    {n j : Nat} (hnj : n + 1 <= j) {x : (X.obj j).M}
    (hx : (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (min h.A (n : Real))))
    {z : E} (hz : z ∈ Metric.ball (0 : E) (h.radius j x)) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     ‖fderiv Real (framedCoordMetric (I := I) (X.obj j) x) z‖ <= h.metricC n 1) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  rw [← norm_iteratedFDeriv_one (f := framedCoordMetric (I := I) (X.obj j) x)]
  exact h.metric_deriv n 1 j hnj x hx z hz

omit [NeZero (Module.finrank Real E)] in
theorem exists_framedMetric0_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : SeqBallFramedCoordMetricBounds (I := I) X)
    (c : forall k : Nat, (X.obj k).M) (N : Nat)
    (hc : forall k : Nat,
      (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
       letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
       letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
       riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint (c k) <=
         ENNReal.ofReal (min input.A (N : Real)))) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧ ContDiffOn Real (⊤ : ℕ∞) gInf Set.univ ∧
        MapCInfConvergenceOnCompacts Set.univ
          (fun k _ => framedCoordMetric (I := I) (X.obj (phi k)) (c (phi k)) 0)
          gInf ∧
        forall z : E, forall v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 <= gInf z v v ∧
            gInf z v v <= 2 * ‖v‖ ^ 2 := by
  let g0 : Nat -> E -> (E →L[Real] E →L[Real] Real) :=
    fun k _ => framedCoordMetric (I := I) (X.obj k) (c k) 0
  have hzero : forall k, (0 : E) ∈ Metric.ball 0 (input.radius k (c k)) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c k)
  have hcA : forall k : Nat,
      (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
       letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
       letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
       riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint (c k) <=
         ENNReal.ofReal input.A) := by
    intro k
    refine (hc k).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hsmooth : forall k, ContDiffOn Real (⊤ : ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists C : Real, ∀ᶠ k in atTop, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= C := by
    intro r K _hK _hKU
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      refine ⟨input.metricC N 0, eventually_atTop.mpr ⟨N, fun k hk => ?_⟩⟩
      intro x _hx
      let : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      have hkn : N + 0 <= k := by omega
      have hderiv := input.metric_deriv N 0 k hkn (c k) (hc k) 0 (hzero k)
      simpa only [g0, norm_iteratedFDeriv_zero] using hderiv
    · refine ⟨0, Eventually.of_forall (fun k x _hx => ?_)⟩
      simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact le_refl 0
  have hequiv : forall k : Nat, forall z, z ∈ (Set.univ : Set E) -> forall v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 <= g0 k z v v ∧
        g0 k z v v <= 2 * ‖v‖ ^ 2 := by
    intro k _z _hz v
    exact input.metric_equiv k (c k) (hcA k) 0 (hzero k) v
  simpa only [g0, Set.mem_univ, forall_const] using
    (exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd
      (E := E) isOpen_univ g0 hsmooth hbdd (1 / 2) 2 hequiv)

end SeqBallFramedCoordMetricBounds

omit [NeZero (Module.finrank Real E)] in
theorem framedCoordMetric_zero_eq_innerSL_and_normalCoordMetric_zero_eq_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    (letI : TopologicalSpace Y.M := Y.topology
     letI : ChartedSpace H Y.M := Y.charted
     letI : IsManifold I ∞ Y.M := Y.smooth
     letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
     framedCoordMetric (I := I) Y x 0 =
         (innerSL Real : E →L[Real] E →L[Real] Real) ∧
       normalCoordMetric (I := I) Y x 0 = Y.metric.inner x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨framedCoordMetric_zero (I := I) Y x, normal_coord_metric_zero (I := I) Y x⟩

end CheegerGromovCompactness
end DifferentialGeometry
