import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter Topology
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace SeqBallNormalChartData

omit [CompleteSpace E] in
def chartMap
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat)
    (x : (X.obj k).M) : E → (X.obj k).M :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  (d.chart k x).hom

omit [CompleteSpace E] in
theorem chartMap_of_boundedGeometryNormalChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
     (of_boundedGeometryNormalChartData (I := I) d).chartMap k x = d.chartMap k x) :=
  rfl

omit [CompleteSpace E] in
theorem exists_metricDerivBound_of_lt_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (j : Nat) (x : (X.obj j).M)
    (q : Nat) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∀ σ : Real, σ < (d.chart j x).radius →
      ∃ C : Real, 0 ≤ C ∧
        (d.chart j x).MetricDerivBound (X.obj j).metric
          (Metric.ball (0 : E) σ) q C := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  intro σ hσ
  let σ' : Real := (σ + (d.chart j x).radius) / 2
  have hσ' : σ < σ' := by
    simp only [σ']
    linarith [(d.chart j x).radius_pos]
  have hσ'rad : σ' < (d.chart j x).radius := by
    simp only [σ']
    linarith
  let U : Set E := Metric.ball (0 : E) σ'
  have hU : IsOpen U := Metric.isOpen_ball
  have hUrad : U ⊆ Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball hσ'rad.le
  have hcont : ContDiffOn Real (⊤ : ℕ∞) ((d.chart j x).metric (X.obj j).metric) U :=
    (d.chart j x).metric_cont_diff_on (X.obj j).metric hU
      ((d.chart j x).smooth_to.mono hUrad)
  have hK : IsCompact (Metric.closedBall (0 : E) σ) := isCompact_closedBall _ _
  have hKU : Metric.closedBall (0 : E) σ ⊆ U := Metric.closedBall_subset_ball hσ'
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hcont.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top (a := (q : ℕ∞)))) hU.uniqueDiffOn).mono hKU)
  exact ⟨max M 0, le_max_right M 0, fun z hz => by
    have hzK : z ∈ Metric.closedBall (0 : E) σ := Metric.ball_subset_closedBall hz
    rw [← iteratedFDerivWithin_of_isOpen q hU (hKU hzK)]
    exact (hM z hzK).trans (le_max_left M 0)⟩

omit [CompleteSpace E] in
theorem exists_metricBounds_of_lt_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    {n j : Nat} (x : (X.obj j).M)
    (hn : hd.dist j x (X.obj j).basepoint ≤ n) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∀ σ : Real, 0 < σ → σ < (d.chart j x).radius →
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = σ ∧ ∀ q, n + q ≤ j → b.C q = d.metricC n q := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  have hx : riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x ≤
      ENNReal.ofReal (n : Real) := by
    let : EMetricSpace (X.obj j).M := (X.obj j).emetricSpace
    have hbridge : (edist (X.obj j).basepoint x) =
        riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x := rfl
    rw [← hbridge, edist_comm, hreal.edist_eq j x (X.obj j).basepoint]
    exact ENNReal.ofReal_le_ofReal hn
  intro σ hσpos hσ
  have hsub : Metric.ball (0 : E) σ ⊆ Metric.ball (0 : E) (d.chart j x).radius :=
    Metric.ball_subset_ball hσ.le
  refine ⟨
    { C := fun q => if n + q ≤ j then d.metricC n q
        else max 0 (Classical.choose
          (exists_metricDerivBound_of_lt_radius (I := I) d j x q σ hσ))
      C_nonneg := fun q => ?_
      radius := σ
      radius_pos := hσpos
      equiv := fun z hz v => d.metric_equiv j x z (hsub hz) v
      deriv := fun q z hz => ?_ }, rfl, ?_⟩
  · by_cases h : n + q ≤ j
    · simpa only [h, if_true] using d.metricC_nonneg n q
    · simpa only [h, if_false] using le_max_left 0 _
  · by_cases h : n + q ≤ j
    · simpa only [h, if_true] using d.metric_deriv n q j h x hx z (hsub hz)
    · simpa only [h, if_false] using
        ((Classical.choose_spec
          (exists_metricDerivBound_of_lt_radius (I := I) d j x q σ hσ)).2 z hz).trans
          (le_max_right 0 _)
  · intro q hq
    simp only [hq, if_true]

omit [CompleteSpace E] in
theorem offShell_metricDerivBound_of_radius_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {n j : Nat} (x : (X.obj j).M) :
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
    ∀ b : (d.chart j x).MetricBounds (X.obj j).metric,
      b.radius = (d.chart j x).radius →
      ∀ q, ¬ n + q ≤ j →
        (d.chart j x).MetricDerivBound (X.obj j).metric
          (Metric.ball (0 : E) (d.chart j x).radius) q (b.C q) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  intro b hrad q _
  have h := b.deriv q
  rwa [hrad] at h

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
