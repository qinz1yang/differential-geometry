import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BallGeometry

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance seqBallInjectivityMeasurableSpaceE : MeasurableSpace E := borel E
private local instance seqBallInjectivityBorelE : BorelSpace E := ⟨rfl⟩

theorem exists_uniform_injectivity_radius_on_ball_of_seqBallGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hinj : BaseInjBound (I := I) X)
    (hball : SeqBallGeometry (I := I) X)
    (A : Real) (hA : 0 < A) :
    ∃ ρ : Real, 0 < ρ ∧ ∀ᶠ i in atTop,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      let _ : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
      ∀ x : (X.obj i).M,
        edist (X.obj i).basepoint x ≤ ENNReal.ofReal A →
          HasInjRadiusAt (I := I) (X.obj i) x ρ := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * A + 3)
  let σ : Nat → Nat := fun k => N + k
  let X' := X.subseq σ
  have hcomplete' : SeqMetricComplete (I := I) X' := hcomplete.subseq σ
  have hconn' : ∀ k : Nat,
      let _ : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      ConnectedSpace (X'.obj k).M := PointedRiemannianSeq.connected_subseq hconn σ
  have hinj' : BaseInjBound (I := I) X' := hinj.subseq σ
  have hrm' : ∀ k : Nat,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      ∀ y : (X'.obj k).M,
        edist (X'.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X'.obj k).metric y 4
          (metricRm04At (I := I) (M := (X'.obj k).M) (X'.obj k).metric y)) ≤
            hball.C N 0 := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    intro y hy
    have hy' : riemannianEDistOf (I := I) (X'.obj k).metric
        (X'.obj k).basepoint y ≤ ENNReal.ofReal (N : Real) := by
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X'.obj k)]
      exact hy.trans (ENNReal.ofReal_le_ofReal hN)
    have hjet := hball.bound N 0 (σ k) (Nat.le_add_right N k) y hy'
    exact (normSq0S_metricRm04At_le_curvDerivNorm (I := I) (X'.obj k).metric y).trans hjet
  have hpull' : ∀ k : Nat,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
      letI : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
        (X'.obj k).riemBundle (I := I)
      letI : (y : (X'.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
        (X'.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X'.obj k).M => TangentSpace I y) := (X'.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X'.obj k).M :=
        MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
      letI : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
      ∀ (x : (X'.obj k).M)
        (hEnorm : ∀ (y : (X'.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X'.obj k).metric.inner y w w)))
        (q R : Real), 0 ≤ q → 0 < R →
        (∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
          ∀ t, t ∈ Set.Ioo (0 : Real) 1 →
            ¬ IsConjVec (I := I) (X'.obj k).metric hEnorm x
              ((t • normalFrame (I := I) (X'.obj k).metric x z : TangentSpace I x) : E)) →
        ricciBoundedBelowOn (I := I) (X'.obj k).metric
          {y : (X'.obj k).M | riemannianEDist I x y < ENNReal.ofReal R}
          (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)) →
        intrinsicPullVol (I := I) (X'.obj k).metric hEnorm x R ≤
          (MeasureTheory.volume : MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) R) := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
    let : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
      (X'.obj k).riemBundle (I := I)
    let : (y : (X'.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X'.obj k).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X'.obj k).M => TangentSpace I y) := (X'.obj k).riemBundle_cont (I := I)
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    let : CompleteSpace (X'.obj k).M :=
      MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
    let : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
    intro x hEnorm q R hq hR hno hRic
    exact intrinsicPullVol_le_hyperbolic_of_ricciBoundedBelowOn
      (I := I) (X'.obj k).metric hEnorm x hq hR hno hRic
  obtain ⟨ρ, hρ, hdec⟩ :=
    exists_pos_injectivity_radius_on_ball (I := I) X' hcomplete' hconn' hinj' A hA
      (hball.C N 0) (hball.nonneg N 0) hrm' hpull'
  refine ⟨ρ, hρ, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact hdec k

end CheegerGromovCompactness
end DifferentialGeometry

end
