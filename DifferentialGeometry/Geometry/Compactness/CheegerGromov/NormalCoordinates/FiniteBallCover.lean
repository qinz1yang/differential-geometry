import DifferentialGeometry.Topology.EMetricSpace.UniformImageCover
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.ClosedBallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.IntrinsicLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds

section

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold Filter
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates
open Geometry.Riemannian.VolumeComparison
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_eventually_finite_ball_cover_of_local_curvature
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    {r R K : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hK : 0 ≤ K)
    (hcurv : ∀ᶠ i in atTop,
      HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R 0 K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ᶠ i in atTop,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
      letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
      ∃ c : Fin N → (X.obj i).M,
        (∀ j, riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint (c j) ≤
          ENNReal.ofReal r) ∧
        ∀ y : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint y ≤
            ENNReal.ofReal r →
          ∃ j, riemannianEDistOf (I := I) (X.obj i).metric y (c j) < ε := by
  classical
  let J := {i : ℕ | HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R 0 K}
  let (i : J) : TopologicalSpace (X.obj i.1).M := (X.obj i.1).topology
  let (i : J) : ChartedSpace H (X.obj i.1).M := (X.obj i.1).charted
  let (i : J) : IsManifold I ∞ (X.obj i.1).M := (X.obj i.1).smooth
  let (i : J) : IsManifold I 1 (X.obj i.1).M :=
    IsManifold.of_le (I := I) (M := (X.obj i.1).M) (n := ∞) (by decide)
  let (i : J) : SigmaCompactSpace (X.obj i.1).M := (X.obj i.1).sigmaCompact
  let (i : J) : T2Space (X.obj i.1).M := (X.obj i.1).t2
  let (i : J) : T2Space (TangentBundle I (X.obj i.1).M) := (X.obj i.1).t2TangentBundle
  let (i : J) : RiemannianBundle (fun y : (X.obj i.1).M => TangentSpace I y) :=
    (X.obj i.1).riemBundle (I := I)
  let (i : J) : (y : (X.obj i.1).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (X.obj i.1).riemInner (I := I)
  let (i : J) : IsContinuousRiemannianBundle E (fun y : (X.obj i.1).M => TangentSpace I y) :=
    (X.obj i.1).riemBundle_cont (I := I)
  let (i : J) : EMetricSpace (X.obj i.1).M := (X.obj i.1).emetricSpace (I := I)
  let (i : J) : IsRiemannianManifold I (X.obj i.1).M := ⟨fun _ _ => rfl⟩
  let (i : J) : CompleteSpace (X.obj i.1).M :=
    MetricComplete.complete (I := I) (X.obj i.1) (hcomplete.complete i.1)
  let hEnorm (i : J) : ∀ (y : (X.obj i.1).M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i.1).metric.inner y v v)) := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj i.1).metric y v
  let f (i : J) : E → (X.obj i.1).M :=
    intrinsicFramedExp (I := I) (X.obj i.1).metric (hEnorm i) (X.obj i.1).basepoint
  let A : ℝ := Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2
  let B : ℝ := 1 + gronwallBound 0 (max A 1) A 1
  let C : ℝ≥0 := ⟨max B 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hf : ∀ i : J, LipschitzOnWith C (f i) (Metric.closedBall (0 : E) r) := by
    intro i
    apply lipschitzOnWith_intrinsicFramedExp_of_metric_bound (X.obj i.1).metric (hEnorm i)
      (X.obj i.1).basepoint
    intro z hz v
    have hRm : ∀ y : (X.obj i.1).M,
        riemannianEDist I (X.obj i.1).basepoint y < ENNReal.ofReal R →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj i.1).metric y 4
          (Geometry.Curvature.metricRm04At (I := I) (X.obj i.1).metric y)) ≤ K := by
      intro y hy
      apply (normSq0S_metricRm04At_le_curvDerivNorm (I := I) (X.obj i.1).metric y).trans
      apply i.2 y
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i.1)]
      simpa only [IsRiemannianManifold.out (I := I)] using hy.le
    exact (intrinsicFrameMetric_sqrt_le_of_local_curvature (X.obj i.1).metric (hEnorm i)
      (X.obj i.1).basepoint hr hrR hK hRm
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) v).trans
      (mul_le_mul_of_nonneg_right (le_max_left B 1) (norm_nonneg v))
  obtain ⟨N, d, hd, hcover⟩ := EMetric.TotallyBounded.exists_uniform_finite_image_cover
    (isCompact_closedBall (0 : E) r).totallyBounded f C hf hε
  have himage (i : J) : f i '' Metric.closedBall (0 : E) r =
      {y : (X.obj i.1).M | riemannianEDistOf (I := I) (X.obj i.1).metric
        (X.obj i.1).basepoint y ≤ ENNReal.ofReal r} := by
    rw [show f i = intrinsicFramedExp (I := I) (X.obj i.1).metric (hEnorm i)
      (X.obj i.1).basepoint from rfl]
    rw [intrinsicFramedExp_image_closedBall (I := I) (X.obj i.1).metric (hEnorm i)
      (X.obj i.1).basepoint hr]
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i.1),
      IsRiemannianManifold.out (I := I)]
  refine ⟨N, hcurv.mono fun i hi => ?_⟩
  let j : J := ⟨i, hi⟩
  let : TopologicalSpace (X.obj i).M := (X.obj i).topology
  let : ChartedSpace H (X.obj i).M := (X.obj i).charted
  let : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
  let : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
  let : T2Space (X.obj i).M := (X.obj i).t2
  let : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
  refine ⟨fun a => f j (d a), ?_, ?_⟩
  · intro a
    have hm : f j (d a) ∈ f j '' Metric.closedBall (0 : E) r := ⟨d a, hd a, rfl⟩
    rw [himage j] at hm
    exact hm
  · intro y hy
    have hyimage : y ∈ f j '' Metric.closedBall (0 : E) r := by rw [himage j]; exact hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover j hyimage)
    refine ⟨a, ?_⟩
    rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)]
    exact Metric.mem_eball.mp ha
end DifferentialGeometry.CheegerGromovCompactness

end

end
