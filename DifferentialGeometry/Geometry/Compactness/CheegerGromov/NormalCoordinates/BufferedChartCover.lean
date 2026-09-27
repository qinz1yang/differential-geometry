import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalConjugateRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.CenteredJetBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.FiniteBallCover
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_uniform_intrinsicBallChart_on_buffered_ball_of_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    {R r K η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hK : 0 ≤ K) (hη : 0 < η)
    (hcurv : ∀ᶠ i in atTop,
      HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R 0 K)
    (hinj : ∀ᶠ i in atTop,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
      letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
      ∀ x : (X.obj i).M,
        riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
          ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj i) x η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R - r ∧
      ∀ᶠ i in atTop,
        letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
        letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
        letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        letI : IsManifold I 1 (X.obj i).M :=
          IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
        letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        letI : T2Space (X.obj i).M := (X.obj i).t2
        letI : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
        letI : RiemannianBundle (fun y : (X.obj i).M => TangentSpace I y) :=
          (X.obj i).riemBundle (I := I)
        letI : (y : (X.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
          (X.obj i).riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : (X.obj i).M => TangentSpace I y) :=
          (X.obj i).riemBundle_cont (I := I)
        letI : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
        letI : IsRiemannianManifold I (X.obj i).M := ⟨fun _ _ => rfl⟩
        letI : CompleteSpace (X.obj i).M :=
          MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
        let hEnorm : ∀ (y : (X.obj i).M) (v : TangentSpace I y),
            ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i).metric.inner y v v)) := by
          intro y v
          with_unfolding_all
            exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
              (I := I) (X.obj i).metric y v
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal r →
          Nonempty (IntrinsicBallChart (I := I) (X.obj i).metric hEnorm x ρ) ∧
          (∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
                intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ∧
              intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ≤
                2 * ‖v‖ ^ 2) := by
  classical
  have hbuffer : 0 < R - r := sub_pos.mpr hrR
  obtain ⟨rCtrl, hrCtrl, hrCtrlLe, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) (R := R - r) (K := K) hbuffer hK
  let ρ : ℝ := min rCtrl η / 2
  have hρmin : 0 < min rCtrl η := lt_min hrCtrl hη
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    linarith
  have hρ_lt : ρ < η := by
    dsimp only [ρ]
    have h1 : min rCtrl η ≤ η := min_le_right _ _
    linarith
  have hρ_le : ρ ≤ rCtrl := by
    dsimp only [ρ]
    have h1 : min rCtrl η ≤ rCtrl := min_le_left _ _
    linarith
  have hρ_le_buffer : ρ ≤ R - r := hρ_le.trans hrCtrlLe
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcurv
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hinj
  refine ⟨ρ, hρ, hρ_le_buffer, Filter.eventually_atTop.mpr ⟨max N₀ N₁, fun i hi => ?_⟩⟩
  let : TopologicalSpace (X.obj i).M := (X.obj i).topology
  let : ChartedSpace H (X.obj i).M := (X.obj i).charted
  let : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
  let : IsManifold I 1 (X.obj i).M :=
    IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
  let : T2Space (X.obj i).M := (X.obj i).t2
  let : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
  let : RiemannianBundle (fun y : (X.obj i).M => TangentSpace I y) :=
    (X.obj i).riemBundle (I := I)
  let : (y : (X.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (X.obj i).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj i).M => TangentSpace I y) :=
    (X.obj i).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
  let : IsRiemannianManifold I (X.obj i).M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace (X.obj i).M :=
    MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
  intro hEnorm x hx
  have hx' : edist (X.obj i).basepoint x ≤ ENNReal.ofReal r := by
    rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)] at hx
    exact hx
  have hRmBall : ∀ y : (X.obj i).M,
      riemannianEDist I x y < ENNReal.ofReal (R - r) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj i).metric y 4
        (metricRm04At (I := I) (M := (X.obj i).M) (X.obj i).metric y)) ≤ K := by
    intro y hy
    have hyE : edist x y < ENNReal.ofReal (R - r) := by
      rw [← IsRiemannianManifold.out (I := I)] at hy
      exact hy
    have hbase : riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint y ≤
        ENNReal.ofReal R := by
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)]
      calc edist (X.obj i).basepoint y
          ≤ edist (X.obj i).basepoint x + edist x y := edist_triangle _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal (R - r) := add_le_add hx' hyE.le
        _ = ENNReal.ofReal R := by
            rw [← ENNReal.ofReal_add hr hbuffer.le]
            congr 1
            ring
    exact (normSq0S_metricRm04At_le_curvDerivNorm (I := I) (X.obj i).metric y).trans
      (hN₀ i (le_trans (le_max_left _ _) hi) y hbase)
  have hmetric : ∀ z ∈ Metric.ball (0 : E) rCtrl, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
          intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ∧
        intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2 := by
    intro z hz v
    have hzr : ‖z‖ < rCtrl := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact intrinsicFrameMetric_bounds_of_local_curvature (I := I) (X.obj i).metric
      hEnorm x hK hRmBall (hzr.trans_le hrCtrlLe)
      (herror ‖z‖ (norm_nonneg _) hzr.le) v
  have hlocal : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) rCtrl) :=
    intrinsicFrame_localOn_of_local_curvature (I := I) (X.obj i).metric hEnorm x
      hK hrCtrlLe hRmBall (fun t ht htr => herror t ht htr)
  have hlocρ : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) ρ) :=
    fun z => hlocal ⟨z.1, Metric.ball_subset_ball hρ_le z.2⟩
  have hinjρ : Set.InjOn (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) ρ) :=
    (hN₁ i (le_trans (le_max_right _ _) hi) x
      hx).injOn_ball
      (hcomplete.complete i) hρ_lt
  exact ⟨⟨Classical.choice (exists_intrinsic_ball_chart (I := I) (X.obj i).metric
      hEnorm x hlocρ hinjρ)⟩,
    fun z hz v => hmetric z (Metric.ball_subset_ball hρ_le hz) v⟩

end CheegerGromovCompactness
end DifferentialGeometry

end


end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_eventually_finite_pointed_intrinsicBallChart_cover_of_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    {R r K η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hK : 0 ≤ K) (hη : 0 < η)
    (hcurv : ∀ᶠ i in atTop,
      HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R 0 K)
    (hinj : ∀ᶠ i in atTop,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
      letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
      ∀ x : (X.obj i).M,
        riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
          ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj i) x η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R - r ∧ ∀ a : ℝ, 0 < a → a ≤ ρ → ∃ N : ℕ,
      ∀ᶠ i in atTop,
        letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
        letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
        letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        letI : IsManifold I 1 (X.obj i).M :=
          IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
        letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        letI : T2Space (X.obj i).M := (X.obj i).t2
        letI : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
        letI : RiemannianBundle (fun y : (X.obj i).M => TangentSpace I y) :=
          (X.obj i).riemBundle (I := I)
        letI : (y : (X.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
          (X.obj i).riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : (X.obj i).M => TangentSpace I y) :=
          (X.obj i).riemBundle_cont (I := I)
        letI : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
        letI : IsRiemannianManifold I (X.obj i).M := ⟨fun _ _ => rfl⟩
        letI : CompleteSpace (X.obj i).M :=
          MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
        let hEnorm : ∀ (y : (X.obj i).M) (v : TangentSpace I y),
            ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i).metric.inner y v v)) := by
          intro y v
          with_unfolding_all
            exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
              (I := I) (X.obj i).metric y v
        ∃ (c : Fin (N + 1) → (X.obj i).M)
          (charts : ∀ j, IntrinsicBallChart (I := I) (X.obj i).metric hEnorm (c j) ρ),
          c 0 = (X.obj i).basepoint ∧
          (∀ j, riemannianEDistOf (I := I) (X.obj i).metric
            (X.obj i).basepoint (c j) ≤ ENNReal.ofReal r) ∧
          (∀ j, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
                intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm (c j) z v v ∧
              intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm (c j) z v v ≤
                2 * ‖v‖ ^ 2) ∧
          ∀ y : (X.obj i).M,
            riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint y ≤
              ENNReal.ofReal r →
            ∃ j, y ∈ (charts j).hom '' Metric.ball (0 : E) a := by
  classical
  obtain ⟨ρ, hρ, hρR, hcharts⟩ :=
    exists_uniform_intrinsicBallChart_on_buffered_ball_of_curvature_injectivity
      X hcomplete hr hrR hK hη hcurv hinj
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro a ha haρ
  obtain ⟨N, hcenters⟩ := exists_eventually_finite_ball_cover_of_local_curvature
    X hcomplete hr hrR hK hcurv (ENNReal.ofReal_pos.mpr ha)
  refine ⟨N, ?_⟩
  filter_upwards [hcharts, hcenters] with i hcharti hcentersi
  let : TopologicalSpace (X.obj i).M := (X.obj i).topology
  let : ChartedSpace H (X.obj i).M := (X.obj i).charted
  let : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
  let : IsManifold I 1 (X.obj i).M :=
    IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
  let : T2Space (X.obj i).M := (X.obj i).t2
  let : T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle
  let : RiemannianBundle (fun y : (X.obj i).M => TangentSpace I y) :=
    (X.obj i).riemBundle (I := I)
  let : (y : (X.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (X.obj i).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj i).M => TangentSpace I y) :=
    (X.obj i).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj i).M := (X.obj i).emetricSpace (I := I)
  let : IsRiemannianManifold I (X.obj i).M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace (X.obj i).M :=
    MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
  intro hEnorm
  obtain ⟨c, hc, hcover⟩ := hcentersi
  let c' : Fin (N + 1) → (X.obj i).M := Fin.cases (X.obj i).basepoint c
  have hc' : ∀ j, riemannianEDistOf (I := I) (X.obj i).metric
      (X.obj i).basepoint (c' j) ≤ ENNReal.ofReal r := by
    intro j
    refine Fin.cases ?_ (fun j => hc j) j
    simp only [c', Fin.cases_zero, riemannianEDistOf_self]
    exact bot_le
  have hchart : ∀ j, Nonempty (IntrinsicBallChart (I := I) (X.obj i).metric hEnorm (c' j) ρ) :=
    fun j => (hcharti (c' j) (hc' j)).1
  let charts : ∀ j, IntrinsicBallChart (I := I) (X.obj i).metric hEnorm (c' j) ρ :=
    fun j => Classical.choice (hchart j)
  refine ⟨c', charts, rfl, hc', fun j => (hcharti (c' j) (hc' j)).2, ?_⟩
  intro y hy
  obtain ⟨j, hj⟩ := hcover y hy
  have hdist : riemannianEDist I (c' j.succ) y < ENNReal.ofReal a := by
    rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)] at hj
    rw [← IsRiemannianManifold.out (I := I), edist_comm]
    exact hj
  have hdistρ : riemannianEDist I (c' j.succ) y < ENNReal.ofReal ρ :=
    hdist.trans_le (ENNReal.ofReal_le_ofReal haρ)
  obtain ⟨hmem, hnorm⟩ := (charts j.succ).mem_target_and_norm_symm (I := I)
    (X.obj i).metric hEnorm (c' j.succ) hdistρ
  refine ⟨j.succ, (charts j.succ).hom.symm y, ?_, (charts j.succ).hom.right_inv hmem⟩
  rw [Metric.mem_ball, dist_zero_right, hnorm]
  exact (ENNReal.lt_ofReal_iff_toReal_lt
    (ne_of_lt (hdist.trans ENNReal.ofReal_lt_top))).mp hdist

end CheegerGromovCompactness
end DifferentialGeometry

end

end
