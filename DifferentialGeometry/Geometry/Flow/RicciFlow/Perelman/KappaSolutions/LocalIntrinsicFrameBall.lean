import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.CenteredJetBounds

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

theorem exists_uniform_intrinsicBallChart_on_ball_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (A : ℝ) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ A / 2 ∧
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
        letI : ConnectedSpace (X.obj i).M := hconn i
        let hEnorm : ∀ (y : (X.obj i).M) (v : TangentSpace I y),
            ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i).metric.inner y v v)) := by
          intro y v
          with_unfolding_all
            exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
              (I := I) (X.obj i).metric y v
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal (A / 2) →
          Nonempty (IntrinsicBallChart (I := I) (X.obj i).metric hEnorm x ρ) ∧
          (∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
                intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ∧
              intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x z v v ≤
                2 * ‖v‖ ^ 2) := by
  classical
  obtain ⟨C₀, hC₀, hjets₀⟩ := hjets A hA 0
  obtain ⟨ρ₁, hρ₁, hinj₁⟩ :=
    exists_uniform_injectivity_radius_on_ball_of_local_jets
      (I := I) X hcomplete hconn hinj hjets A hA
  have hA2 : 0 < A / 2 := by linarith
  obtain ⟨rCtrl, hrCtrl, hrCtrlLe, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) (R := A / 2) (K := C₀) hA2 hC₀
  let ρ : ℝ := min rCtrl ρ₁ / 2
  have hρmin : 0 < min rCtrl ρ₁ := lt_min hrCtrl hρ₁
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    linarith
  have hρ_lt : ρ < ρ₁ := by
    dsimp only [ρ]
    have h1 : min rCtrl ρ₁ ≤ ρ₁ := min_le_right _ _
    linarith
  have hρ_le : ρ ≤ rCtrl := by
    dsimp only [ρ]
    have h1 : min rCtrl ρ₁ ≤ rCtrl := min_le_left _ _
    linarith
  have hρ_le_A2 : ρ ≤ A / 2 := hρ_le.trans hrCtrlLe
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hjets₀
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hinj₁
  refine ⟨ρ, hρ, hρ_le_A2, Filter.eventually_atTop.mpr ⟨max N₀ N₁, fun i hi => ?_⟩⟩
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
  let : ConnectedSpace (X.obj i).M := hconn i
  intro hEnorm x hx
  have hx' : edist (X.obj i).basepoint x ≤ ENNReal.ofReal (A / 2) := by
    rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)] at hx
    exact hx
  have hRmBall : ∀ y : (X.obj i).M,
      riemannianEDist I x y < ENNReal.ofReal (A / 2) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj i).metric y 4
        (metricRm04At (I := I) (M := (X.obj i).M) (X.obj i).metric y)) ≤ C₀ := by
    intro y hy
    have hyE : edist x y < ENNReal.ofReal (A / 2) := by
      rw [← IsRiemannianManifold.out (I := I)] at hy
      exact hy
    have hbase : riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint y ≤
        ENNReal.ofReal A := by
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X.obj i)]
      calc edist (X.obj i).basepoint y
          ≤ edist (X.obj i).basepoint x + edist x y := edist_triangle _ _ _
        _ ≤ ENNReal.ofReal (A / 2) + ENNReal.ofReal (A / 2) := add_le_add hx' hyE.le
        _ = ENNReal.ofReal A := by
            rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
            norm_num
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
      hEnorm x hC₀ hRmBall (hzr.trans_le hrCtrlLe)
      (herror ‖z‖ (norm_nonneg _) hzr.le) v
  have hlocal : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) rCtrl) :=
    intrinsicFrame_localOn_of_local_curvature (I := I) (X.obj i).metric hEnorm x
      hC₀ hrCtrlLe hRmBall (fun t ht htr => herror t ht htr)
  have hlocρ : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) ρ) :=
    fun z => hlocal ⟨z.1, Metric.ball_subset_ball hρ_le z.2⟩
  have hinjρ : Set.InjOn (intrinsicFramedExp (I := I) (X.obj i).metric hEnorm x)
      (Metric.ball (0 : E) ρ) :=
    (hN₁ i (le_trans (le_max_right _ _) hi) x
      (hx'.trans (ENNReal.ofReal_le_ofReal (by linarith)))).injOn_ball
      (hcomplete.complete i) hρ_lt
  exact ⟨⟨Classical.choice (exists_intrinsic_ball_chart (I := I) (X.obj i).metric
      hEnorm x hlocρ hinjρ)⟩,
    fun z hz v => hmetric z (Metric.ball_subset_ball hρ_le hz) v⟩

theorem exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_on_ball_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (A : ℝ) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ A / 2 ∧ ∃ C : ℕ → ℝ, (∀ p : ℕ, 0 ≤ C p) ∧
      ∀ p : ℕ, ∀ᶠ i in atTop,
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
        letI : ConnectedSpace (X.obj i).M := hconn i
        let hEnorm : ∀ (y : (X.obj i).M) (v : TangentSpace I y),
            ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i).metric.inner y v v)) := by
          intro y v
          with_unfolding_all
            exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
              (I := I) (X.obj i).metric y v
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal (A / 2) →
          ∀ z ∈ Metric.ball (0 : E) ρ,
            ‖iteratedFDeriv Real p
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z‖ ≤ C p := by
  classical
  obtain ⟨ρ, hρ, hρA, hchart⟩ :=
    exists_uniform_intrinsicBallChart_on_ball_of_local_jets
      (I := I) X hcomplete hconn hinj hjets A hA
  have hjet : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
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
        letI : CompleteSpace (X.obj i).M :=
          MetricComplete.complete (I := I) (X.obj i) (hcomplete.complete i)
        letI : ConnectedSpace (X.obj i).M := hconn i
        let hEnorm : ∀ (y : (X.obj i).M) (v : TangentSpace I y),
            ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj i).metric.inner y v v)) := by
          intro y v
          with_unfolding_all
            exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
              (I := I) (X.obj i).metric y v
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal (A / 2) →
          ∀ z : E, ‖z‖ ≤ ρ →
            ContDiffAt Real ∞
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z →
            ‖iteratedFDeriv Real p
              (intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x) z‖ ≤ C :=
    fun p => exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_of_edist_le_of_curvDerivNorm_eventually
      (I := I) X hcomplete hconn hjets A hA p (U := ρ) hρA
  choose C hCnonneg hCev using hjet
  refine ⟨ρ, hρ, hρA, C, hCnonneg, fun p => ?_⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hchart
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hCev p)
  refine Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun i hi => ?_⟩
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
  let : ConnectedSpace (X.obj i).M := hconn i
  intro hEnorm x hx z hz
  have hc : IntrinsicBallChart (I := I) (X.obj i).metric hEnorm x ρ :=
    Classical.choice (hN₁ i (le_trans (le_max_left _ _) hi) x hx).1
  have hzball : z ∈ Metric.ball (0 : E) ρ := hz
  have hle : ‖z‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hzball)
  exact hN₂ i (le_trans (le_max_right _ _) hi) x hx z hle
    (hc.contDiffAt_intrinsicFrameMetric (I := I) (X.obj i).metric hEnorm x hρ hzball)

end CheegerGromovCompactness
end DifferentialGeometry

end
