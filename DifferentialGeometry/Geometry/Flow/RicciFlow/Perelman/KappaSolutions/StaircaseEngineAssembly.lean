import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalIntrinsicFrameBall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.FramedBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BallGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.NormalCharts

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_staircaseFramedSourceRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∃ r : ℝ, 0 < r ∧
      ∀ (hEnorm : ∀ (y : Y.M) (v : TangentSpace I y),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v))),
        Metric.ball (0 : E) r ⊆
          (intrinsicFrameDiffeo (I := I) Y.metric hEnorm x).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let hEnorm₀ : ∀ (y : Y.M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v)) := by
    intro y v
    with_unfolding_all
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric y v
  refine ⟨min (metricCoerciveExpRadius (I := I) Y.metric x)
      (intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x) / 2, ?_, ?_⟩
  · exact div_pos (lt_min (metricCoerciveExpRadius_pos (I := I) Y.metric x)
      (intrinsicFrameRadius_pos (I := I) Y.metric hEnorm₀ x)) (by norm_num)
  · intro hEnorm
    have hle₁ : min (metricCoerciveExpRadius (I := I) Y.metric x)
        (intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x) / 2 ≤
        metricCoerciveExpRadius (I := I) Y.metric x := by
      linarith [min_le_left (metricCoerciveExpRadius (I := I) Y.metric x)
        (intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x),
        metricCoerciveExpRadius_pos (I := I) Y.metric x,
        intrinsicFrameRadius_pos (I := I) Y.metric hEnorm₀ x]
    have hle₂ : min (metricCoerciveExpRadius (I := I) Y.metric x)
        (intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x) / 2 ≤
        intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x := by
      linarith [min_le_right (metricCoerciveExpRadius (I := I) Y.metric x)
        (intrinsicFrameRadius (I := I) Y.metric hEnorm₀ x),
        metricCoerciveExpRadius_pos (I := I) Y.metric x,
        intrinsicFrameRadius_pos (I := I) Y.metric hEnorm₀ x]
    rw [intrinsicFrameDiffeo_source]
    exact fun z hz =>
      ⟨(Metric.ball_subset_ball hle₁).trans
          (framedExp_ball_subset_source (I := I) Y x) hz,
        Metric.ball_subset_ball hle₂ hz⟩

noncomputable def staircaseFramedSourceRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y) (x : Y.M) : ℝ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact Classical.choose (show ∃ r : ℝ, 0 < r ∧
      ∀ (hEnorm : ∀ (y : Y.M) (v : TangentSpace I y),
          ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v))),
        Metric.ball (0 : E) r ⊆
          (intrinsicFrameDiffeo (I := I) Y.metric hEnorm x).source from
    exists_staircaseFramedSourceRadius (I := I) Y hcomplete x)

theorem staircaseFramedSourceRadius_pos
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y) (x : Y.M) :
    0 < staircaseFramedSourceRadius (I := I) Y hcomplete x := by
  rw [staircaseFramedSourceRadius]
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact (Classical.choose_spec (exists_staircaseFramedSourceRadius (I := I) Y
    hcomplete x)).1

theorem ball_subset_staircaseFramedSourceRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∀ (hEnorm : ∀ (y : Y.M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v))),
      Metric.ball (0 : E) (staircaseFramedSourceRadius (I := I) Y hcomplete x) ⊆
        (intrinsicFrameDiffeo (I := I) Y.metric hEnorm x).source := by
  intro hEnorm
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  rw [staircaseFramedSourceRadius]
  exact (Classical.choose_spec (exists_staircaseFramedSourceRadius (I := I) Y
    hcomplete x)).2 hEnorm

theorem eqOn_framedCoordMetric_intrinsicFrameMetric_staircaseFramedSourceRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∀ (hEnorm : ∀ (y : Y.M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v))),
      Set.EqOn (framedCoordMetric (I := I) Y x)
        (intrinsicFrameMetric (I := I) Y.metric hEnorm x)
        (Metric.ball (0 : E) (staircaseFramedSourceRadius (I := I) Y hcomplete x)) := by
  intro hEnorm
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact fun z hz =>
    framedCoordMetric_eq_intrinsicFrameMetric (I := I) Y hcomplete x hEnorm z
      (ball_subset_staircaseFramedSourceRadius (I := I) Y hcomplete x hEnorm hz)

theorem exists_subseq_seqBallFramedCoordMetricBounds_of_local_jets
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
    {A : ℝ} (hA : 0 < A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) (X.subseq φ)) := by
  classical
  obtain ⟨ρ₁, hρ₁, hρ₁A, hchart⟩ :=
    exists_uniform_intrinsicBallChart_on_ball_of_local_jets (I := I) X
      hcomplete hconn hinj hjets A hA
  obtain ⟨ρ₂, hρ₂, hρ₂A, C, hCnonneg, hCev⟩ :=
    exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_on_ball_of_local_jets
      (I := I) X hcomplete hconn hinj hjets A hA
  let ρ : ℝ := min ρ₁ ρ₂
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  have hρA : ρ ≤ A / 2 := (min_le_left _ _).trans hρ₁A
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hchart
  choose Nj hNj using fun p : ℕ => Filter.eventually_atTop.mp (hCev p)
  let N : ℕ → ℕ := fun p => max (Nj p) N₁
  let Mb : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup N
  let φ : ℕ → ℕ := fun j => j + Mb j + 1
  have hMb_mono : ∀ j : ℕ, Mb j ≤ Mb (j + 1) := by
    intro j
    refine Finset.sup_le_iff.mpr fun p hp => ?_
    exact Finset.le_sup (f := N)
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hp)))
  have hφ : StrictMono φ := by
    intro a b hab
    have hle : Mb a ≤ Mb b := by
      refine Finset.sup_le_iff.mpr fun p hp => ?_
      exact Finset.le_sup (f := N) (Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hp) (Nat.succ_le_succ hab.le)))
    simp only [φ]
    omega
  have hNφ : ∀ (p j : ℕ), p ≤ j → N p ≤ φ j := by
    intro p j hpj
    have h1 : N p ≤ Mb j :=
      Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_of_le hpj))
    simp only [φ]
    omega
  refine ⟨φ, hφ, ⟨{
    A := A / 2
    A_pos := by linarith
    metricC := fun _ p => C p
    metricC_nonneg := fun _ p => hCnonneg p
    radius := fun k x =>
      min ρ (staircaseFramedSourceRadius (I := I) (X.obj (φ k))
        (hcomplete.complete (φ k)) x)
    radius_pos := ?_
    radius_le_A := ?_
    metric_equiv := ?_
    metric_deriv := ?_ }⟩⟩
  · intro k x
    exact lt_min hρpos (staircaseFramedSourceRadius_pos (I := I) (X.obj (φ k))
      (hcomplete.complete (φ k)) x)
  · intro k x
    exact (min_le_left _ _).trans hρA
  · intro k x hx
    have hx' : (letI : TopologicalSpace (X.obj (φ k)).M := (X.obj (φ k)).topology
      letI : ChartedSpace H (X.obj (φ k)).M := (X.obj (φ k)).charted
      letI : IsManifold I ∞ (X.obj (φ k)).M := (X.obj (φ k)).smooth
      riemannianEDistOf (I := I) (X.obj (φ k)).metric (X.obj (φ k)).basepoint x ≤
        ENNReal.ofReal (A / 2)) := hx
    let : TopologicalSpace (X.obj (φ k)).M := (X.obj (φ k)).topology
    let : ChartedSpace H (X.obj (φ k)).M := (X.obj (φ k)).charted
    let : IsManifold I ∞ (X.obj (φ k)).M := (X.obj (φ k)).smooth
    let : IsManifold I 1 (X.obj (φ k)).M :=
      IsManifold.of_le (I := I) (M := (X.obj (φ k)).M) (n := ∞) (by decide)
    let : SigmaCompactSpace (X.obj (φ k)).M := (X.obj (φ k)).sigmaCompact
    let : T2Space (X.obj (φ k)).M := (X.obj (φ k)).t2
    let : T2Space (TangentBundle I (X.obj (φ k)).M) :=
      (X.obj (φ k)).t2TangentBundle
    let : RiemannianBundle (fun y : (X.obj (φ k)).M => TangentSpace I y) :=
      (X.obj (φ k)).riemBundle (I := I)
    let : (y : (X.obj (φ k)).M) → InnerProductSpace ℝ (TangentSpace I y) :=
      (X.obj (φ k)).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X.obj (φ k)).M => TangentSpace I y) :=
      (X.obj (φ k)).riemBundle_cont (I := I)
    let : EMetricSpace (X.obj (φ k)).M := (X.obj (φ k)).emetricSpace (I := I)
    let : IsRiemannianManifold I (X.obj (φ k)).M := ⟨fun _ _ => rfl⟩
    let : CompleteSpace (X.obj (φ k)).M :=
      MetricComplete.complete (I := I) (X.obj (φ k)) (hcomplete.complete (φ k))
    let hEnorm : ∀ (y : (X.obj (φ k)).M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt ((X.obj (φ k)).metric.inner y v v)) := by
      intro y v
      with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I)
        (X.obj (φ k)).metric y v
    intro z hz v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        framedCoordMetric (I := I) (X.obj (φ k)) x z v v ∧
      framedCoordMetric (I := I) (X.obj (φ k)) x z v v ≤ 2 * ‖v‖ ^ 2
    have hzρ₁ : z ∈ Metric.ball (0 : E) ρ₁ :=
      Metric.ball_subset_ball (min_le_left _ _)
        (Metric.ball_subset_ball (min_le_left _ _) hz)
    have heq : Set.EqOn (framedCoordMetric (I := I) (X.obj (φ k)) x)
        (intrinsicFrameMetric (I := I) (X.obj (φ k)).metric hEnorm x)
        (Metric.ball (0 : E) (min ρ (staircaseFramedSourceRadius (I := I)
          (X.obj (φ k)) (hcomplete.complete (φ k)) x))) :=
      (eqOn_framedCoordMetric_intrinsicFrameMetric_staircaseFramedSourceRadius
        (I := I) (X.obj (φ k)) (hcomplete.complete (φ k)) x hEnorm).mono
        (Metric.ball_subset_ball (min_le_right _ _))
    rw [heq hz]
    have hN₁φ : N₁ ≤ φ k := by
      have h1 : N₁ ≤ N 0 := le_max_right (Nj 0) N₁
      have h2 : N 0 ≤ Mb k :=
        Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.succ_pos k))
      have h3 : Mb k ≤ φ k := by simp only [φ]; omega
      omega
    exact (hN₁ (φ k) hN₁φ x hx').2 z hzρ₁ v
  · intro n p j hnj x hx
    let : TopologicalSpace (X.obj (φ j)).M := (X.obj (φ j)).topology
    let : ChartedSpace H (X.obj (φ j)).M := (X.obj (φ j)).charted
    let : IsManifold I ∞ (X.obj (φ j)).M := (X.obj (φ j)).smooth
    let : IsManifold I 1 (X.obj (φ j)).M :=
      IsManifold.of_le (I := I) (M := (X.obj (φ j)).M) (n := ∞) (by decide)
    let : SigmaCompactSpace (X.obj (φ j)).M := (X.obj (φ j)).sigmaCompact
    let : T2Space (X.obj (φ j)).M := (X.obj (φ j)).t2
    let : T2Space (TangentBundle I (X.obj (φ j)).M) :=
      (X.obj (φ j)).t2TangentBundle
    let : RiemannianBundle (fun y : (X.obj (φ j)).M => TangentSpace I y) :=
      (X.obj (φ j)).riemBundle (I := I)
    let : (y : (X.obj (φ j)).M) → InnerProductSpace ℝ (TangentSpace I y) :=
      (X.obj (φ j)).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X.obj (φ j)).M => TangentSpace I y) :=
      (X.obj (φ j)).riemBundle_cont (I := I)
    let : EMetricSpace (X.obj (φ j)).M := (X.obj (φ j)).emetricSpace (I := I)
    let : IsRiemannianManifold I (X.obj (φ j)).M := ⟨fun _ _ => rfl⟩
    let : CompleteSpace (X.obj (φ j)).M :=
      MetricComplete.complete (I := I) (X.obj (φ j)) (hcomplete.complete (φ j))
    let hEnorm : ∀ (y : (X.obj (φ j)).M) (v : TangentSpace I y),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt ((X.obj (φ j)).metric.inner y v v)) := by
      intro y v
      with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I)
        (X.obj (φ j)).metric y v
    have hpj : p ≤ j := le_trans (Nat.le_add_left p n) hnj
    have hx' : riemannianEDistOf (I := I) (X.obj (φ j)).metric
        (X.obj (φ j)).basepoint x ≤ ENNReal.ofReal (A / 2) :=
      hx.trans (ENNReal.ofReal_le_ofReal (min_le_left (A / 2) (n : ℝ)))
    refine FramedCoordMetricDerivBound.of_eqOn (I := I) (X.obj (φ j)) x
      (U := Metric.ball (0 : E) (min ρ (staircaseFramedSourceRadius (I := I)
        (X.obj (φ j)) (hcomplete.complete (φ j)) x)))
      (f := intrinsicFrameMetric (I := I) (X.obj (φ j)).metric hEnorm x)
      (p := p) (C := C p) Metric.isOpen_ball ?_ ?_
    · exact (eqOn_framedCoordMetric_intrinsicFrameMetric_staircaseFramedSourceRadius
        (I := I) (X.obj (φ j)) (hcomplete.complete (φ j)) x hEnorm).mono
        (Metric.ball_subset_ball (min_le_right _ _))
    · intro z hz
      exact hNj p (φ j) (le_trans (le_max_left (Nj p) N₁) (hNφ p j hpj)) x hx' z
        (Metric.ball_subset_ball (min_le_right ρ₁ ρ₂)
          (Metric.ball_subset_ball (min_le_left _ _) hz))

theorem exists_subseq_seqBallFramedCoordMetricBounds_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X)
    {A : ℝ} (hA : 0 < A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) (X.subseq φ)) :=
  exists_subseq_seqBallFramedCoordMetricBounds_of_local_jets (I := I) X hcomplete hconn hinj
    (fun _A _hA p => ⟨hgeom.C p, hgeom.nonneg p,
      Filter.Eventually.of_forall fun i => fun x _hx => hgeom.bound i p x⟩) hA

theorem exists_subseq_seqBallFramedCoordMetricBounds_of_seqBallGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hball : SeqBallGeometry (I := I) X)
    {A : ℝ} (hA : 0 < A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) (X.subseq φ)) := by
  refine exists_subseq_seqBallFramedCoordMetricBounds_of_local_jets (I := I) X
    hcomplete hconn hinj ?_ hA
  intro A' hA' p
  obtain ⟨n, hn⟩ := exists_nat_ge A'
  refine ⟨hball.C n p, hball.nonneg n p,
    (Filter.eventually_ge_atTop (n + p)).mono fun i hi => fun x hx =>
      hball.bound n p i hi x (hx.trans (ENNReal.ofReal_le_ofReal hn))⟩

def StaircaseEngineFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : ℕ,
    let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  Nonempty (SeqBallFramedCoordMetricBounds (I := I) Y) →
  ∃ C : CanonicalMetricCompactness (I := I) Y,
    @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology

theorem exists_local_pointed_metric_compactness_of_staircaseEngineFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
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
    (hfrontier : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseEngineFrontier (I := I) Y) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨φ, hφ, hb⟩ :=
    exists_subseq_seqBallFramedCoordMetricBounds_of_local_jets (I := I) X
      hcomplete hconnected hinj hjets (A := 1) one_pos
  obtain ⟨C, hCconn⟩ := hfrontier (X.subseq φ) (hcomplete.subseq φ)
    (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hb
  let C₀ : CanonicalMetricCompactness (I := I) X := C.ofSubsequence φ hφ
  refine ⟨C₀.compactness, C₀.domain_eq_canonical, C₀.reference_eq_limit, ?_⟩
  change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
  exact hCconn

theorem staircaseEngineFrontier_of_metricCompactSeedFrontier
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      SeqMetricComplete (I := I) Y →
      (∀ i : ℕ,
        let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
        ConnectedSpace (Y.obj i).M) →
      BaseInjBound (I := I) Y →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ b : MetricCompactSeed (I := I) (Y.subseq ψ),
          Nonempty (BoundedGeometryNormalChartData (I := I) (Y.subseq ψ) b.decay)) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseEngineFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj _hbounds
  obtain ⟨ψ, hψ, b, hd⟩ := hseed Y hcomplete hconnected hinj
  let C : CanonicalMetricCompactness (I := I) (Y.subseq ψ) :=
    b.higherRegularityCanonicalMetricCompactness (Classical.choice hd)
      (hcomplete.subseq ψ) (PointedRiemannianSeq.connected_subseq hconnected ψ)
  have hCconn : @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology :=
    b.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd)
      (hcomplete.subseq ψ) (PointedRiemannianSeq.connected_subseq hconnected ψ)
  exact ⟨C.ofSubsequence ψ hψ, by
    change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
    exact hCconn⟩

end CheegerGromovCompactness
end DifferentialGeometry
