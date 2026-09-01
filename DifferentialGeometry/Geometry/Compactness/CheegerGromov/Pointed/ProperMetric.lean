import Mathlib.Topology.MetricSpace.ProperSpace
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

structure ProperMetricOn {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  ms : MetricSpace Y.M
  realizes : ∀ x y : Y.M,
    (letI : EMetricSpace Y.M := Y.emetricSpace
     edist x y) =
    ENNReal.ofReal (letI : MetricSpace Y.M := ms
      dist x y)
  proper : letI : MetricSpace Y.M := ms
    ProperSpace Y.M
  hint : letI : MetricSpace Y.M := ms
    ∀ p : Y.M, ∀ t : ℝ, 0 ≤ t → t ≤ dist p Y.basepoint →
      ∃ q : Y.M, dist q Y.basepoint = t

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.top_eq {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = Y.topology := by
  have hem :
      (letI : MetricSpace Y.M := P.ms
       (inferInstance : PseudoEMetricSpace Y.M)) =
        (letI : EMetricSpace Y.M := Y.emetricSpace
         (inferInstance : PseudoEMetricSpace Y.M)) := by
    apply PseudoEMetricSpace.ext
    ext x y
    change (letI : MetricSpace Y.M := P.ms; edist x y) =
      (letI : EMetricSpace Y.M := Y.emetricSpace; edist x y)
    rw [P.realizes x y]
    have hdist :
        (letI : MetricSpace Y.M := P.ms
         edist x y) =
          ENNReal.ofReal (letI : MetricSpace Y.M := P.ms
            dist x y) := by
      let : MetricSpace Y.M := P.ms
      exact edist_dist x y
    exact hdist
  have htop :
      (letI : MetricSpace Y.M := P.ms
       (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) =
        (letI : EMetricSpace Y.M := Y.emetricSpace
         (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) := by
    simpa using
      congrArg (fun m : PseudoEMetricSpace Y.M => m.toUniformSpace.toTopologicalSpace) hem
  have hcan :
      (letI : EMetricSpace Y.M := Y.emetricSpace
       (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) =
        Y.topology := by
    rfl
  change P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = Y.topology
  rw [htop, hcan]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.isRiemannianManifold {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
    letI : MetricSpace Y.M := P.ms
    IsRiemannianManifold I Y.M := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
  let : MetricSpace Y.M := P.ms
  refine ⟨fun x y => ?_⟩
  have hreal := P.realizes x y
  rw [edist_dist, ← hreal]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_proper_metric_on {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hc : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M) :
    Nonempty (ProperMetricOn (I := I) Y) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  have : T3Space Y.M := inferInstance
  have : ConnectedSpace Y.M := hconn
  let rb : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hCont := Y.riemBundle_cont (I := I)
  have hcomplete :
      (letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
       CompleteSpace Y.M) := by
    simpa [MetricComplete] using hc
  let ms := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace
    (I := I) (M := Y.M)
  have hreal : ∀ x y : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       edist x y) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
        dist x y) := by
    intro x y
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes
      (I := I) (M := Y.M) x y
    simpa [PointedRiemannianManifold.emetricSpace, ms] using h
  have hproper :
      letI : MetricSpace Y.M := ms
      ProperSpace Y.M := by
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric
      (I := I) (M := Y.M) hcomplete Y.metric (by
        intro x v
        exact
          (DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle
            (I := I) Y.metric) x v)
    simpa [ms] using h
  have hhint :
      letI : MetricSpace Y.M := ms
      ∀ p : Y.M, ∀ t : ℝ, 0 ≤ t → t ≤ dist p Y.basepoint →
        ∃ q : Y.M, dist q Y.basepoint = t := by
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric
      (I := I) (M := Y.M) hcomplete Y.metric (by
        intro x v
        exact
          (DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle
            (I := I) Y.metric) x v) Y.basepoint
    simpa [ms] using h
  exact ⟨⟨ms, hreal, hproper, hhint⟩⟩

omit [CompleteSpace E] in
noncomputable def properMetricOn {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hc : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M) :
    ProperMetricOn (I := I) Y :=
  Classical.choice (exists_proper_metric_on (I := I) Y hc hconn)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.isOpen_ball {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @IsOpen Y.M Y.topology
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  have hb :
      @IsOpen Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace Y.M := P.ms
         Metric.ball x r) := by
    let : MetricSpace Y.M := P.ms
    exact Metric.isOpen_ball
  rw [P.top_eq Y] at hb
  exact hb

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.mem_ball_self {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    x ∈
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  let : MetricSpace Y.M := P.ms
  exact Metric.mem_ball_self hr

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.ball_nonempty {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) :=
  ⟨⟨x, P.mem_ball_self Y x hr⟩⟩

def ProperMetricOn.openBall {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @TopologicalSpace.Opens Y.M Y.topology :=
  letI : TopologicalSpace Y.M := Y.topology
  ⟨(letI : MetricSpace Y.M := P.ms
    Metric.ball x r), P.isOpen_ball Y x r⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.openBall_nonempty {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty (P.openBall Y x r) := by
  let : TopologicalSpace Y.M := Y.topology
  exact P.ball_nonempty Y x hr

end HCGCompactness
end DifferentialGeometry
