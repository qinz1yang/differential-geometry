import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Comparison.Volume.Packing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.BallMultiplicityBound
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem exists_small_ball_volume_bounds_of_bounded_geometry
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (hgeom : BoundedGeometry (I := I) Y)
    (p : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
      Y.metric.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      ⟨cg.toRiemannianMetric⟩
    letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
    letI : PseudoEMetricSpace Y.M := inferInstance
    letI : ConnectedSpace Y.M := hconn
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∃ C D Blo A δ : Real, 0 < C ∧ 0 < D ∧ 0 < Blo ∧ 0 < δ ∧
      ∀ {s : Real}, 0 < s → s < δ →
        let Rlo : Real := s / (2 * C)
        let Rup : Real := D * s
        let Bhi : Real :=
          max
            (A + gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) * A) 1)
            0
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rlo ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ∧
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ≤
          ENNReal.ofReal
            (Real.sqrt (((Module.finrank Real E).factorial : Real) *
              (Bhi * Bhi) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rup ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
    Y.metric.toContinuousRiemannianMetric
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
  let : PseudoEMetricSpace Y.M := inferInstance
  let : ConnectedSpace Y.M := hconn
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hEnorm := fun x v =>
    (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) Y.metric x v)
  obtain ⟨C, D, Blo, A, hC, hD, hBlo, hvol⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_pairR_bound
      (I := I) (M := Y.M) Y.metric hEnorm p
  obtain ⟨δ, hδ, hsmall⟩ :=
    hvol (Rm := hgeom.C 0) (hgeom.nonneg 0)
      (rm04Bound_of_geom (I := I) hgeom)
  exact ⟨C, D, Blo, A, δ, hC, hD, hBlo, hδ, hsmall⟩

theorem exists_small_ball_volume_bounds_of_sequence_bounded_geometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (k : Nat) (p : (X.obj k).M) :
    let Y := X.obj k
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
      Y.metric.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      ⟨cg.toRiemannianMetric⟩
    letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
    letI : PseudoEMetricSpace Y.M := inferInstance
    letI : ConnectedSpace Y.M := hconn k
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y (hcomplete.complete k)
    ∃ C D Blo A δ : Real, 0 < C ∧ 0 < D ∧ 0 < Blo ∧ 0 < δ ∧
      ∀ {s : Real}, 0 < s → s < δ →
        let Rlo : Real := s / (2 * C)
        let Rup : Real := D * s
        let Bhi : Real :=
          max
            (A + gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) * A) 1)
            0
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rlo ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ∧
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ≤
          ENNReal.ofReal
            (Real.sqrt (((Module.finrank Real E).factorial : Real) *
              (Bhi * Bhi) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rup ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  let Y := X.obj k
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
    Y.metric.toContinuousRiemannianMetric
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
  let : PseudoEMetricSpace Y.M := inferInstance
  let : ConnectedSpace Y.M := hconn k
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y (hcomplete.complete k)
  let hgeom_k : BoundedGeometry (I := I) Y := {
    C := hgeom.C
    nonneg := hgeom.nonneg
    bound := hgeom.bound k }
  obtain ⟨C0, D, Blo, A, δ, hC0, hD, hBlo, hδ, hsmall⟩ :=
    exists_small_ball_volume_bounds_of_bounded_geometry
      (I := I) Y (hcomplete.complete k) (hconn k) hgeom_k p
  refine ⟨C0, D, Blo, A, δ, hC0, hD, hBlo, hδ, ?_⟩
  intro s hs hsd
  simpa [Y, hgeom_k] using hsmall (s := s) hs hsd

omit [NeZero (Module.finrank Real E)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricci_bounded_below_of_sequence_bounded_geometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) (k : Nat) :
    let Y := X.obj k
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) Y.metric
      (-((Module.finrank Real E : Real) ^ 2 * hgeom.C 0)) := by
  let Y := X.obj k
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  refine Geometry.Riemannian.BonnetMyers.ricciLower_of_rm
    (I := I) Y.metric ?_
  simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound] using
    (rm04Bound_of_seq (I := I) hgeom k)

structure UniformBallVolumeBounds
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedRiemannianSeq.Distance (I := I) X
  metricSpace : ∀ k : Nat, MetricSpace (X.obj k).M
  dist_eq : ∀ k : Nat, ∀ x y : (X.obj k).M,
    dist k x y =
      (letI : MetricSpace (X.obj k).M := metricSpace k
       @Dist.dist (X.obj k).M _ x y)
  r0 : Real
  r0_pos : 0 < r0
  multiplicity : Real → Nat
  lowerVolume : Real → Real → Real
  upperVolume : Real → Real → Real
  lowerVolume_pos : ∀ m r : Real, 0 < r → m * r ≤ r0 → 0 < lowerVolume m r
  upperVolume_nonneg : ∀ m r : Real, 0 < r → m * r ≤ r0 → 0 ≤ upperVolume m r
  upper_lt_multiplicity_mul_lower : ∀ m r : Real, 0 < r → m * r ≤ r0 →
    upperVolume m r < ((multiplicity m + 1 : Nat) : Real) * lowerVolume m r
  small_ball_measurable : ∀ m : Real, ∀ k : Nat, ∀ p : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := metricSpace k
      letI : MeasurableSpace Y.M := borel Y.M
      MeasurableSet (Metric.ball p (r / 2))
  small_ball_volume_lower : ∀ m : Real, ∀ k : Nat, ∀ p : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := metricSpace k
      letI : MeasurableSpace Y.M := borel Y.M
      ENNReal.ofReal (lowerVolume m r) ≤
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
          (Metric.ball p (r / 2))
  large_ball_volume_upper : ∀ m : Real, ∀ k : Nat, ∀ z : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := metricSpace k
      letI : MeasurableSpace Y.M := borel Y.M
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
          (Metric.ball z ((m + 1 / 2) * r)) ≤
        ENNReal.ofReal (upperVolume m r)

namespace UniformBallVolumeBounds

def toBallMultiplicityBound {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : UniformBallVolumeBounds (I := I) X) :
    BallMultiplicityBound (I := I) X where
  dist := h.dist
  r0 := h.r0
  r0_pos := h.r0_pos
  multiplicity := h.multiplicity
  card_le := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    let Y := X.obj k
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : T2Space Y.M := Y.t2
    let : SigmaCompactSpace Y.M := Y.sigmaCompact
    let : MetricSpace Y.M := h.metricSpace k
    let : MeasurableSpace Y.M := borel Y.M
    let μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
      (M := Y.M) Y.metric
    have hsep_metric :
        ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          r ≤ @Dist.dist Y.M _ (centers i) (centers j) := by
      intro i hi j hj hij
      simpa [h.dist_eq k] using hsep i j hij
    have hJz_metric :
        ∀ j ∈ J, @Dist.dist Y.M _ (centers j) z ≤ m * r := by
      intro j hj
      simpa [h.dist_eq k] using hJz j hj
    exact
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_card_le_meas
        μ J centers z
        (h.lowerVolume_pos m r hr hcap)
        (h.upperVolume_nonneg m r hr hcap)
        (fun j _hj => h.small_ball_measurable m k (centers j) hr hcap)
        hsep_metric hJz_metric
        (fun j _hj => h.small_ball_volume_lower m k (centers j) hr hcap)
        (h.large_ball_volume_upper m k z hr hcap)
        (h.upper_lt_multiplicity_mul_lower m r hr hcap)

end UniformBallVolumeBounds

end HCGCompactness
end DifferentialGeometry
