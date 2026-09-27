import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.InjectivityRadiusDecay.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeOverlap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Filter Manifold
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance seedDecompositionMeasurableSpaceE : MeasurableSpace E := borel E
private local instance seedDecompositionBorelSpaceE : BorelSpace E := ⟨rfl⟩

omit [CompleteSpace E] in
theorem InjectivityRadiusDecay.dist_eq_riemannianSequenceDistance_of_realizesDistance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (h : hd.RealizesDistance) :
    hd.dist = riemannianSequenceDistance (I := I) X := by
  funext k x y
  simp only [riemannianSequenceDistance]
  rw [← ENNReal.toReal_ofReal (h.dist_nonneg k x y), ← h.edist_eq k x y]

omit [CompleteSpace E] in
theorem InjectivityRadiusDecay.realizesDistance_of_dist_eq_riemannianSequenceDistance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X)
    (hconn : ∀ k : ℕ,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (h : hd.dist = riemannianSequenceDistance (I := I) X) : hd.RealizesDistance := by
  refine ⟨?_, ?_⟩
  · intro k x y
    rw [h]
    simp only [riemannianSequenceDistance]
    exact ENNReal.toReal_nonneg
  · intro k x y
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    let : T2Space (X.obj k).M := (X.obj k).t2
    let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    let : RiemannianBundle (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    let : (y : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    have : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
    let : ConnectedSpace (X.obj k).M := hconn k
    rw [h]
    simp only [riemannianSequenceDistance]
    exact (ENNReal.ofReal_toReal (by
      rw [IsRiemannianManifold.out (I := I)]
      exact riemannianEDist_ne_top (I := I) x y)).symm

omit [CompleteSpace E] in
theorem MetricCompactSeed.decay_dist_eq_riemannianSequenceDistance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X) :
    b.decay.dist = riemannianSequenceDistance (I := I) X :=
  InjectivityRadiusDecay.dist_eq_riemannianSequenceDistance_of_realizesDistance
    b.decay b.realizes

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem riemannianSequenceDistance_comm
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (x y : (X.obj k).M) :
    riemannianSequenceDistance (I := I) X k x y =
      riemannianSequenceDistance (I := I) X k y x := by
  simp only [riemannianSequenceDistance]
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  exact congrArg ENNReal.toReal (edist_comm x y)

theorem exists_subseq_ballInjectivityRadiusDecay_of_seqBallGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hinj : BaseInjBound (I := I) X)
    (hball : SeqBallGeometry (I := I) X)
    (A : ℝ) (hA : 0 < A) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
        ∀ k : ℕ,
          letI : TopologicalSpace ((X.subseq ψ).obj k).M :=
            ((X.subseq ψ).obj k).topology
          letI : EMetricSpace ((X.subseq ψ).obj k).M :=
            ((X.subseq ψ).obj k).emetricSpace (I := I)
          ∀ x : ((X.subseq ψ).obj k).M,
            edist ((X.subseq ψ).obj k).basepoint x ≤ ENNReal.ofReal A →
              HasInjRadiusAt (I := I) ((X.subseq ψ).obj k) x
                (a * (min hinj.ρ 1) ^ Module.finrank ℝ E *
                  Real.exp (-C *
                    (edist ((X.subseq ψ).obj k).basepoint x).toReal)) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * A + 3)
  let σ : ℕ → ℕ := fun k => N + k
  let X' := X.subseq σ
  have hcomplete' : SeqMetricComplete (I := I) X' := hcomplete.subseq σ
  have hconn' : ∀ k : ℕ,
      let _ : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      ConnectedSpace (X'.obj k).M := PointedRiemannianSeq.connected_subseq hconn σ
  let hbase' : BaseInjBound (I := I) X' := hinj.subseq σ
  have hrm' : ∀ k : ℕ,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      ∀ y : (X'.obj k).M,
        edist (X'.obj k).basepoint y ≤ ENNReal.ofReal (2 * A + 3) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X'.obj k).metric y 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I)
            (M := (X'.obj k).M) (X'.obj k).metric y)) ≤ hball.C N 0 := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    intro y hy
    have hy' : riemannianEDistOf (I := I) (X'.obj k).metric
        (X'.obj k).basepoint y ≤ ENNReal.ofReal (N : ℝ) := by
      rw [PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I) (X'.obj k)]
      exact hy.trans (ENNReal.ofReal_le_ofReal hN)
    have hjet := hball.bound N 0 (σ k) (Nat.le_add_right N k) y hy'
    exact (normSq0S_metricRm04At_le_curvDerivNorm (I := I) (X'.obj k).metric y).trans hjet
  have hpull' : ∀ k : ℕ,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
      letI : T2Space (X'.obj k).M := (X'.obj k).t2
      letI : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
      letI : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
        (X'.obj k).riemBundle (I := I)
      letI : (y : (X'.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
        (X'.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X'.obj k).M => TangentSpace I y) :=
        (X'.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X'.obj k).M :=
        MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
      letI : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
      ∀ (x : (X'.obj k).M)
        (hEnorm : ∀ (y : (X'.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X'.obj k).metric.inner y w w)))
        (q R : ℝ), 0 ≤ q → 0 < R →
        (∀ z, z ∈ Metric.ball (0 : E) R → z ≠ 0 →
          ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 →
            ¬ IsConjVec (I := I) (X'.obj k).metric hEnorm x
              ((t • normalFrame (I := I) (X'.obj k).metric x z : TangentSpace I x) : E)) →
        ricciBoundedBelowOn (I := I) (X'.obj k).metric
          {y : (X'.obj k).M | riemannianEDist I x y < ENNReal.ofReal R}
          (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
        intrinsicPullVol (I := I) (X'.obj k).metric hEnorm x R ≤
          (MeasureTheory.volume : MeasureTheory.Measure E).toSphere Set.univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) := by
    intro k
    let : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    let : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    let : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    let : SigmaCompactSpace (X'.obj k).M := (X'.obj k).sigmaCompact
    let : T2Space (X'.obj k).M := (X'.obj k).t2
    let : T2Space (TangentBundle I (X'.obj k).M) := (X'.obj k).t2TangentBundle
    let : RiemannianBundle (fun y : (X'.obj k).M => TangentSpace I y) :=
      (X'.obj k).riemBundle (I := I)
    let : (y : (X'.obj k).M) → InnerProductSpace ℝ (TangentSpace I y) :=
      (X'.obj k).riemInner (I := I)
    let : IsContinuousRiemannianBundle E
        (fun y : (X'.obj k).M => TangentSpace I y) :=
      (X'.obj k).riemBundle_cont (I := I)
    let : EMetricSpace (X'.obj k).M := (X'.obj k).emetricSpace (I := I)
    let : CompleteSpace (X'.obj k).M :=
      MetricComplete.complete (I := I) (X'.obj k) (hcomplete'.complete k)
    let : IsRiemannianManifold I (X'.obj k).M := ⟨fun _ _ => rfl⟩
    intro x hEnorm q R hq hR hno hRic
    exact intrinsicPullVol_le_hyperbolic_of_ricciBoundedBelowOn
      (I := I) (X'.obj k).metric hEnorm x hq hR hno hRic
  obtain ⟨a, C, ha, hC, hdec⟩ :=
    exists_ball_injectivity_radius_decay (I := I) X' hcomplete' hconn' hbase' A hA
      (hball.C N 0) (hball.nonneg N 0) hrm' hpull'
  refine ⟨σ, fun i j hij => Nat.add_lt_add_left hij N, a, C, ha, hC, ?_⟩
  intro k
  simpa only [BaseInjBound.subseq, hbase', X', σ] using hdec k

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def StaircaseSeedDecayFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : ℕ,
    let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  Nonempty (SeqBallGeometry (I := I) Y) →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ hd : InjectivityRadiusDecay (I := I) (Y.subseq ψ), hd.RealizesDistance

def StaircaseSeedPackingFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X) : Prop :=
  SeqMetricComplete (I := I) X →
  (∀ i : ℕ,
    let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
    ConnectedSpace (X.obj i).M) →
  BaseInjBound (I := I) X →
  Nonempty (SeqBallGeometry (I := I) X) →
  hd.RealizesDistance →
  Nonempty (∀ D : ℝ, 0 < D → hd.PackingBound D) ∧
    ∃ vol : BallMultiplicityBound (I := I) X, vol.dist = hd.dist

def StaircaseSeedChartFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X) : Prop :=
  SeqMetricComplete (I := I) X →
  (∀ i : ℕ,
    let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
    ConnectedSpace (X.obj i).M) →
  BaseInjBound (I := I) X →
  Nonempty (SeqBallGeometry (I := I) X) →
  hd.RealizesDistance →
  Nonempty (BoundedGeometryNormalChartData (I := I) X hd)

omit [CompleteSpace E] in
theorem staircaseMetricCompactSeedFrontier_of_seedFrontiers
    (hdecay : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseSeedDecayFrontier (I := I) Y)
    (hpack : ∀ (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) X),
      StaircaseSeedPackingFrontier (I := I) X hd)
    (hchart : ∀ (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) X),
      StaircaseSeedChartFrontier (I := I) X hd) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y := by
  intro Y hcomplete hconn hinj hball
  obtain ⟨ψ, hψ, hd, hreal⟩ := hdecay Y hcomplete hconn hinj hball
  have hcomplete' : SeqMetricComplete (I := I) (Y.subseq ψ) := hcomplete.subseq ψ
  have hconn' : ∀ i : ℕ,
      let _ : TopologicalSpace ((Y.subseq ψ).obj i).M := ((Y.subseq ψ).obj i).topology
      ConnectedSpace ((Y.subseq ψ).obj i).M :=
    PointedRiemannianSeq.connected_subseq hconn ψ
  have hinj' : BaseInjBound (I := I) (Y.subseq ψ) := hinj.subseq ψ
  have hball' : Nonempty (SeqBallGeometry (I := I) (Y.subseq ψ)) :=
    ⟨(Classical.choice hball).subseq ψ hψ.id_le⟩
  obtain ⟨hpackAll, hvol⟩ := hpack (Y.subseq ψ) hd hcomplete' hconn' hinj' hball' hreal
  obtain ⟨vol, hvolEq⟩ := hvol
  let packAll : ∀ D : ℝ, 0 < D → hd.PackingBound D := Classical.choice hpackAll
  exact ⟨ψ, hψ,
    { decay := hd
      packAll := packAll
      volume := vol
      dist_eq := hvolEq
      realizes := hreal },
    hchart (Y.subseq ψ) hd hcomplete' hconn' hinj' hball' hreal⟩

omit [CompleteSpace E] in
theorem staircaseSeedDecayFrontier_of_metricCompactSeedFrontier
    {Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : StaircaseMetricCompactSeedFrontier (I := I) Y) :
    StaircaseSeedDecayFrontier (I := I) Y := by
  intro hcomplete hconn hinj hball
  obtain ⟨ψ, hψ, b, _hd⟩ := h hcomplete hconn hinj hball
  exact ⟨ψ, hψ, b.decay, b.realizes⟩

omit [CompleteSpace E] in
theorem exists_seedComponents_of_metricCompactSeedFrontier
    {Y : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : StaircaseMetricCompactSeedFrontier (I := I) Y)
    (hcomplete : SeqMetricComplete (I := I) Y)
    (hconn : ∀ i : ℕ,
      let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
      ConnectedSpace (Y.obj i).M)
    (hinj : BaseInjBound (I := I) Y)
    (hball : Nonempty (SeqBallGeometry (I := I) Y)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ hd : InjectivityRadiusDecay (I := I) (Y.subseq ψ),
        hd.RealizesDistance ∧
          Nonempty (∀ D : ℝ, 0 < D → hd.PackingBound D) ∧
          (∃ vol : BallMultiplicityBound (I := I) (Y.subseq ψ),
            vol.dist = hd.dist) ∧
          Nonempty (BoundedGeometryNormalChartData (I := I) (Y.subseq ψ) hd) := by
  obtain ⟨ψ, hψ, b, hd⟩ := h hcomplete hconn hinj hball
  exact ⟨ψ, hψ, b.decay, b.realizes, ⟨b.packAll⟩, ⟨b.volume, b.dist_eq⟩, hd⟩

theorem staircaseSeedDecayFrontier_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) Y) :
    StaircaseSeedDecayFrontier (I := I) Y := by
  intro hcomplete hconn hinj _hball
  obtain ⟨hd, hreal⟩ :=
    exists_injectivity_radius_decay (I := I) Y hcomplete hconn hgeom hinj
  exact ⟨id, strictMono_id, hd, hreal⟩

theorem staircaseSeedPackingFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    StaircaseSeedPackingFrontier (I := I) X hd := by
  intro hcomplete hconn _hinj _hball hreal
  exact ⟨⟨fun D hD => packInputOfBg (I := I) X hgeom hd hreal hcomplete hconn D hD⟩,
    (volInputOfBg (I := I) X hgeom hd hreal hcomplete hconn 1 (by norm_num)).1,
    (volInputOfBg (I := I) X hgeom hd hreal hcomplete hconn 1 (by norm_num)).2⟩

theorem staircaseSeedChartFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    StaircaseSeedChartFrontier (I := I) X hd := by
  intro hcomplete hconn _hinj _hball hreal
  exact nonempty_bounded_geometry_normal_chart_data (I := I) X hcomplete hconn hgeom hd hreal

omit [CompleteSpace E] in
theorem exists_injectivityRadiusDecay_of_uniform_exponential_decay
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (base : BaseInjBound (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (h : ∀ (k : ℕ) (x : (X.obj k).M),
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min base.ρ 1) ^ Module.finrank ℝ E *
          Real.exp (-C *
            riemannianSequenceDistance (I := I) X k x (X.obj k).basepoint))) :
    ∃ hd : InjectivityRadiusDecay (I := I) X, hd.RealizesDistance := by
  let hd : InjectivityRadiusDecay (I := I) X :=
    { baseInj := base
      dist := riemannianSequenceDistance (I := I) X
      a := a
      C := C
      a_pos := ha
      C_nonneg := hC
      decay := fun k x => h k x }
  exact ⟨hd,
    InjectivityRadiusDecay.realizesDistance_of_dist_eq_riemannianSequenceDistance
      (I := I) hd hconn rfl⟩

theorem exists_local_pointed_metric_compactness_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X) :
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
       ConnectedSpace P.limit.M) :=
  exists_local_pointed_metric_compactness_of_metricCompactSeed X hcomplete hconnected
    (exists_metricCompactSeed_of_seqBoundedGeometry (I := I) X hcomplete hconnected hgeom hinj)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
