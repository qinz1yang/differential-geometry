import DifferentialGeometry.Analysis.Calculus.Compactness.EventuallyBounded
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BallGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.NormalCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessSeedDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase

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
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [CompleteSpace E] in
theorem exists_metric_limit_subsequence_of_seqBallNormalChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (c : ∀ k : Nat, (X.obj k).M) (N : Nat)
    (hc : ∀ k : Nat,
      (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
       letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
       letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
       riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint (c k) <=
         ENNReal.ofReal (N : Real))) :
    ∃ (phi : Nat -> Nat) (gInf : E -> (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧ ContDiffOn Real (⊤ : ℕ∞) gInf Set.univ ∧
        MapCInfConvergenceOnCompacts Set.univ
          (fun k _ =>
            letI : TopologicalSpace (X.obj (phi k)).M := (X.obj (phi k)).topology
            letI : ChartedSpace H (X.obj (phi k)).M := (X.obj (phi k)).charted
            letI : IsManifold I ∞ (X.obj (phi k)).M := (X.obj (phi k)).smooth
            letI : T2Space (TangentBundle I (X.obj (phi k)).M) :=
              (X.obj (phi k)).t2TangentBundle
            (d.chart (phi k) (c (phi k))).metric (X.obj (phi k)).metric 0) gInf ∧
        ∀ z : E, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 <= gInf z v v ∧
            gInf z v v <= 2 * ‖v‖ ^ 2 := by
  let g0 : Nat -> E -> (E →L[Real] E →L[Real] Real) := fun k =>
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    fun _ => (d.chart k (c k)).metric (X.obj k).metric 0
  have hzero : ∀ k : Nat,
      (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
       letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
       letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
       letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
       (0 : E) ∈ Metric.ball 0 ((d.chart k (c k)).radius)) := by
    intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    rw [Metric.mem_ball, dist_self]
    exact (d.chart k (c k)).radius_pos
  have hsmooth : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : ∀ r : Nat, ∀ K : Set E, IsCompact K -> K ⊆ Set.univ ->
      ∃ C : Real, ∀ᶠ k in atTop, ∀ x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= C := by
    intro r K _hK _hKU
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      refine ⟨d.metricC N 0, eventually_atTop.mpr ⟨N, fun k hk => ?_⟩⟩
      intro x _hx
      let : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      have hkn : N + 0 <= k := by omega
      have hderiv := d.metric_deriv N 0 k hkn (c k) (hc k) 0 (hzero k)
      simpa only [g0, norm_iteratedFDeriv_zero] using hderiv
    · refine ⟨0, Eventually.of_forall (fun k x _hx => ?_)⟩
      simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact le_refl 0
  have hequiv : ∀ k : Nat, ∀ z, z ∈ (Set.univ : Set E) -> ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 <= g0 k z v v ∧
        g0 k z v v <= 2 * ‖v‖ ^ 2 := by
    intro k _z _hz v
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    exact d.metric_equiv k (c k) 0 (hzero k) v
  simpa only [g0, Set.mem_univ, forall_const] using
    (exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd
      (E := E) isOpen_univ g0 hsmooth hbdd (1 / 2) 2 hequiv)

omit [CompleteSpace E] in
theorem nonempty_seqBallNormalChartData_of_boundedGeometryNormalChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) :
    Nonempty (SeqBallNormalChartData (I := I) X hd) :=
  ⟨SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d⟩

theorem nonempty_seqBallNormalChartData_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) (hreal : hd.RealizesDistance) :
    Nonempty (SeqBallNormalChartData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    nonempty_bounded_geometry_normal_chart_data (I := I) X hcomplete hconn hgeom hd hreal
  exact ⟨SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d⟩

namespace SeqBallNormalChartData

omit [CompleteSpace E] in
theorem metric_deriv_ball
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    {A : Real} {p j : Nat} (hj : Nat.ceil A + p <= j) {x : (X.obj j).M}
    (hx : letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal A) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.chart j x).MetricDerivBound (X.obj j).metric
       (Metric.ball (0 : E) (d.chart j x).radius) p (d.metricC (Nat.ceil A) p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  exact d.metric_deriv (Nat.ceil A) p j hj x
    (hx.trans (ENNReal.ofReal_le_ofReal (Nat.le_ceil A)))

omit [CompleteSpace E] in
theorem metric_deriv_ball_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (A : Real) (p : Nat) :
    0 <= d.metricC (Nat.ceil A) p :=
  d.metricC_nonneg (Nat.ceil A) p

end SeqBallNormalChartData

def StaircaseChartSeedFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : Nat,
    letI : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  Nonempty (SeqBallGeometry (I := I) Y) →
  ∃ psi : Nat → Nat, StrictMono psi ∧
    ∃ b : MetricCompactSeed (I := I) (Y.subseq psi),
      Nonempty (SeqBallNormalChartData (I := I) (Y.subseq psi) b.decay)

def StaircaseChartEngineFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : Nat,
    letI : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  (∃ psi : Nat → Nat, StrictMono psi ∧
    ∃ b : MetricCompactSeed (I := I) (Y.subseq psi),
      Nonempty (SeqBallNormalChartData (I := I) (Y.subseq psi) b.decay)) →
  ∃ C : CanonicalMetricCompactness (I := I) Y,
    @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology

def StaircaseChartCompactnessFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : Nat,
    letI : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  Nonempty (SeqBallGeometry (I := I) Y) →
  ∃ C : CanonicalMetricCompactness (I := I) Y,
    @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology

theorem staircaseChartCompactnessFrontier_of_seedFrontier_and_engineFrontier
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartSeedFrontier (I := I) Y)
    (hengine : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartEngineFrontier (I := I) Y) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartCompactnessFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj hball
  obtain ⟨psi, hpsi, b, hd⟩ := hseed Y hcomplete hconnected hinj hball
  exact hengine Y hcomplete hconnected hinj ⟨psi, hpsi, b, hd⟩

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
omit [CompleteSpace E] in
theorem staircaseChartSeedFrontier_of_metricCompactSeedFrontier
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartSeedFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj hball
  obtain ⟨psi, hpsi, b, hd⟩ := hseed Y hcomplete hconnected hinj hball
  exact ⟨psi, hpsi, b,
    ⟨SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I)
      (Classical.choice hd)⟩⟩

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
theorem staircaseChartCompactnessFrontier_of_metricCompactSeedFrontier
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartCompactnessFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj hball
  obtain ⟨psi, hpsi, b, hd⟩ := hseed Y hcomplete hconnected hinj hball
  let C : CanonicalMetricCompactness (I := I) (Y.subseq psi) :=
    b.higherRegularityCanonicalMetricCompactness (Classical.choice hd)
      (hcomplete.subseq psi) (PointedRiemannianSeq.connected_subseq hconnected psi)
  have hCconn : @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology :=
    b.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd)
      (hcomplete.subseq psi) (PointedRiemannianSeq.connected_subseq hconnected psi)
  exact ⟨C.ofSubsequence psi hpsi, by
    change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
    exact hCconn⟩

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
theorem staircaseChartCompactnessFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    StaircaseChartCompactnessFrontier (I := I) X := by
  intro hcomplete hconnected hinj _hball
  obtain ⟨phi, hphi, b, hd⟩ :=
    exists_metricCompactSeed_of_seqBoundedGeometry (I := I) X hcomplete hconnected hgeom hinj
  let C : CanonicalMetricCompactness (I := I) (X.subseq phi) :=
    b.higherRegularityCanonicalMetricCompactness (Classical.choice hd)
      (hcomplete.subseq phi) (PointedRiemannianSeq.connected_subseq hconnected phi)
  have hCconn : @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology :=
    b.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd)
      (hcomplete.subseq phi) (PointedRiemannianSeq.connected_subseq hconnected phi)
  exact ⟨C.ofSubsequence phi hphi, by
    change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
    exact hCconn⟩

def StaircaseSeedChartDataFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X) : Prop :=
  SeqMetricComplete (I := I) X →
  (∀ i : Nat,
    letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
    ConnectedSpace (X.obj i).M) →
  BaseInjBound (I := I) X →
  Nonempty (SeqBallGeometry (I := I) X) →
  hd.RealizesDistance →
  Nonempty (SeqBallNormalChartData (I := I) X hd)

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
omit [CompleteSpace E] in
theorem staircaseSeedChartDataFrontier_of_staircaseSeedChartFrontier
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (h : StaircaseSeedChartFrontier (I := I) X hd) :
    StaircaseSeedChartDataFrontier (I := I) X hd := by
  intro hcomplete hconn hinj hball hreal
  obtain ⟨d⟩ := h hcomplete hconn hinj hball hreal
  exact ⟨SeqBallNormalChartData.of_boundedGeometryNormalChartData (I := I) d⟩

theorem staircaseSeedChartDataFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    StaircaseSeedChartDataFrontier (I := I) X hd := by
  intro hcomplete hconn _hinj _hball hreal
  exact nonempty_seqBallNormalChartData_of_seqBoundedGeometry (I := I) X
    hcomplete hconn hgeom hd hreal

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
omit [CompleteSpace E] in
theorem staircaseChartSeedFrontier_of_seedFrontiers
    (hdecay : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseSeedDecayFrontier (I := I) Y)
    (hpack : ∀ (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) X),
      StaircaseSeedPackingFrontier (I := I) X hd)
    (hchart : ∀ (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) X),
      StaircaseSeedChartDataFrontier (I := I) X hd) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartSeedFrontier (I := I) Y := by
  intro Y hcomplete hconn hinj hball
  obtain ⟨psi, hpsi, hd, hreal⟩ := hdecay Y hcomplete hconn hinj hball
  have hcomplete' : SeqMetricComplete (I := I) (Y.subseq psi) := hcomplete.subseq psi
  have hconn' : ∀ i : Nat,
      letI : TopologicalSpace ((Y.subseq psi).obj i).M := ((Y.subseq psi).obj i).topology
      ConnectedSpace ((Y.subseq psi).obj i).M :=
    PointedRiemannianSeq.connected_subseq hconn psi
  have hinj' : BaseInjBound (I := I) (Y.subseq psi) := hinj.subseq psi
  have hball' : Nonempty (SeqBallGeometry (I := I) (Y.subseq psi)) :=
    ⟨(Classical.choice hball).subseq psi hpsi.id_le⟩
  obtain ⟨hpackAll, hvol⟩ := hpack (Y.subseq psi) hd hcomplete' hconn' hinj' hball' hreal
  obtain ⟨vol, hvolEq⟩ := hvol
  let packAll : ∀ D : Real, 0 < D → hd.PackingBound D := Classical.choice hpackAll
  exact ⟨psi, hpsi,
    { decay := hd
      packAll := packAll
      volume := vol
      dist_eq := hvolEq
      realizes := hreal },
    hchart (Y.subseq psi) hd hcomplete' hconn' hinj' hball' hreal⟩

theorem exists_local_pointed_metric_compactness_of_staircaseChartCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : Nat,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
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
      StaircaseChartCompactnessFrontier (I := I) Y) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨phi, hphi, hball⟩ := exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets
  obtain ⟨C, hCconn⟩ :=
    hfrontier (X.subseq phi) (hcomplete.subseq phi)
      (PointedRiemannianSeq.connected_subseq hconnected phi) (hinj.subseq phi) hball
  let C₀ : CanonicalMetricCompactness (I := I) X := C.ofSubsequence phi hphi
  refine ⟨C₀.compactness, C₀.domain_eq_canonical, C₀.reference_eq_limit, ?_⟩
  change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
  exact hCconn

theorem exists_local_pointed_metric_compactness_of_staircaseChartSeed_and_engineFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : Nat,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartSeedFrontier (I := I) Y)
    (hengine : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseChartEngineFrontier (I := I) Y) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) :=
  exists_local_pointed_metric_compactness_of_staircaseChartCompactnessFrontier
    (I := I) X hcomplete hconnected hinj hjets
    (staircaseChartCompactnessFrontier_of_seedFrontier_and_engineFrontier
      (I := I) hseed hengine)

end CheegerGromovCompactness
end DifferentialGeometry
