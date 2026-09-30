import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalMarkedInverse
import DifferentialGeometry.Geometry.Metric.Distance.ClosedBall
import DifferentialGeometry.Geometry.Metric.ConeDistance.Compactness

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  [SigmaCompactSpace W]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q]
  [IsManifold I3 ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.exists_marked_local_cone_embedding_of_local_metric_limit
    [CompactSpace (UniformSpace.Completion angles.quotient)]
    (C : AnnularConvergence H angles ray d) {a b lambda R : ℝ}
    (ha : 0 < a) (hlambda : 0 < lambda) (ha1 : a < 1) (h1b : 1 < b) (hR : 0 < R)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (target : ∀ i, SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 W (M i) ∞)
    (hcompare : ∀ᶠ i in atTop,
      let scaled := scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g
      let ball := riemannianClosedBallOf scaled (ray.point (d i)) R
      IsCompact ball ∧ ball ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn (fun _ => scaled) (fun _ => target i) (F i)
        ball {0} 0 (1 / ((i : ℝ) + 2))))
    (gQ : SmoothRiemannianMetric I3 Q) (V U : TopologicalSpace.Opens Q)
    (hVU : V ≤ U) (q : Q) (hq : q ∈ V)
    (f : ∀ i, PartialDiffeomorph I3 I3 Q (M i) ∞)
    (G : ℕ → SmoothRiemannianMetric I3 U)
    (hG : MetricCInfConvergenceOnCompacts G (gQ.restrictOpen U) (gQ.restrictOpen U))
    (hfsource : ∀ᶠ i in atTop, (U : Set Q) ⊆ (f i).source)
    (hmetric : ∀ᶠ i in atTop, ∀ (x : U) (v w : TangentSpace I3 x),
      (G i).inner x v w = (target i).inner (f i x)
        (mfderiv I3 I3 (f i) x v) (mfderiv I3 I3 (f i) x w))
    (hbase : ∀ i, f i q = F i (ray.point (d i))) :
    ∃ A : ℝ, 0 < A ∧ A ≤ R / 16 ∧
      ∃ K : Set Q, IsCompact K ∧ K ⊆ V ∧
      (∃ rK : ℝ, 0 < rK ∧ K = riemannianClosedBallOf gQ q rK) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in atTop, ∀ p ∈ K, ∀ z ∈ K,
        |(riemannianEDistOf (target i) (f i p) (f i z)).toReal -
          (riemannianEDistOf gQ p z).toReal| < epsilon) ∧
      ∃ D : Set (ℝ × UniformSpace.Completion angles.quotient), IsOpen D ∧
        (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) ∈ D ∧
        (∀ x ∈ D, x.1 ∈ Ioo a b) ∧
        ∃ (Psi : D → V) (u : ℕ → D → V)
          (y : D → ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : D → ℕ → W),
          Topology.IsEmbedding Psi ∧ MapClusterPt Psi atTop u ∧
          (∀ x : D, (Psi x : Q) ∈ K) ∧
          (∀ i (x : D), (u i x : Q) ∈ K) ∧
          (∀ x : D, (x : ℝ × UniformSpace.Completion angles.quotient) =
            (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) → (Psi x : Q) = q) ∧
          (∀ x z : D, (riemannianEDistOf (gQ.restrictOpen V) (Psi x) (Psi z)).toReal =
            lambda * Metric.coneDistance (x : ℝ × UniformSpace.Completion angles.quotient)
              (z : ℝ × UniformSpace.Completion angles.quotient)) ∧
          (∀ x : D, Tendsto (y x) atTop (𝓝 (x : ℝ × UniformSpace.Completion angles.quotient))) ∧
          ∀ x : D, ∀ᶠ i in atTop,
            (y x i, w x i) ∈ C.relation a b i ∧
            metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
              (ray.point (d i)) (w x i) < A ∧
            (u i x : Q) = (f i).symm (F i (w x i)) ∧
            f i (u i x) = F i (w x i) := by
  classical
  obtain ⟨A, hA, hAR, K, hK, hKV, hqK, ⟨rK, hrK, hKrK⟩,
      hrestrict, herror, y0, w0, hy0, hrel0, hinv0, hpair0, hbase0⟩ :=
    C.exists_local_marked_inverse_distance_family_in_ball ha ha1 h1b hR hd hQ hscale
      target F hcompare gQ V U hVU q hq f G hG hfsource hmetric hbase
  subst K
  let K := riemannianClosedBallOf gQ q rK
  let o : ℝ × UniformSpace.Completion angles.quotient :=
    (1, (angles.classOf ray : UniformSpace.Completion angles.quotient))
  let D0 := {x : ℝ × UniformSpace.Completion angles.quotient |
    x.1 ∈ Icc a b ∧ lambda * Metric.coneDistance o x < A}
  let D := {x : ℝ × UniformSpace.Completion angles.quotient |
    x.1 ∈ Ioo a b ∧ lambda * Metric.coneDistance o x < A}
  have hDopen : IsOpen D := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt (continuous_const.mul (Metric.continuous_coneDistance.comp
      (continuous_const.prodMk continuous_id))) continuous_const)
  have hoD : o ∈ D := by
    refine ⟨⟨ha1, h1b⟩, ?_⟩
    have hozero : Metric.coneDistance o o = 0 :=
      (Metric.coneDistance_eq_zero_iff zero_lt_one zero_lt_one).mpr rfl
    simpa only [hozero, mul_zero] using hA
  let incD : D → D0 := fun x => ⟨x.1, ⟨⟨x.2.1.1.le, x.2.1.2.le⟩, x.2.2⟩⟩
  let y := fun x : D => y0 (incD x)
  let w := fun x : D => w0 (incD x)
  obtain ⟨m, hm, hmdist⟩ := Geometry.Riemannian.exists_metricSpace_closedBall gQ q (r := rK)
  let : MetricSpace K := m.replaceTopology hm.symm
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let qK : K := ⟨q, hqK⟩
  let uK : ℕ → D → K := fun i x =>
    if h : (f i).symm (F i (w x i)) ∈ K then ⟨(f i).symm (F i (w x i)), h⟩ else qK
  have huK (x : D) : ∀ᶠ i in atTop,
      (uK i x : Q) = (f i).symm (F i (w x i)) := by
    filter_upwards [hinv0 (incD x)] with i hi
    have hmem : (f i).symm (F i (w x i)) ∈ K := hi.2.1
    dsimp only [uK]
    rw [dite_eq_left hmem]
  have hdistK (x z : K) : dist x z = (riemannianEDistOf gQ x z).toReal := hmdist x z
  have hpair (x z : D) : Tendsto (fun i => dist (uK i x) (uK i z)) atTop
      (𝓝 (lambda * Metric.coneDistance (x : ℝ × UniformSpace.Completion angles.quotient)
        (z : ℝ × UniformSpace.Completion angles.quotient))) := by
    apply (hpair0 (incD x) (incD z)).congr'
    filter_upwards [huK x, huK z] with i hx hz
    rw [hdistK, hx, hz]
  let oD : D := ⟨o, hoD⟩
  have hbaseK : Tendsto (fun i => dist (uK i oD) qK) atTop (𝓝 0) := by
    apply (hbase0 (incD oD) rfl).congr'
    filter_upwards [huK oD] with i hi
    rw [hdistK, hi]
  obtain ⟨PK, hPKcluster, hPKemb, hPKbase, hPKmetric⟩ :=
    Metric.exists_marked_cone_embedding_of_compact_pair_limits ha hlambda D
      (fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩) uK hpair oD qK hbaseK
  let inc : K → V := fun x => ⟨x.1, hKV x.2⟩
  have hincCont : Continuous inc := continuous_subtype_val.subtype_mk _
  have hincEmb : Topology.IsEmbedding inc :=
    Topology.IsEmbedding.of_comp hincCont continuous_subtype_val Topology.IsEmbedding.subtypeVal
  let Psi : D → V := inc ∘ PK
  let u : ℕ → D → V := fun i x => inc (uK i x)
  have hmap : Continuous (fun p : D → K => fun x => inc (p x)) :=
    continuous_pi fun x => hincCont.comp (continuous_apply x)
  refine ⟨A, hA, hAR, K, hK, hKV, ⟨rK, hrK, rfl⟩, herror, D, hDopen, hoD, fun _ hx => hx.1,
    Psi, u, y, w, hincEmb.comp hPKemb, hPKcluster.continuousAt_comp hmap.continuousAt,
    fun x => (PK x).2, fun i x => (uK i x).2, ?_, ?_, fun x => hy0 (incD x), ?_⟩
  · intro x hx
    have heq : x = oD := Subtype.ext hx
    subst x
    exact congrArg (fun z : K => (z : Q)) hPKbase
  · intro x z
    rw [hrestrict (Psi x) (Psi z) (PK x).2 (PK z).2]
    exact (hdistK (PK x) (PK z)).symm.trans (hPKmetric x z)
  · intro x
    filter_upwards [hrel0 (incD x), huK x, hinv0 (incD x)] with i hrel hu hinv
    refine ⟨hrel.1, hinv.1, hu, ?_⟩
    change f i ((uK i x : K) : Q) = F i (w x i)
    rw [hu]
    exact hinv.2.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
