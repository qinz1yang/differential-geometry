import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedSpatialNeckScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCompactOrNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardDistanceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedRestart

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

open private nonempty_standard_tangent_orientation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels

theorem standard_complete_pointed_limit_scalar_bounded
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    {tau : ℝ} (htau : 0 < tau)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
    ∀ (L : PointedRiemannianManifold (𝓡 3)) (subseq : ℕ → ℕ)
      (maps : PointedRiemannianConvergenceMaps X L subseq) (C : MetricConvergenceData maps),
      (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      MetricComplete L → ConnectedSpace L.M →
      ∃ K : ℝ, ∀ x : L.M, metricScalarAt L.metric x ≤ K := by
  intro X L subseq maps C hcanonical hcomplete hconnected
  have hoperator : ∀ x : L.M, metricAlgebraicCurvatureTensorAt L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3) := by
    apply Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence C hcanonical
    intro K hK
    exact Eventually.of_forall fun k z _ _ =>
      (S (subseq k)).curvatureOperator_nonnegative (time (subseq k)) (htime (subseq k)).1 (maps.map k z)
  have hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature L.metric := by
    apply (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff L.metric).mpr
    intro x v w
    have hh := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hoperator x))
      1 (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      tensor04StandardAt_apply, metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt_apply] using hh
  let _ : ∀ i, ConnectedSpace (X.obj i).M := fun _ => by change ConnectedSpace E3; infer_instance
  obtain ⟨alpha0, ha0, hsmall0, hneckbound⟩ := exists_eventually_spatialNeck_scalar_upper_bound
  let alpha := neckModelTolerance alpha0 / 2
  have htol : neckModelTolerance alpha0 < alpha0 :=
    (neckModelTolerance_le_smallness alpha0).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha0 hsmall0)
  have ha : 0 < alpha := half_pos (neckModelTolerance_pos ha0)
  have hsmall : alpha < 1 / 32 := by dsimp [alpha]; linarith
  have hnktol : 2 * alpha = neckModelTolerance alpha0 := by dsimp [alpha]; ring
  let kappa := standardModelKappa
  obtain ⟨epsStar, r, D, hepsStar, hr, hD, hwindow⟩ :=
    exists_windowed_scalar_comparison_or_spatial_neck kappa ha hsmall
  let eps := min (epsStar / 2) (1 / 2)
  have heps : 0 < eps := lt_min (half_pos hepsStar) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsStar' : eps ≤ epsStar := (min_le_left _ _).trans (half_le_self hepsStar.le)
  obtain ⟨Q, hQ, hmodels⟩ := exists_standard_high_scalar_model_threshold heps heps1 htau
  obtain ⟨B, _hB, hbound⟩ := hneckbound X L subseq maps C hcanonical hcomplete hconnected hsec
  let A := max (max Q 1) (D * (metricScalarAt L.metric L.basepoint + 1))
  refine ⟨max A (D * B), ?_⟩
  apply metricScalarAt_le_of_eventually_comparable_spatialNeck
    maps C hcanonical hcomplete hconnected.toPreconnectedSpace hD.le hr.le hbound
  intro x hx
  have hsource : ∀ᶠ i in atTop, A < metricScalarAt (X.obj (subseq i)).metric (maps.map i x) :=
    (Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      C hcanonical x).eventually (Ioi_mem_nhds hx)
  have hbase : ∀ᶠ i in atTop, metricScalarAt (X.obj (subseq i)).metric (point (subseq i)) ≤
      metricScalarAt L.metric L.basepoint + 1 := by
    have hh := (Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      C hcanonical L.basepoint).eventually (Iio_mem_nhds (lt_add_one _))
    filter_upwards [hh] with i hi
    have he := maps.basepoint_map i
    change maps.map i L.basepoint = point (subseq i) at he
    rw [he] at hi
    exact hi.le
  filter_upwards [hsource, hbase] with i hi hibase
  have hQi : Q ≤ metricScalarAt ((S (subseq i)).metric (time (subseq i))) (maps.map i x) :=
    ((le_max_left Q 1).trans (le_max_left _ _)).trans hi.le
  obtain ⟨o⟩ := nonempty_standard_tangent_orientation
  obtain ⟨W, oN, _⟩ := hmodels (S (subseq i)) o (maps.map i x) (time (subseq i))
    (htime (subseq i)).1 (htime (subseq i)).2.1 (htime (subseq i)).2.2 hQi
  rcases hwindow E3 (lifetimeInterval (S (subseq i)).lifetime (S (subseq i)).lifetime_pos)
      (S (subseq i)).toSolutionOn eps (maps.map i x) (time (subseq i)) W hepsStar' oN with hglobal | hneck
  · have hh := hglobal (point (subseq i))
    have hA : D * (metricScalarAt L.metric L.basepoint + 1) ≤ A := le_max_right _ _
    have hup := mul_le_mul_of_nonneg_left hibase hD.le
    exact (not_le_of_gt hi) (hh.trans (hup.trans hA)) |>.elim
  · obtain ⟨y, ⟨nk⟩, hlo, _hhi, hdist⟩ := hneck
    have hone : 1 ≤ metricScalarAt ((S (subseq i)).metric (time (subseq i))) (maps.map i x) :=
      ((le_max_right Q 1).trans (le_max_left _ _)).trans hi.le
    have hroot : 1 ≤ Real.sqrt (metricScalarAt ((S (subseq i)).metric (time (subseq i))) (maps.map i x)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hone
    change Real.sqrt (metricScalarAt ((S (subseq i)).metric (time (subseq i))) (maps.map i x)) *
      metricDistance ((S (subseq i)).metric (time (subseq i))) (maps.map i x) (W.embedding y) ≤ r at hdist
    have hdist0 : metricDistance ((S (subseq i)).metric (time (subseq i)))
        (maps.map i x) (W.embedding y) ≤ r := by
      have hn : 0 ≤ metricDistance ((S (subseq i)).metric (time (subseq i)))
          (maps.map i x) (W.embedding y) := ENNReal.toReal_nonneg
      nlinarith
    have hball : W.embedding y ∈ riemannianClosedBallOf (X.obj (subseq i)).metric (maps.map i x) r :=
      (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _) hr.le).mpr hdist0
    have hcompare : metricScalarAt (X.obj (subseq i)).metric (maps.map i x) ≤
        D * metricScalarAt (X.obj (subseq i)).metric (W.embedding y) := by
      have hh := mul_le_mul_of_nonneg_left hlo hD.le
      rwa [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] at hh
    rw [hnktol] at nk
    exact ⟨W.embedding y, hball, ⟨nk⟩, hcompare⟩

theorem exists_standard_complete_terminal_limit_of_bounded_scalar_on_balls
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    {tau : ℝ} (htau : 0 < tau)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → ∃ A : ℝ, ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ A) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
    ∃ P : MetricCompactLimit X,
      (∀ k, P.convergence.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      ConnectedSpace P.limit.M ∧
      (∀ k, IsCompact (closure (P.maps.source k))) ∧
      (∀ k, IsConnected (P.maps.source k)) ∧
      (∀ k, closure (P.maps.source k) ⊆ P.maps.source (k + 1)) ∧
      ∃ K : ℝ, ∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ K := by
  intro X
  have hc : SeqMetricComplete X := ⟨fun i => (S i).pointedFlow_complete (time i) (htime i).1⟩
  have hconn : ∀ i, ConnectedSpace (X.obj i).M := fun _ => by
    change ConnectedSpace E3
    infer_instance
  obtain ⟨P, hcanonical, _href, hconnected, hpre, hsource, hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity X hc hconn
      (by
        intro r hr m
        obtain ⟨A, hA⟩ := hscalar (r + 1) (by linarith)
        obtain ⟨C, hC, hb⟩ := standard_curvature_derivative_bounds_of_terminal_scalar_bound
          (half_pos htau) (by norm_num : (0 : ℝ) < 1) hr.le (lt_add_one r) A
        refine ⟨C m, hC m, ?_⟩
        filter_upwards [hA] with i hi y hy
        exact hb (S i) (time i) (htime i).1 (by linarith [(htime i).2.1])
          (htime i).2.2.le (point i) hi m (time i) ⟨by linarith, le_rfl⟩ y hy)
      (by
        intro r hr
        obtain ⟨A, hA⟩ := hscalar (r + 1) (by linarith)
        obtain ⟨eta, heta, hb⟩ := standard_injectivity_radius_lower_of_terminal_scalar_bound
          htau hr.le (lt_add_one r) A
        refine ⟨eta, heta, ?_⟩
        filter_upwards [hA] with i hi y hy
        exact hb (S i) (time i) (htime i).1 (htime i).2.1 (htime i).2.2 (point i) hi y hy)
  refine ⟨P, hcanonical, hconnected, hpre, hsource, hnested, ?_⟩
  exact standard_complete_pointed_limit_scalar_bounded S time point htau htime
    P.limit P.subseq P.maps P.convergence.metrics hcanonical P.limit_complete hconnected

end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

theorem PartialStandardSolution.scalar_time_mul_le_of_complete_terminal_limit
    (S : PartialStandardSolution) (time : ℕ → ℝ) (p : E3)
    (htime : ∀ i, time i ∈ S.domain ∧ time i < 1) (hlim : Tendsto time atTop (𝓝 1)) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => (S.pointedFlow.atTime (time i)).repoint p⟩
    ∀ (P : MetricCompactLimit X),
      (∀ k, P.convergence.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData P.maps k) →
      ∀ K : ℝ, (∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ K) →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : E3, t * metricScalarAt (S.metric t) x ≤ K + 1 := by
  intro X P hcanonical K hK t ht x
  let L := P.limit
  let maps := P.maps
  let C := P.convergence.metrics
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    exact canonicalSourceData_referenceMetric_eq_limitMetric maps k
  let r := (riemannianEDistOf StandardCap.metric p x).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  obtain ⟨hcompact, n₀, hcapture⟩ := Perelman.KappaSolutions.exists_pointed_inverse_capture_at
    C href P.limit_complete L.basepoint hr (by norm_num : (0 : ℝ) < 1)
  obtain ⟨n₁, happrox⟩ := Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical (riemannianClosedBallOf L.metric L.basepoint ((1 + 1) * r)) hcompact 1 zero_lt_one
  have hbound : ∀ᶠ n in atTop, metricScalarAt (S.metric (time (P.subseq n))) x ≤ K + 1 := by
    filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop n₁] with n hn₀ hn₁
    have hball : x ∈ riemannianClosedBallOf (X.obj (P.subseq n)).metric (maps.map n L.basepoint) r := by
      have hbase := maps.basepoint_map n
      change maps.map n L.basepoint = p at hbase
      rw [hbase]
      change riemannianEDistOf (S.metric (time (P.subseq n))) p x ≤ ENNReal.ofReal r
      rw [ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)]
      exact S.riemannianEDistOf_le_initial (htime (P.subseq n)).1 p x
    obtain ⟨htarget, hinverse⟩ := hcapture n hn₀ x hball
    have hmap : maps.map n ((maps.partialDiffeomorph n).symm x) = x :=
      (maps.partialDiffeomorph n).right_inv htarget
    have herr := (happrox n hn₁).2 ((maps.partialDiffeomorph n).symm x) hinverse
    rw [hmap] at herr
    have hb := hK ((maps.partialDiffeomorph n).symm x)
    change |metricScalarAt (S.metric (time (P.subseq n))) x -
      metricScalarAt L.metric ((maps.partialDiffeomorph n).symm x)| < 1 at herr
    linarith [(abs_lt.mp herr).2]
  have htime' := hlim.comp P.strictMono.tendsto_atTop
  obtain ⟨n, hn, htn⟩ := (hbound.and (htime'.eventually (Ioi_mem_nhds ht.2))).exists
  have hh := S.scalar_time_mul_le ht.1.le htn.le (htime (P.subseq n)).1 x
  have hnonneg := S.one_le_scalar (time (P.subseq n)) (htime (P.subseq n)).1 x
  have hmul : time (P.subseq n) * metricScalarAt (S.metric (time (P.subseq n))) x ≤
      metricScalarAt (S.metric (time (P.subseq n))) x := by
    nlinarith [(htime (P.subseq n)).2]
  exact hh.trans (hmul.trans hn)

theorem StandardSolution.not_exists_complete_bounded_terminal_limit
    (S : StandardSolution) (time : ℕ → ℝ) (p : E3)
    (htime : ∀ i, time i ∈ Ico (0 : ℝ) 1) (hlim : Tendsto time atTop (𝓝 1)) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => (S.val.pointedFlow.atTime (time i)).repoint p⟩
    ¬ ∃ P : MetricCompactLimit X,
      (∀ k, P.convergence.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      ∃ K : ℝ, ∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ K := by
  intro X hP
  obtain ⟨P, hcanonical, K, hK⟩ := hP
  have hdom (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : t ∈ S.val.domain := by
    apply (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
    rw [S.lifetime_eq_one]
    exact ⟨ht.1, ENNReal.ofReal_lt_one.mpr ht.2⟩
  have hscalar := S.val.scalar_time_mul_le_of_complete_terminal_limit time p
    (fun i => ⟨hdom _ (htime i), (htime i).2⟩) hlim P hcanonical K hK
  have hKpos : 0 < K + 1 := by
    have hh := hscalar (1 / 2) (by norm_num) p
    have hlo := S.val.one_le_scalar (1 / 2) (hdom _ (by norm_num)) p
    linarith
  obtain ⟨K₀, hK₀, hcurv₀⟩ := S.val.curvature_bound (1 / 2) (by norm_num)
    (by rw [S.lifetime_eq_one]; norm_num)
  let K₁ := max K₀ (200 * (K + 1))
  have hK₁ : 0 ≤ K₁ := hK₀.trans (le_max_left _ _)
  have hcurv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : E3,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (S.val.metric t) x 4
        (metricRm04 (S.val.metric t) x)) ≤ K₁ := by
    intro t ht x
    by_cases hearly : t ≤ 1 / 2
    · exact (hcurv₀ t ⟨ht.1, hearly⟩ x).trans (le_max_left _ _)
    have htpos : 0 < t := by linarith
    have hsc := hscalar t ⟨htpos, ht.2⟩ x
    have hlo := S.val.one_le_scalar t (hdom t ht) x
    have hu : metricScalarAt (S.val.metric t) x ≤ 2 * (K + 1) := by
      have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hearly) (by linarith : 0 ≤ metricScalarAt (S.val.metric t) x)
      nlinarith
    have hrm := S.val.normSq_rm_le_scalar_sq t (hdom t ht) x
    apply (Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩).trans (le_max_right K₀ _)
    nlinarith
  obtain ⟨delta, _hdelta, KR, _hKR, hext⟩ :=
    standard_closed_restart_extension_of_curvature_bound 1 K₁ (by norm_num) hK₁
  obtain ⟨G, H, Q, _hG, _hH, _hQmetric, _hQlifetime, hSQ, hstrict, _hcomp, _hcurv⟩ :=
    hext S.val (by simpa only [ENNReal.ofReal_one] using S.lifetime_eq_one) hcurv
  exact (not_lt_of_ge (S.property Q hSQ).1) hstrict

end DifferentialGeometry.PDE.RicciFlow
end
