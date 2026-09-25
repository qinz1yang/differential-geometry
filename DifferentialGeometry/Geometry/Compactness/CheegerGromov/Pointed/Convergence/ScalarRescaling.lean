import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem exists_source_scalar_diagonal
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (f : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, uE, uH} I)
    (maps : PointedRiemannianConvergenceMaps X L f)
    (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (x : ℕ → L.M) (K : ℕ → Set L.M) (hK : ∀ n, IsCompact (K n))
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ n, K n ⊆ maps.source (k n)) ∧
      (∀ n, 1 ≤ metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n))) ∧
      (∀ n, metricScalarAt L.metric (x n) / 2 ≤
        metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n))) ∧
      Tendsto (fun n => metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n)) /
        metricScalarAt L.metric (x n)) atTop (𝓝 1) ∧
      ∀ n, ∀ y ∈ K n, ∀ v : TangentSpace I y,
        (1 - 1 / ((n : ℝ) + 2)) * L.metric.inner y v v ≤
          (X.obj (f (k n))).metric.inner (maps.partialDiffeomorph (k n) y)
            (mfderiv I I (maps.partialDiffeomorph (k n)) y v)
            (mfderiv I I (maps.partialDiffeomorph (k n)) y v) ∧
        (X.obj (f (k n))).metric.inner (maps.partialDiffeomorph (k n) y)
            (mfderiv I I (maps.partialDiffeomorph (k n)) y v)
            (mfderiv I I (maps.partialDiffeomorph (k n)) y v) ≤
          (1 + 1 / ((n : ℝ) + 2)) * L.metric.inner y v v := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    intro hdim
    have hz := metricScalarAt_eq_zero_of_finrank_eq_zero L.metric hdim (x 0)
    linarith [hQ 0]⟩
  have heps (n : ℕ) : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have hhalf (n : ℕ) : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have href : ∀ i, (conv.domain i).referenceMetric = (conv.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    rfl
  have hscalar (n : ℕ) : ∀ᶠ i in atTop,
      |metricScalarAt (X.obj (f i)).metric (maps.partialDiffeomorph i (x n)) /
        metricScalarAt L.metric (x n) - 1| < 1 / ((n : ℝ) + 2) := by
    have hq : metricScalarAt L.metric (x n) ≠ 0 := by linarith [hQ n]
    have hconv : ∀ K : Set L.M, IsCompact K →
        metricSourceConvergesOn maps (CanonicalMetricCompactness.canonicalSourceData maps) K 2 := by
      intro K hK
      have heq : conv.domain = CanonicalMetricCompactness.canonicalSourceData maps := funext hcanonical
      rw [← heq]
      exact conv.converges K hK 2
    have ht := (pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence hconv
      (show Tendsto (fun _ : ℕ => x n) atTop (𝓝 (x n)) from tendsto_const_nhds)).div_const
        (metricScalarAt L.metric (x n))
    rw [div_self hq] at ht
    have hd := Metric.tendsto_nhds.mp ht (1 / ((n : ℝ) + 2)) (heps n)
    simpa only [Real.dist_eq, PointedRiemannianConvergenceMaps.map] using hd
  have hall (n : ℕ) : ∀ᶠ i in atTop, K n ⊆ maps.source i ∧
      |metricScalarAt (X.obj (f i)).metric (maps.partialDiffeomorph i (x n)) /
        metricScalarAt L.metric (x n) - 1| < 1 / ((n : ℝ) + 2) ∧
      ∀ y ∈ K n, ∀ v : TangentSpace I y,
        (1 - 1 / ((n : ℝ) + 2)) * L.metric.inner y v v ≤
          (X.obj (f i)).metric.inner (maps.partialDiffeomorph i y)
            (mfderiv I I (maps.partialDiffeomorph i) y v)
            (mfderiv I I (maps.partialDiffeomorph i) y v) ∧
        (X.obj (f i)).metric.inner (maps.partialDiffeomorph i y)
            (mfderiv I I (maps.partialDiffeomorph i) y v)
            (mfderiv I I (maps.partialDiffeomorph i) y v) ≤
          (1 + 1 / ((n : ℝ) + 2)) * L.metric.inner y v v := by
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
      conv href (K n) (hK n) _ (heps n)
    filter_upwards [hscalar n, eventually_ge_atTop N] with i hs hiN
    refine ⟨(hN i hiN).1, hs, ?_⟩
    intro y hy v
    have hh := abs_le.mp ((hN i hiN).2 y hy v)
    change - (1 / ((n : ℝ) + 2) * L.metric.inner y v v) ≤
      (X.obj (f i)).metric.inner (maps.partialDiffeomorph i y)
        (mfderiv I I (maps.partialDiffeomorph i) y v)
        (mfderiv I I (maps.partialDiffeomorph i) y v) - L.metric.inner y v v ∧
      (X.obj (f i)).metric.inner (maps.partialDiffeomorph i y)
        (mfderiv I I (maps.partialDiffeomorph i) y v)
        (mfderiv I I (maps.partialDiffeomorph i) y v) - L.metric.inner y v v ≤
        1 / ((n : ℝ) + 2) * L.metric.inner y v v at hh
    constructor <;> linarith only [hh.1, hh.2]
  choose N hN using fun n => eventually_atTop.mp (hall n)
  obtain ⟨k, hk, hkN⟩ := exists_strictMono_ge N
  have hh (n : ℕ) := hN n (k n) (hkN n)
  have hbound (n : ℕ) : metricScalarAt L.metric (x n) / 2 ≤
      metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n)) := by
    have hlow := (abs_lt.mp (hh n).2.1).1
    have hq : 0 < metricScalarAt L.metric (x n) := by linarith [hQ n]
    have hr : 1 / 2 ≤ metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n)) /
        metricScalarAt L.metric (x n) := by linarith [hhalf n]
    have hm := (le_div_iff₀ hq).mp hr
    linarith
  refine ⟨k, hk, fun n => (hh n).1, fun n => ?_, hbound, ?_, fun n => (hh n).2.2⟩
  · linarith [hbound n, hQ n]
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by
      simpa only [Real.dist_eq] using (hh n).2.1.le) hzero

theorem exists_scalar_rescaled_source_comparison
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (f : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, uE, uH} I)
    (maps : PointedRiemannianConvergenceMaps X L f)
    (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (W : TopologicalSpace.Opens L.M) (x : ℕ → W)
    {R : ℝ} (hR : 0 < R)
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
      (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∃ hq : ∀ n, 1 ≤ metricScalarAt (X.obj (f (k n))).metric
        (maps.partialDiffeomorph (k n) (x n : L.M)),
      let q : ℕ → ℝ := fun n => metricScalarAt (X.obj (f (k n))).metric
        (maps.partialDiffeomorph (k n) (x n : L.M))
      let G := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (X.obj (f (k n))).metric
      let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) W ⟨x 0⟩
      let F := fun n => inc.trans (maps.partialDiffeomorph (k n))
      Tendsto (fun n => q n / metricScalarAt L.metric (x n : L.M)) atTop (𝓝 1) ∧
      ∀ n, IsCompact (riemannianClosedBallOf (G n) (x n) R) ∧
        riemannianClosedBallOf (G n) (x n) R ⊆ (F n).source ∧
        (∀ y ∈ riemannianClosedBallOf (G n) (x n) R, ∀ v : TangentSpace I y,
          (1 - 1 / ((n : ℝ) + 2)) * (G n).inner y v v ≤
            (H n).inner (F n y) (mfderiv I I (F n) y v) (mfderiv I I (F n) y v) ∧
          (H n).inner (F n y) (mfderiv I I (F n) y v) (mfderiv I I (F n) y v) ≤
            (1 + 1 / ((n : ℝ) + 2)) * (G n).inner y v v) ∧
        riemannianClosedBallOf (H n) (F n (x n)) (R / 4) ⊆
          (F n) '' riemannianClosedBallOf (G n) (x n) R ∧
        (∀ y ∈ riemannianClosedBallOf (G n) (x n) (R / 8),
          ∀ z ∈ riemannianClosedBallOf (G n) (x n) (R / 8),
            Real.sqrt (1 - 1 / ((n : ℝ) + 2)) * (riemannianEDistOf (G n) y z).toReal ≤
              (riemannianEDistOf (H n) (F n y) (F n z)).toReal ∧
            (riemannianEDistOf (H n) (F n y) (F n z)).toReal ≤
              Real.sqrt (1 + 1 / ((n : ℝ) + 2)) * (riemannianEDistOf (G n) y z).toReal) := by
  let K := fun n => riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
    (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M)))
  obtain ⟨k, hk, hsource, hq, hhalf, hratio, hcmp⟩ :=
    exists_source_scalar_diagonal X f L maps conv hcanonical
      (fun n => (x n : L.M)) (fun n => Subtype.val '' K n)
      (fun n => (hcompact n).image continuous_subtype_val) hQ
  refine ⟨k, hk, hq, ?_⟩
  dsimp only
  refine ⟨hratio, ?_⟩
  intro n
  let q := metricScalarAt (X.obj (f (k n))).metric (maps.partialDiffeomorph (k n) (x n : L.M))
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one (hq n)
  let G := scaleMetric q hqp (L.metric.restrictOpen W)
  let H := scaleMetric q hqp (X.obj (f (k n))).metric
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) W ⟨x 0⟩
  let F := inc.trans (maps.partialDiffeomorph (k n))
  let eta := 1 / ((n : ℝ) + 2)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaHalf : eta ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hQp : 0 < metricScalarAt L.metric (x n : L.M) := by linarith [hQ n]
  have hsqp : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have hsQp : 0 < Real.sqrt (metricScalarAt L.metric (x n : L.M)) := Real.sqrt_pos.mpr hQp
  have hsqrt : Real.sqrt (metricScalarAt L.metric (x n : L.M)) ≤ 2 * Real.sqrt q := by
    nlinarith only [Real.sq_sqrt hQp.le, Real.sq_sqrt hqp.le, hhalf n, hsQp, hsqp]
  have hrad : R / Real.sqrt q ≤ 4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M)) := by
    apply (div_le_div_iff₀ hsqp hsQp).mpr
    nlinarith only [hsqrt, hR, hsqp]
  have hball : riemannianClosedBallOf G (x n) R =
      riemannianClosedBallOf (L.metric.restrictOpen W) (x n) (R / Real.sqrt q) := by
    conv_lhs => rw [show R = Real.sqrt q * (R / Real.sqrt q) by field_simp]
    exact riemannianClosedBallOf_scaleMetric q hqp _ _ _
  have hsub : riemannianClosedBallOf G (x n) R ⊆ K n := by
    rw [hball]
    exact riemannianClosedBallOf_mono _ _ hrad
  have hclosed : IsClosed (riemannianClosedBallOf G (x n) R) :=
    isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist G (x n))
      continuous_const
  have hcpt : IsCompact (riemannianClosedBallOf G (x n) R) :=
    (hcompact n).of_isClosed_subset hclosed hsub
  have hsrc : riemannianClosedBallOf G (x n) R ⊆ F.source := by
    intro y hy
    change y ∈ (inc.trans (maps.partialDiffeomorph (k n))).source
    rw [PartialDiffeomorph.trans_source]
    exact ⟨mem_univ _, hsource n ⟨y, hsub hy, rfl⟩⟩
  have hmetric : ∀ y ∈ riemannianClosedBallOf G (x n) R, ∀ v : TangentSpace I y,
      (1 - eta) * G.inner y v v ≤ H.inner (F y)
        (mfderiv I I F y v) (mfderiv I I F y v) ∧
      H.inner (F y) (mfderiv I I F y v) (mfderiv I I F y v) ≤
        (1 + eta) * G.inner y v v := by
    intro y hy v
    have hm : (y : L.M) ∈ maps.source (k n) := hsource n ⟨y, hsub hy, rfl⟩
    have hd : mfderiv I I F y v =
        mfderiv I I (maps.partialDiffeomorph (k n)) (y : L.M) v := by
      have hd := mfderiv_comp y
        ((maps.partialDiffeomorph (k n)).mdifferentiableAt (by simp) hm)
        (hasMFDerivAt_subtype_val (I := I) W y).mdifferentiableAt
      rw [mfderiv_subtype_val] at hd
      exact DFunLike.congr_fun hd v
    have hh := hcmp n y ⟨y, hsub hy, rfl⟩ v
    change (1 - eta) * (q * L.metric.inner (y : L.M) v v) ≤
      q * (X.obj (f (k n))).metric.inner (F y)
        (mfderiv I I F y v) (mfderiv I I F y v) ∧
      q * (X.obj (f (k n))).metric.inner (F y)
        (mfderiv I I F y v) (mfderiv I I F y v) ≤
      (1 + eta) * (q * L.metric.inner (y : L.M) v v)
    have hvalue : F y = maps.partialDiffeomorph (k n) (y : L.M) := rfl
    rw [hd, hvalue]
    dsimp only [eta]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 hqp.le using 1 <;> ac_rfl
    · convert mul_le_mul_of_nonneg_left hh.2 hqp.le using 1 <;> ac_rfl
  refine ⟨hcpt, hsrc, hmetric, ?_, ?_⟩
  · apply DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower G H F (x n) hR
      (by norm_num : 0 < (2 : ℝ)) (show R / 4 < R / 2 by linarith) hcpt hsrc
    intro y hy v
    have hg : 0 ≤ G.inner y v v := metric_inner_self_nonneg G _ _
    have hh := hmetric y hy v
    change G.inner y v v ≤ (2 : ℝ) ^ 2 * H.inner (F y)
      (mfderiv I I F y v) (mfderiv I I F y v)
    have he := mul_le_mul_of_nonneg_right hetaHalf hg
    have ht := metric_inner_self_nonneg H (F y) (mfderiv I I F y v)
    nlinarith only [hh.1, he, ht]
  · apply crossModel_toReal_transfer G H F (x n) hR heta.le (by linarith) (by positivity)
      hcpt hsrc hmetric
    have hplus : Real.sqrt (1 + eta) ≤ 3 / 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> linarith
    have hminus : 2 / 3 ≤ Real.sqrt (1 - eta) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    nlinarith only [mul_le_mul_of_nonneg_right hplus (show 0 ≤ 3 * (R / 8) by positivity),
      mul_le_mul_of_nonneg_right hminus hR.le, hR]

end DifferentialGeometry.CheegerGromovCompactness
