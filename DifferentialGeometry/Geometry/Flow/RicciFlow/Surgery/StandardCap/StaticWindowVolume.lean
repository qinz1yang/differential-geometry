import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Metric.EmbeddingComposition
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Measure.OpenRestriction
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}


private local instance : MeasurableSpace ThreeSpace := borel ThreeSpace
private local instance : BorelSpace ThreeSpace := ⟨rfl⟩

private local instance (V : TopologicalSpace.Opens ThreeSpace) : MeasurableSpace V := borel V
private local instance (V : TopologicalSpace.Opens ThreeSpace) : BorelSpace V := ⟨rfl⟩
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
private local instance {B : ℝ} {hB : 0 < B} : SecondCountableTopology (InsertionQuotient hB) :=
  radialCapAttachment_secondCountableTopology transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : LocallyCompactSpace (InsertionQuotient hB) := by
  let : LocallyCompactSpace {x : ThreeSpace // ‖x‖ < transitionEnd + B} :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  exact (radialCapAttachmentHomeomorph transitionEnd_pos hB :
    InsertionQuotient hB ≃ₜ insertionBall B).isClosedEmbedding.locallyCompactSpace

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

theorem window_inner_bounds (heps : ε ≤ 1 / 2)
    {x : standardCapWindow D} (hx : ‖x.val‖ < D) (v : TangentSpace ThreeModel x) :
    (1 / 2 : ℝ) * (standardCapMetric.restrictOpen (standardCapWindow D)).inner x v v ≤
      w.windowMetric.inner x v v ∧
    w.windowMetric.inner x v v ≤
      (3 / 2 : ℝ) * (standardCapMetric.restrictOpen (standardCapWindow D)).inner x v v := by
  have hclose := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at hclose
  simp only [distance_zero] at hclose
  have hb := inner_bounds_of_metricDerivENormSupOn_lt
    (metric.restrictOpen (standardCapWindow D)) w.windowMetric hclose hx v
  rw [standardCapMetric_eq_metric]
  have hn := metric_inner_self_nonneg (metric.restrictOpen (standardCapWindow D)) x v
  constructor <;> nlinarith [hb.1, hb.2]

theorem volume_window_image_ge (heps : ε ≤ 1 / 2)
    {S : Set (standardCapWindow D)} (hS : MeasurableSet S)
    (hSD : S ⊆ {x : standardCapWindow D | ‖x.val‖ < D}) :
    ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure ThreeModel (standardCapWindow D)
        (standardCapMetric.restrictOpen (standardCapWindow D)) S ≤
    riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric) (w.window '' S) := by
  let g₀ := standardCapMetric.restrictOpen (standardCapWindow D)
  have hcomp (x : standardCapWindow D) (hx : x ∈ S) (v : TangentSpace ThreeModel x) :
      (scaleMetric (1 / 2 : ℝ) (by norm_num) g₀).inner x v v ≤
        1 * w.windowMetric.inner x v v := by
    rw [scaleMetric_inner, one_mul]
    exact (w.window_inner_bounds heps (hSD hx) v).1
  have hv := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    w.windowMetric (scaleMetric (1 / 2 : ℝ) (by norm_num) g₀) zero_lt_one hS hcomp
  rw [volume_scale_apply] at hv
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hv
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hv
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    w.windowMetric (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
    w.window w.properties.window_local w.properties.window_embedding.isEmbedding.injective
    (by
      intro x v z
      rw [scaleMetric_inner]
      exact w.window_inner x v z) hS
  rw [← heq]
  apply (mul_le_mul' ?_ le_rfl).trans hv
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
  apply ENNReal.ofReal_le_ofReal
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hp := Real.sqrt_nonneg (1 / 2 : ℝ)
  nlinarith

private theorem exists_window_partialDiffeomorph :
    ∃ Φ : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
        (InsertionQuotient (inv_pos.mpr d.precision_pos)) ∞,
      Φ.source = (standardCapWindow D : Set ThreeSpace) ∧
      Φ.target = range w.window ∧
      ∀ x : standardCapWindow D, Φ x.val = w.window x := by
  let U := standardCapWindow D
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ w.window :=
    w.properties.window_local
  let V := hlocal.image
  let e : Diffeomorph ThreeModel ThreeModel U V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hlocal
      w.window_smooth.isEmbedding.injective
  let x₀ : U := ⟨0, w.properties.window_tip_mem⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel U ⟨x₀⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e x₀⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  refine ⟨Φ, ?_, ?_, ?_⟩
  · ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (univ : Set V) ∧
      e.symm (iV.symm y) ∈ (univ : Set U))) ↔ y ∈ range w.window
    simp only [mem_univ, and_self, and_true, iV,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · intro x
    change (e (iU.symm x.val) : InsertionQuotient _) = w.window x
    rw [show iU.symm x.val = x from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
        ThreeModel U ⟨x₀⟩ x.property]
    rfl


private theorem window_image_subset_ball_of_partialDiffeomorph
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D)
    (F : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
      (InsertionQuotient (inv_pos.mpr d.precision_pos)) ∞)
    (hsource : (standardCapWindow D : Set ThreeSpace) ⊆ F.source)
    (hmap : ∀ x : standardCapWindow D, F x = w.window x) :
    w.window '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 4} ⊆
      riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
        w.data.tip ρ := by
  let gn := scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric
  have hzero : (0 : ThreeSpace) ∈ standardCapWindow D := by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith
  have htip : F 0 = w.data.tip := (hmap ⟨0, hzero⟩).trans (w.window_tip hzero)
  have hsub : riemannianClosedBallOf metric (0 : ThreeSpace) ρ ⊆ standardCapWindow D := by
    intro z hz
    change riemannianEDistOf metric 0 z ≤ ENNReal.ofReal ρ at hz
    rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hρ.le] at hz
    change ‖z‖ < D + 1
    linarith
  have hupper : ∀ z ∈ riemannianClosedBallOf metric (0 : ThreeSpace) ρ,
      ∀ v : TangentSpace ThreeModel z,
      gn.inner (F z) (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v) ≤
        (2 : ℝ)^2 * metric.inner z v v := by
    intro z hz v
    have hnorm : ‖z‖ ≤ ρ := by
      change riemannianEDistOf metric 0 z ≤ ENNReal.ofReal ρ at hz
      rwa [edist_zero, ENNReal.ofReal_le_ofReal_iff hρ.le] at hz
    let q : standardCapWindow D := ⟨z, hsub hz⟩
    have hd : mfderiv ThreeModel ThreeModel w.window q =
        mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z := by
      have hfun : (fun x : standardCapWindow D => F x) = w.window := funext hmap
      rw [← hfun]
      exact mfderiv_restrict_open (F : ThreeSpace → _) (standardCapWindow D) q
    have hb := (w.window_inner_bounds heps (x := q) (hnorm.trans_lt hρD) v).2
    rw [w.window_inner q v v, standardCapMetric_eq_metric] at hb
    change metricScalarAt g x₀ * w.data.outMetric.inner (w.window q)
      (mfderiv ThreeModel ThreeModel w.window q v)
      (mfderiv ThreeModel ThreeModel w.window q v) ≤ (3 / 2 : ℝ) * metric.inner z v v at hb
    rw [hd, ← hmap q] at hb
    change metricScalarAt g x₀ * w.data.outMetric.inner (F z)
      (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v)
      (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v) ≤ _
    exact hb.trans (mul_le_mul_of_nonneg_right (by norm_num) (metric_inner_self_nonneg metric z v))
  rintro _ ⟨x, hx, rfl⟩
  have hy : riemannianEDistOf metric 0 x.val < ENNReal.ofReal ρ := by
    rw [edist_zero]
    apply (ENNReal.ofReal_lt_ofReal_iff hρ).mpr
    exact hx.trans_lt (by linarith)
  have hd := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    metric gn F 0 x.val hρ (by norm_num : (0 : ℝ) < 2)
    (hsub.trans hsource) hupper hy
  rw [htip, hmap x] at hd
  apply hd.trans_lt
  calc ENNReal.ofReal 2 * riemannianEDistOf metric 0 x.val
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (ρ / 4) := by
        rw [edist_zero]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hx)
    _ = ENNReal.ofReal (ρ / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ < ENNReal.ofReal ρ := (ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith)

theorem window_image_subset_normalized_tip_ball
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    w.window '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 4} ⊆
      riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
        w.data.tip ρ := by
  obtain ⟨F, hsource, _, hmap⟩ := w.exists_window_partialDiffeomorph
  exact w.window_image_subset_ball_of_partialDiffeomorph heps hρ hρD F
    (hsource.symm ▸ Subset.rfl) hmap

theorem normalized_tip_ball_volume_ge
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall (0 : ThreeSpace) (ρ / 4)) ≤
    riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
      (riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
        w.data.tip ρ) := by
  let S := {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 4}
  have hS : MeasurableSet S :=
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet
  have hSD : S ⊆ {x : standardCapWindow D | ‖x.val‖ < D} := by
    intro x hx
    change ‖x.val‖ ≤ ρ / 4 at hx
    change ‖x.val‖ < D
    linarith
  have hv := w.volume_window_image_ge heps hS hSD
  have hK : MeasurableSet (Metric.closedBall (0 : ThreeSpace) (ρ / 4)) :=
    Metric.isClosed_closedBall.measurableSet
  have hKU : Metric.closedBall (0 : ThreeSpace) (ρ / 4) ⊆ standardCapWindow D := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    change ‖x‖ < D + 1
    linarith
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage
    metric (standardCapWindow D) hK hKU
  have hSpre : S = (Subtype.val : standardCapWindow D → ThreeSpace) ⁻¹'
      Metric.closedBall (0 : ThreeSpace) (ρ / 4) := by
    ext x
    simp only [S, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [standardCapMetric_eq_metric, hSpre, heq] at hv
  exact hv.trans (measure_mono (by
    simpa only [← hSpre] using w.window_image_subset_normalized_tip_ball heps hρ hρD))

theorem tip_ball_volume_ge
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    ENNReal.ofReal ((1 / 4 : ℝ) /
      (metricScalarAt g x₀ * Real.sqrt (metricScalarAt g x₀))) *
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall (0 : ThreeSpace) (ρ / 4)) ≤
    riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
      w.data.outMetric (riemannianBallOf w.data.outMetric w.data.tip
        (ρ / Real.sqrt (metricScalarAt g x₀))) := by
  let Q := metricScalarAt g x₀
  have hQ : 0 < Q := d.scalar_pos
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hmul : Real.sqrt Q * (ρ / Real.sqrt Q) = ρ := by field_simp
  have hball := riemannianBallOf_scaleMetric Q hQ w.data.outMetric w.data.tip
    (ρ / Real.sqrt Q)
  rw [hmul] at hball
  have hv := w.normalized_tip_ball_volume_ge heps hρ hρD
  change ENNReal.ofReal (1 / 4 : ℝ) * _ ≤
    riemannianVolumeMeasure ThreeModel _ (scaleMetric Q hQ w.data.outMetric) _ at hv
  rw [hball, volume_scale_apply] at hv
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hv
  have hpow : ENNReal.ofReal (Real.sqrt Q) ^ 3 = ENNReal.ofReal (Q * Real.sqrt Q) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
    congr 1
    rw [show Real.sqrt Q ^ 3 = Real.sqrt Q ^ 2 * Real.sqrt Q by ring,
      Real.sq_sqrt hQ.le]
  rw [hpow] at hv
  have hp : 0 < Q * Real.sqrt Q := mul_pos hQ hroot
  have hcancel : ENNReal.ofReal (Q * Real.sqrt Q) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  change ENNReal.ofReal ((1 / 4 : ℝ) / (Q * Real.sqrt Q)) * _ ≤ _
  rw [ENNReal.ofReal_div_of_pos hp]
  rw [← ENNReal.mul_div_right_comm]
  apply (ENNReal.div_le_iff hcancel ENNReal.ofReal_ne_top).mpr
  simpa only [mul_comm] using hv


end CanonicalStaticInsertionWitness


theorem exists_pos_le_normalized_tip_ball_volume {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k}
        {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → ρ < D →
        ENNReal.ofReal v ≤
          riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
            (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
            (riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
              w.data.tip ρ) := by
  let μ := riemannianVolumeMeasure ThreeModel ThreeSpace metric
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure metric
  have hpos : 0 < μ (Metric.ball (0 : ThreeSpace) (ρ / 4)) :=
    Metric.isOpen_ball.measure_pos μ ⟨0, Metric.mem_ball_self (by positivity)⟩
  obtain ⟨v, _, hv, hbound⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hvpos : 0 < v := ENNReal.ofReal_pos.mp hv
  refine ⟨v / 4, by positivity, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ε w heps hρD
  calc ENNReal.ofReal (v / 4)
      = ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal v := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
          congr 1
          ring
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) * μ (Metric.closedBall (0 : ThreeSpace) (ρ / 4)) :=
      mul_le_mul' le_rfl (hbound.le.trans (measure_mono Metric.ball_subset_closedBall))
    _ ≤ _ := w.normalized_tip_ball_volume_ge heps hρ hρD

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_standard_cap_coordinate_ball_volume_lower (R : ℝ) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ p : ThreeSpace, ‖p‖ ≤ R →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p (r / 4)) := by
  obtain ⟨c, C, hc, _, hb⟩ := Geometry.exists_compact_source_metric_ellipticity
    (f := id) (U := univ) metric isOpen_univ contMDiff_id.contMDiffOn
    (isCompact_closedBall (0 : ThreeSpace) (R + 1)) (subset_univ _)
    (by intro x hx; simpa using Function.injective_id)
  have hbound (x : ThreeSpace) (hx : ‖x‖ ≤ R + 1) (v : ThreeSpace) :
      c * ‖v‖ ^ 2 ≤ metric.inner x v v := by
    have hid : mfderiv ThreeModel ThreeModel (@id ThreeSpace) x v = v := by
      rw [mfderiv_id]
      rfl
    simpa only [hid, id_eq] using (hb x (by simpa using hx) v).1
  let ν := Real.sqrt c ^ 3 * (Real.pi * 4 / 3) / 4 ^ 3
  have hν : 0 < ν := by dsimp [ν]; positivity
  refine ⟨ν, hν, ?_⟩
  intro p hp r hr hr1
  let gE : SmoothRiemannianMetric ThreeModel ThreeSpace := euclideanMetric (E := ThreeSpace)
  let gC := scaleMetric c hc gE
  have hS : MeasurableSet (Metric.closedBall p (r / 4)) := Metric.isClosed_closedBall.measurableSet
  have hcomp : ∀ x ∈ Metric.closedBall p (r / 4), ∀ v : TangentSpace ThreeModel x,
      gC.inner x v v ≤ 1 * metric.inner x v v := by
    intro x hx v
    have hxR : ‖x‖ ≤ R + 1 := by
      have hxp : ‖x - p‖ ≤ r / 4 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
      have htri : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := norm_le_norm_sub_add x p
      linarith
    change c * @inner ℝ ThreeSpace _ (show ThreeSpace from v) (show ThreeSpace from v) ≤
      1 * metric.inner x v v
    rw [real_inner_self_eq_norm_sq, one_mul]
    exact hbound x hxR v
  have hvol := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le metric gC one_pos hS hcomp
  have hlow : riemannianVolumeMeasure ThreeModel ThreeSpace gC
      (Metric.closedBall p (r / 4)) ≤
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p (r / 4)) := by
    simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using hvol
  have heq : riemannianVolumeMeasure ThreeModel ThreeSpace gC
      (Metric.closedBall p (r / 4)) = ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 := by
    rw [volume_scale_apply]
    rw [show gE = euclideanMetric (E := ThreeSpace) from rfl,
      riemannianVolumeMeasure_euclideanMetric]
    have hv : (volume : Measure ThreeSpace) (Metric.closedBall p (r / 4)) =
        ENNReal.ofReal (r / 4) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
      have hv := InnerProductSpace.volume_closedBall_of_dim_odd (E := ThreeSpace) (k := 1)
        (by simp [ThreeSpace]) p (r / 4)
      rw [hv]
      norm_num [Nat.doubleFactorial]
    rw [hv]
    rw [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg c), ← ENNReal.ofReal_pow (by positivity : 0 ≤ r / 4),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r / 4) ^ 3),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.sqrt c ^ 3),
      ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hν.le]
    congr 1
    dsimp only [ν]
    ring
  exact heq.symm.le.trans hlow


namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

private theorem window_image_subset_normalized_ball
    (heps : ε ≤ 1 / 2) (p : standardCapWindow D) {r : ℝ} (hr : 0 < r)
    (hmargin : ‖p.val‖ + r < D) :
    w.window '' {x : standardCapWindow D | dist x.val p.val ≤ r / 4} ⊆
      riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
        (w.window p) r := by
  let gn := scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric
  let ge := DifferentialGeometry.Geometry.standardEuclideanMetric ThreeSpace
  have hed (x y : ThreeSpace) : riemannianEDistOf ge x y = edist x y :=
    DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric x y
  obtain ⟨F, hsource, _, hmap⟩ := exists_window_partialDiffeomorph w
  have hnorm {z : ThreeSpace} (hz : z ∈ riemannianClosedBallOf ge p.val r) : ‖z‖ < D := by
    have hdist : dist z p.val ≤ r := by
      change riemannianEDistOf ge p.val z ≤ ENNReal.ofReal r at hz
      rw [hed, edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le] at hz
      rwa [dist_comm]
    have hn : ‖z‖ ≤ ‖p.val‖ + ‖z - p.val‖ := by
      calc
        ‖z‖ = ‖p.val + (z - p.val)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p.val‖ + ‖z - p.val‖ := norm_add_le _ _
    exact hn.trans_lt (by
      rw [← dist_eq_norm]
      linarith)
  have hsub : riemannianClosedBallOf ge p.val r ⊆ standardCapWindow D := by
    intro z hz
    change ‖z‖ < D + 1
    exact (hnorm hz).trans (by linarith)
  have hupper : ∀ z ∈ riemannianClosedBallOf ge p.val r, ∀ v : TangentSpace ThreeModel z,
      gn.inner (F z) (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z v) ≤
      (2 : ℝ)^2 * ge.inner z v v := by
    intro z hz v
    let q : standardCapWindow D := ⟨z, hsub hz⟩
    have hd : mfderiv ThreeModel ThreeModel w.window q =
        mfderiv ThreeModel ThreeModel (F : ThreeSpace → _) z := by
      have hfun : (fun x : standardCapWindow D => F x) = w.window := funext hmap
      rw [← hfun]
      exact mfderiv_restrict_open (F : ThreeSpace → _) (standardCapWindow D) q
    have hb := (w.window_inner_bounds heps (x := q) (show ‖q.val‖ < D from hnorm hz) v).2
    rw [w.window_inner q v v, standardCapMetric_eq_metric] at hb
    change metricScalarAt g x₀ * w.data.outMetric.inner (w.window q)
      (mfderiv ThreeModel ThreeModel w.window q v)
      (mfderiv ThreeModel ThreeModel w.window q v) ≤ (3 / 2 : ℝ) * metric.inner z v v at hb
    rw [hd, ← hmap q] at hb
    have hmetricNorm : metric.inner z v v ≤ ‖(show ThreeSpace from v)‖ ^ 2 :=
      metric_inner_le z v
    apply hb.trans
    change (3 / 2 : ℝ) * metric.inner z v v ≤
      2 ^ 2 * @inner ℝ ThreeSpace _ (show ThreeSpace from v) (show ThreeSpace from v)
    rw [real_inner_self_eq_norm_sq]
    nlinarith [hmetricNorm, sq_nonneg ‖(show ThreeSpace from v)‖]
  rintro _ ⟨x, hx, rfl⟩
  have hy : riemannianEDistOf ge p.val x.val < ENNReal.ofReal r := by
    rw [hed, edist_dist]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    rw [dist_comm]
    exact hx.trans_lt (by linarith)
  have hd := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    ge gn F p.val x.val hr (by norm_num : (0 : ℝ) < 2)
    (by rw [hsource]; exact hsub) hupper hy
  rw [hmap p, hmap x] at hd
  apply hd.trans_lt
  calc
    ENNReal.ofReal 2 * riemannianEDistOf ge p.val x.val ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) := by
      rw [hed, edist_dist, dist_comm]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hx)
    _ = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)



theorem normalized_window_ball_volume_ge
    (heps : ε ≤ 1 / 2) (p : standardCapWindow D) {r : ℝ} (hr : 0 < r)
    (hmargin : ‖p.val‖ + r < D) :
    ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p.val (r / 4)) ≤
    riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
      (riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
        (w.window p) r) := by
  let S : Set (standardCapWindow D) := {x | dist x.val p.val ≤ r / 4}
  have hS : MeasurableSet S := (isClosed_le (continuous_subtype_val.dist continuous_const)
    continuous_const).measurableSet
  have hSD : S ⊆ {x : standardCapWindow D | ‖x.val‖ < D} := by
    intro x hx
    have hn := norm_le_norm_sub_add x.val p.val
    change dist x.val p.val ≤ r / 4 at hx
    rw [dist_eq_norm] at hx
    change ‖x.val‖ < D
    linarith
  have himage : Metric.closedBall p.val (r / 4) ⊆ standardCapWindow D := by
    intro x hx
    have hn := norm_le_norm_sub_add x p.val
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    change ‖x‖ < D + 1
    linarith
  have hvol : riemannianVolumeMeasure ThreeModel (standardCapWindow D)
      (standardCapMetric.restrictOpen (standardCapWindow D)) S =
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p.val (r / 4)) := by
    rw [standardCapMetric_eq_metric]
    exact DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      metric (standardCapWindow D) Metric.isClosed_closedBall.measurableSet himage
  rw [← hvol]
  exact (w.volume_window_image_ge heps hS hSD).trans
    (measure_mono (window_image_subset_normalized_ball w heps p hr hmargin))

end CanonicalStaticInsertionWitness

theorem exists_uniform_normalized_window_ball_volume_lower (R : ℝ) :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → ∀ p : standardCapWindow D, ‖p.val‖ ≤ R →
        ∀ r : ℝ, 0 < r → r ≤ 1 → ‖p.val‖ + r < D →
          ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
              (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
              (riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
                (w.window p) r) := by
  obtain ⟨v, hv, hvol⟩ := exists_uniform_standard_cap_coordinate_ball_volume_lower R
  refine ⟨v / 4, by positivity, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ε w heps p hp r hr hr1 hmargin
  have h := (mul_le_mul' (le_rfl : ENNReal.ofReal (1 / 4 : ℝ) ≤ _) (hvol p.val hp r hr hr1)).trans
    (CanonicalStaticInsertionWitness.normalized_window_ball_volume_ge w heps p hr hmargin)
  have heq : ENNReal.ofReal (v / 4) * ENNReal.ofReal r ^ 3 =
      ENNReal.ofReal (1 / 4 : ℝ) * (ENNReal.ofReal v * ENNReal.ofReal r ^ 3) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    congr 2
    ring
  exact heq.trans_le h


section

open DifferentialGeometry.Topology.Manifold

theorem exists_uniform_window_isometric_ball_capture (R₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {η : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ η k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
      ε ≤ 1 / 2 → R₀ + 1 < D →
      ∀ {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold ThreeModel ∞ N] [T2Space N]
        (gN : SmoothRiemannianMetric ThreeModel N)
        (F : InsertionQuotient (inv_pos.mpr d.precision_pos) → N),
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ F → Injective F →
      (∀ y v z, gN.inner (F y) (mfderiv ThreeModel ThreeModel F y v)
        (mfderiv ThreeModel ThreeModel F y z) = w.data.outMetric.inner y v z) →
      ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ →
        riemannianBallOf (scaleMetric (metricScalarAt g x₀) d.scalar_pos gN)
            (F (w.window p)) δ ⊆
          (F ∘ w.window) '' {x : standardCapWindow D | dist x.val p.val ≤ 1} := by
  obtain ⟨Λ, hΛ, hbound⟩ := exists_uniform_window_ellipticity (R₀ + 1)
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  refine ⟨1 / Λ, div_pos zero_lt_one hΛpos, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ η k d A hA D m ε w heps hRD
    N _ _ _ _ gN F hF hiF hisom p hp
  let Φ := F ∘ w.window
  let gQ := scaleMetric (metricScalarAt g x₀) d.scalar_pos gN
  let ge := DifferentialGeometry.Geometry.standardEuclideanMetric ThreeSpace
  have hed (x y : ThreeSpace) : riemannianEDistOf ge x y = edist x y :=
    DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric x y
  have hball : riemannianClosedBallOf ge p.val 1 = Metric.closedBall p.val 1 := by
    ext x
    change riemannianEDistOf ge p.val x ≤ ENNReal.ofReal 1 ↔ dist x p.val ≤ 1
    rw [hed, edist_dist, ENNReal.ofReal_le_ofReal_iff zero_le_one, dist_comm]
  have hnorm {x : ThreeSpace} (hx : x ∈ riemannianClosedBallOf ge p.val 1) :
      ‖x‖ ≤ R₀ + 1 := by
    have hd : dist x p.val ≤ 1 := by simpa only [hball, Metric.mem_closedBall] using hx
    have hn := norm_le_norm_sub_add x p.val
    rw [← dist_eq_norm] at hn
    linarith
  have hcpt : IsCompact (riemannianClosedBallOf ge p.val 1) :=
    hball ▸ isCompact_closedBall p.val 1
  have hsub : riemannianClosedBallOf ge p.val 1 ⊆ standardCapWindow D := by
    intro x hx
    change ‖x‖ < D + 1
    linarith [hnorm hx]
  have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    fun x => (w.properties.window_local x).comp ThreeModel N (hF (w.window x))
  have hiΦ : Injective Φ := hiF.comp w.window_smooth.isEmbedding.injective
  have hin (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
      gQ.inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x z) = w.windowMetric.inner x v z := by
    rw [scaleMetric_inner, w.window_inner]
    apply congrArg (fun a => metricScalarAt g x₀ * a)
    exact metric_inner_comp_of_isometry w.data.outMetric gN F hF.contMDiff hisom
      w.window w.window_smooth.contMDiff x v z
  have hlow (x : standardCapWindow D)
      (hx : x.val ∈ riemannianClosedBallOf ge p.val 1)
      (v : TangentSpace ThreeModel x) :
      ge.inner x.val v v ≤ Λ ^ 2 * gQ.inner (Φ x)
        (mfderiv ThreeModel ThreeModel Φ x v) (mfderiv ThreeModel ThreeModel Φ x v) := by
    rw [hin]
    have hb := (hbound w heps hRD x (hnorm hx) v).1
    rw [← w.window_inner x v v] at hb
    have hh : ‖(show ThreeSpace from v)‖ ^ 2 ≤ Λ * w.windowMetric.inner x v v :=
      (inv_mul_le_iff₀ hΛpos).mp hb
    have hΛsq : Λ ≤ Λ ^ 2 := le_self_pow₀ hΛ (by decide)
    have hnn : 0 ≤ w.windowMetric.inner x v v := metric_inner_self_nonneg w.windowMetric x v
    have heuc : ge.inner x.val v v = ‖(show ThreeSpace from v)‖ ^ 2 := by
      change @inner ℝ ThreeSpace _ (show ThreeSpace from v) (show ThreeSpace from v) = _
      exact real_inner_self_eq_norm_sq _
    rw [heuc]
    exact hh.trans (mul_le_mul_of_nonneg_right hΛsq hnn)
  have hcapture := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    gQ ge (standardCapWindow D) Φ hΦ hiΦ p zero_lt_one hΛpos hcpt hsub hlow
  apply hcapture.trans
  apply image_mono
  intro x hx
  simpa only [hball, Metric.mem_closedBall] using hx

end

end DifferentialGeometry.PDE.RicciFlow.StandardCap
