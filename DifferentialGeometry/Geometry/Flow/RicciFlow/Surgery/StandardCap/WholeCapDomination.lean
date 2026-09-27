import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionVolume
import DifferentialGeometry.Geometry.Neck.InsertionOrientation
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure MeasureTheory
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance : ChartedSpace (EuclideanHalfSpace 3) Cap := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞ Cap := closedBall_isManifold transitionEnd_pos
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩
private local instance (U : Opens E3) : MeasurableSpace U := borel U
private local instance (U : Opens E3) : BorelSpace U := ⟨rfl⟩
private local instance (U : Opens E3) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB
private local instance quotientSecondCountable {B : ℝ} {hB : 0 < B} :
    SecondCountableTopology (InsertionQuotient hB) := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
private local instance quotientLocallyCompact {B : ℝ} {hB : 0 < B} :
    LocallyCompactSpace (InsertionQuotient hB) := by
  let : LocallyCompactSpace {x : E3 // ‖x‖ < transitionEnd + B} :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  exact (radialCapAttachmentHomeomorph transitionEnd_pos hB : InsertionQuotient hB ≃ₜ insertionBall B).isClosedEmbedding.locallyCompactSpace
private local instance quotientMeasurable {B : ℝ} {hB : 0 < B} :
    MeasurableSpace (InsertionQuotient hB) := borel (InsertionQuotient hB)
private local instance quotientBorel {B : ℝ} {hB : 0 < B} :
    BorelSpace (InsertionQuotient hB) := ⟨rfl⟩

theorem exists_wholeCap_metric_domination (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ,
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        let j := adjunctionCell (radialCapBoundary transitionEnd_pos)
          (retainedBoundary (inv_pos.mpr d.precision_pos))
        ∀ (x : Cap) (v : TangentSpace (𝓡∂ 3) x),
          (scaleMetric (metricScalarAt g x₀) d.scalar_pos
            (d.oriented.positiveSideInsertionMetric hA hAB)).inner (j x)
            (mfderiv (𝓡∂ 3) (𝓡 3) j x v) (mfderiv (𝓡∂ 3) (𝓡 3) j x v) ≤
          2 * metric.inner x.val
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v) := by
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := exists_normalizedDatum_insertedMetric_ball_error_lt
    A hA 0 (by norm_num) 0 (1 / 2) (by norm_num)
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, _, hb⟩ := hmod δ hδ hle
  refine ⟨hAB, ?_⟩
  intro k E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  have hn := hb k (Nat.zero_le k) g x₀ d.oriented
  dsimp only
  intro x v
  rw [d.oriented.positiveSideInsertionMetric_normalization, insertedQuotientMetric_cap]
  let q : insertionBall δ⁻¹ := ⟨x.val, x.property.trans_lt
    (lt_add_of_pos_right transitionEnd (inv_pos.mpr hδ))⟩
  let u : TangentSpace (𝓡 3) q := mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v
  have hq : q ∈ {z : insertionBall δ⁻¹ | ‖z.val‖ ≤ transitionEnd + 0} := by
    change ‖x.val‖ ≤ transitionEnd + 0
    simpa only [add_zero] using x.property
  have hu := (inner_bounds_of_metricDerivENormSupOn_lt
    (metric.restrictOpen (insertionBall δ⁻¹))
    (insertedMetric hA hAB d.oriented.controlledMetric_cylinder_lower.1 d.oriented.controlledMetric)
    hn hq u).2
  have hnonneg := metric_inner_self_nonneg (metric.restrictOpen (insertionBall δ⁻¹)) q u
  change (insertedMetric hA hAB d.oriented.controlledMetric_cylinder_lower.1 d.oriented.controlledMetric).inner q u u ≤
    2 * (metric.restrictOpen (insertionBall δ⁻¹)).inner q u u
  linarith

private theorem volume_scale_factor (Q : ℝ) (hQ : 0 < Q) :
    ENNReal.ofReal (Real.sqrt Q⁻¹) ^ 3 = ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
  congr 1
  calc
    (Real.sqrt Q⁻¹) ^ 3 = (Q⁻¹ ^ (1 / 2 : ℝ)) ^ (3 : ℕ) := by rw [Real.sqrt_eq_rpow]
    _ = Q⁻¹ ^ ((1 / 2 : ℝ) * 3) := (Real.rpow_mul_natCast (inv_nonneg.mpr hQ.le) _ 3).symm
    _ = Q ^ (-((1 / 2 : ℝ) * 3)) := (Real.rpow_neg_eq_inv_rpow Q _).symm
    _ = Q ^ (-3 / 2 : ℝ) := by congr 1; ring

private theorem two_le_volume_constant : (2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by
  have h : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  simpa only [Real.rpow_one] using h

theorem exists_wholeCap_metric_and_volume_bounds (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ,
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        let j := adjunctionCell (radialCapBoundary transitionEnd_pos)
          (retainedBoundary (inv_pos.mpr d.precision_pos))
        let out := d.oriented.positiveSideInsertionMetric hA hAB
        (∀ (x : Cap) (v : TangentSpace (𝓡∂ 3) x),
          (scaleMetric (metricScalarAt g x₀) d.scalar_pos out).inner (j x)
            (mfderiv (𝓡∂ 3) (𝓡 3) j x v) (mfderiv (𝓡∂ 3) (𝓡 3) j x v) ≤
          2 * metric.inner x.val
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
            (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)) ∧
        riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos)) out (range j) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (3 / 2 : ℝ) * (metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
            riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  obtain ⟨δd, hδd, hdhalf, hd⟩ := exists_wholeCap_metric_domination A hA
  obtain ⟨δv, hδv, _, hv⟩ := exists_normalizedDatum_positiveSideInsertionMetric_cap_volume_bound A hA
  refine ⟨min δd δv, lt_min hδd hδv, (min_le_left _ _).trans_lt hdhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hd⟩ := hd δ hδ (hle.trans (min_le_left _ _))
  obtain ⟨_, hv⟩ := hv δ hδ (hle.trans (min_le_right _ _))
  refine ⟨hAB, ?_⟩
  intro k E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  refine ⟨hd k g x₀ d, ?_⟩
  have hvol := hv k g x₀ d.oriented
  rw [volume_scale_factor _ d.scalar_pos] at hvol
  have hcoeff : ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) * 2 ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 / 2 : ℝ) * (metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    calc
      _ ≤ ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
          ENNReal.ofReal ((2 : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_le_mul' le_rfl (by simpa using ENNReal.ofReal_le_ofReal two_le_volume_constant)
      _ = _ := mul_comm _ _
  exact (hvol.trans_eq (mul_assoc _ _ _).symm).trans (mul_le_mul' hcoeff le_rfl)
end DifferentialGeometry.PDE.RicciFlow.StandardCap
