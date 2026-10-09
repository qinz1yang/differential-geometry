import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse
import DifferentialGeometry.Geometry.Measure.PullbackOpen
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Measure DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩
private local instance (U : Opens E3) : MeasurableSpace U := borel U
private local instance (U : Opens E3) : BorelSpace U := ⟨rfl⟩
private local instance (U : Opens E3) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
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

private theorem original_cap_range {B : ℝ} (hB : 0 < B) :
    range (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) =
      (radialCapAttachmentDiffeomorph transitionEnd_pos hB) ⁻¹'
        {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd} := by
  let D : InsertionQuotient hB ≃ₘ⟮𝓡 3, 𝓡 3⟯ insertionBall B :=
    radialCapAttachmentDiffeomorph transitionEnd_pos hB
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    change ‖(D (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x) : E3)‖ ≤ transitionEnd
    rw [show (D (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x) : E3) = x.val from
      radialCapAttachmentHomeomorph_cap transitionEnd_pos hB x]
    exact x.property
  · intro hp
    let x : Cap := ⟨(D p).val, hp⟩
    refine ⟨x, D.injective ?_⟩
    apply Subtype.ext
    exact radialCapAttachmentHomeomorph_cap transitionEnd_pos hB x

private theorem precision_for_input_error (A : ℝ) (hA : 0 < A) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      2 * A < δ⁻¹ ∧ 1 < δ⁻¹ ∧ δ + Real.sqrt δ < ε := by
  have hc : Continuous (fun δ : ℝ => δ + Real.sqrt δ) := by fun_prop
  have he : ∀ᶠ δ : ℝ in 𝓝 0, δ + Real.sqrt δ < ε :=
    hc.continuousAt.eventually_lt_const (by simpa using hε)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp he
  let T := 2 * A + 2
  have hT : 0 < T := by dsimp [T]; linarith
  let δ₀ := min (r / 2) (min (1 / 4 : ℝ) (1 / (2 * T)))
  have hδ₀ : 0 < δ₀ := lt_min (half_pos hr) (lt_min (by norm_num) (by positivity))
  have hquarter : δ₀ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨δ₀, hδ₀, hquarter.trans_lt (by norm_num), ?_⟩
  intro δ hδ hδle
  have hδT : δ ≤ 1 / (2 * T) := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : T * δ < 1 := by
    have h := mul_le_mul_of_nonneg_left hδT hT.le
    have heq : T * (1 / (2 * T)) = 1 / 2 := by field_simp
    rw [heq] at h
    linarith
  have hfit : T < δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hδ).mpr hprod
  refine ⟨(show 2 * A < T by dsimp [T]; linarith).trans hfit,
    (show 1 < T by dsimp [T]; linarith).trans hfit, ?_⟩
  apply hrr
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
  exact (hδle.trans (min_le_left _ _)).trans_lt (half_lt_self hr)

section Geometry
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private theorem quotient_cap_volume_eq (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos))
      (d.positiveSideInsertionMetric hA hAB)
      (range (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary (inv_pos.mpr d.precision_pos)))) =
    riemannianVolumeMeasure (𝓡 3) (insertionBall δ⁻¹) (d.positiveSideCollapseMetric hA hAB)
      {x | ‖(x : E3)‖ ≤ transitionEnd} := by
  rw [original_cap_range, d.positiveSideInsertionMetric_eq_pullback_collapseMetric hA hAB]
  exact riemannianVolumeMeasure_pullbackOpen_preimage (d.positiveSideCollapseMetric hA hAB)
    (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos))
    ((isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet)
end Geometry

theorem exists_normalizedDatum_positiveSideInsertionMetric_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ,
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
          let hB := inv_pos.mpr d.precision_pos
          letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
          riemannianVolumeMeasure (𝓡 3) (InsertionQuotient hB) (d.positiveSideInsertionMetric hA hAB)
            (range (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB))) ≤
            ENNReal.ofReal (Real.sqrt ((metricScalarAt g x₀)⁻¹)) ^ 3 *
              (2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨ε, hε, hvolume⟩ := exists_insertedMetric_scaled_cap_volume_bound A hA
  obtain ⟨δ₀, hδ₀, hhalf, hprecision⟩ := precision_for_input_error A hA ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hB, hsmall⟩ := hprecision δ hδ hδle
  refine ⟨hAB, ?_⟩
  intro k E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  dsimp only
  have hin : metricDerivENormSupOn
      {q : openCylinder δ⁻¹ | q.val.2 ∈ Icc (-2 * A) 0} 0 d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) < ENNReal.ofReal δ :=
    (metricDerivENormSupOn_mono (subset_univ _) (Nat.zero_le k) _ _ _).trans_lt d.controlledMetric_error_lt
  have hsum := ENNReal.add_lt_add_right (a := ENNReal.ofReal (Real.sqrt δ)) ENNReal.ofReal_ne_top hin
  rw [← ENNReal.ofReal_add hδ.le (Real.sqrt_nonneg _)] at hsum
  have herr := hsum.trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hsmall)
  have habs : |1 - Real.sqrt δ - 1| = Real.sqrt δ := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hv := hvolume δ⁻¹ hAB hB (1 - Real.sqrt δ) d.controlledMetric_cylinder_lower.1 d.controlledMetric
    (by simpa only [habs] using herr) (metricScalarAt g x₀) d.scalar_pos
  rw [quotient_cap_volume_eq d hA hAB]
  exact hv

end DifferentialGeometry.PDE.RicciFlow.StandardCap
