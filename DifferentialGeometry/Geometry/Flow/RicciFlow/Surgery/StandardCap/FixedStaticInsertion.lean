import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticPinchingInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessCoherence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WideStaticRequests
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WholeCapDomination

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure MeasureTheory
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

private abbrev S2 := Metric.sphere (0 : E3) 1
private def capTip : Cap := ⟨0, by simpa using transitionEnd_pos.le⟩
private def capPoint {B : ℝ} (hB : 0 < B) (x : Cap) : insertionBall B :=
  ⟨x.val, x.property.trans_lt (lt_add_of_pos_right transitionEnd hB)⟩
private def retainedPoint {B : ℝ} (q : S2 × Ico (0 : ℝ) B) : insertionBall B :=
  ⟨(transitionEnd + q.2.val) • (q.1 : E3), by
    change ‖(transitionEnd + q.2.val) • (q.1 : E3)‖ < transitionEnd + B
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg transitionEnd_pos q.2.property.1),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
    linarith [q.2.property.2]⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

structure FixedStaticInsertionProperties (C : ℕ → ℝ)
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε) : Prop where
  additional : StaticInsertionAdditionalProperties C w
  wide_embedding : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
    (wideModelMap (inv_pos.mpr d.precision_pos))
  wide_local : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (wideModelMap (inv_pos.mpr d.precision_pos))
  wide_cap : ∀ x : Cap, wideModelMap (inv_pos.mpr d.precision_pos)
    (capPoint (inv_pos.mpr d.precision_pos) x) = w.data.capMap x
  wide_retained : ∀ q : S2 × Ico (0 : ℝ) δ⁻¹,
    wideModelMap (inv_pos.mpr d.precision_pos) (retainedPoint q) = w.data.retainedInclusion q
  cap_metric : ∀ (x : Cap) (v : TangentSpace (𝓡∂ 3) x),
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric).inner (w.data.capMap x)
      (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x v) (mfderiv (𝓡∂ 3) (𝓡 3) w.data.capMap x v) ≤
      2 * metric.inner x.val
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
  cap_volume : riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos))
    w.data.outMetric (range w.data.capMap) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 / 2 : ℝ) * (metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
        riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}

theorem exists_fixed_static_insertion :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∃ δBase : ℝ, 0 < δBase ∧ δBase < 1 / 2 ∧
      ∃ δRequest : StaticRequest → ℝ, (∀ P, 0 < δRequest P ∧ δRequest P ≤ δBase) ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δBase → ∀ (k : ℕ) (hk : 8 ≤ k),
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        ∃ w : CanonicalStaticInsertionWitness (d.lowerOrder hk) A hA 1 4 1,
          FixedStaticInsertionProperties C w ∧
          ∀ P : StaticRequest, δ ≤ δRequest P → max 8 P.order ≤ k →
            P.IsSatisfied w.data.outMetric (metricScalarAt g x₀) d.scalar_pos
              (insertionBall δ⁻¹) (wideModelMap (inv_pos.mpr d.precision_pos))
              (wideModelMap_isLocalDiffeomorph (inv_pos.mpr d.precision_pos))
              (wideModelMap_isSmoothEmbedding (inv_pos.mpr d.precision_pos)).isEmbedding.injective
              w.data.tip := by
  classical
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_staticInsertion_with_additional_properties
  obtain ⟨δb, hδb, hbhalf, hb⟩ := hmod 1 (by norm_num) 4 1 (by norm_num)
  obtain ⟨δv, hδv, _, hv⟩ := exists_wholeCap_metric_and_volume_bounds A hA
  choose δR hδR hRhalf hR using fun P : StaticRequest => exists_wideModel_request_threshold A hA P
  refine ⟨C, hC, A, hA, hsmall, min δb δv, lt_min hδb hδv,
    (min_le_left _ _).trans_lt hbhalf, fun P => min (min δb δv) (δR P),
    fun P => ⟨lt_min (lt_min hδb hδv) (hδR P), min_le_left _ _⟩, ?_⟩
  intro δ hδ hle k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨w, hw⟩ := hb δ hδ (hle.trans (min_le_left _ _)) g x₀ (d.lowerOrder hk)
  obtain ⟨hAB, hv⟩ := hv δ hδ (hle.trans (min_le_right _ _))
  have hbounds := hv k g x₀ d
  have hmetric : w.data.outMetric = d.oriented.positiveSideInsertionMetric hA hAB :=
    w.properties.outMetric_eq.trans
      (d.oriented.lowerOrder_positiveSideInsertionMetric hk hA w.properties.cut_fit)
  have hcapMap := w.properties.capMap_eq.trans w.properties.capInclusion_eq
  refine ⟨w, ?_, ?_⟩
  · refine
      { additional := hw
        wide_embedding := wideModelMap_isSmoothEmbedding _
        wide_local := wideModelMap_isLocalDiffeomorph _
        wide_cap := ?_
        wide_retained := ?_
        cap_metric := ?_
        cap_volume := ?_ }
    · intro x
      rw [hcapMap]
      exact wideModelMap_cap _ x
    · intro q
      rw [w.properties.retainedInclusion_eq]
      exact wideModelMap_retained _ q
    · intro x v
      rw [hcapMap, hmetric]
      exact hbounds.1 x v
    · simpa only [hmetric, hcapMap] using hbounds.2
  · intro P hleP hPk
    obtain ⟨_, _, hreq⟩ := hR P δ hδ (hleP.trans (min_le_right _ _))
    have h := hreq k ((le_max_right 8 P.order).trans hPk) g x₀ d
    have htip : w.data.tip = adjunctionCell (radialCapBoundary transitionEnd_pos)
        (retainedBoundary (inv_pos.mpr d.precision_pos)) capTip :=
      w.properties.tip_eq.trans (congrFun w.properties.capInclusion_eq capTip)
    rw [hmetric, htip]
    exact h
end DifferentialGeometry.PDE.RicciFlow.StandardCap
