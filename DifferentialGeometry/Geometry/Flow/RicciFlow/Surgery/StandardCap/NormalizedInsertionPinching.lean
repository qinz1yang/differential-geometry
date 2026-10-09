import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionOuterCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertion
import DifferentialGeometry.Geometry.Neck.InsertionChart
import DifferentialGeometry.Geometry.Neck.ScalarControl
import DifferentialGeometry.Geometry.Curvature.OperatorScaling
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ EC) := ⟨by simp⟩
private abbrev cyl := roundCylinderMetric (E := E3) (n := 2)
private local instance (U : Opens (S2 × ℝ)) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC U.isOpen)

section Incoming
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem normalizedDatum_controlledMetric_curvature (d : normalizedDatum g x₀ δ k)
    (q : openCylinder δ⁻¹) :
    metricScalarAt d.controlledMetric q = metricScalarAt g (d.controlledMap q) / metricScalarAt g x₀ ∧
      leastCurvatureOperatorEigenvalueAt d.controlledMetric q
          (metricAlgebraicCurvatureTensorAt d.controlledMetric q) =
        leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
          (metricAlgebraicCurvatureTensorAt g (d.controlledMap q)) / metricScalarAt g x₀ := by
  have hrange : range d.controlledChart = univ := d.controlledChart.surjective.range_eq
  let : SigmaCompactSpace d.controlledImage := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range d.controlledChart.continuous)
  rw [d.controlledMetric_eq_pullback_controlledChart]
  constructor
  · exact metricScalarAt_pullback_scaleMetric_restrictOpenCross g d.controlledImage
      d.controlledChart (metricScalarAt g x₀) d.scalar_pos q
  · rw [leastCurvatureOperatorEigenvalueAt_pullbackMetricCross,
      DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric,
      leastCurvatureOperatorEigenvalueAt_restrictOpen]
    rfl

private theorem controlled_scalar_pos (d : normalizedDatum g x₀ δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 200000000) (q : openCylinder δ⁻¹) :
    0 < metricScalarAt d.controlledMetric q := by
  rw [(normalizedDatum_controlledMetric_curvature d q).1]
  apply div_pos _ d.scalar_pos
  apply d.scalar_pos_of_controlled hk (by linarith)
  exact ⟨q.property.1.le, q.property.2.le⟩

private theorem controlled_HamiltonIvey (d : normalizedDatum g x₀ δ k)
    (a : ℝ) (q : openCylinder δ⁻¹)
    (hin : (metricScalarAt g (d.controlledMap q),
      2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
        (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a) :
    (metricScalarAt d.controlledMetric q,
      2 * leastCurvatureOperatorEigenvalueAt d.controlledMetric q
        (metricAlgebraicCurvatureTensorAt d.controlledMetric q)) ∈
      fixedHamiltonIveyRegion (metricScalarAt g x₀ * a) := by
  obtain ⟨hR, hν⟩ := normalizedDatum_controlledMetric_curvature d q
  rw [hR, hν, ← mul_div_assoc]
  exact (mem_fixedHamiltonIveyRegion_scale_iff d.scalar_pos a _ _).mpr hin
end Incoming

private theorem old_subset {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

private theorem outer_point {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (x : insertionBall B) (hx : conformalRadius (-A) < ‖(x : E3)‖) :
    ∃ q : insertionCylinder A B, insertionMap hA hAB q = x ∧ -A < q.val.2 := by
  have hxann : x.val ∈ insertionAnnulus A B := by
    constructor
    · exact (strictMono_conformalRadius (by linarith : -2 * A < -A)).trans hx
    · rw [conformalRadius_cylindrical (by linarith : 0 ≤ B)]
      exact x.property
  have hr : x ∈ range (insertionMap hA hAB) := by
    rw [range_insertionMap]
    exact hxann
  obtain ⟨q, hq⟩ := hr
  refine ⟨q, hq, ?_⟩
  have he : ‖(x : E3)‖ = conformalRadius q.val.2 := by
    rw [← hq, insertionMap_apply, conformalMap_norm]
  rw [he] at hx
  exact strictMono_conformalRadius.lt_iff_lt.mp hx

private theorem rounding_gain_nonneg (z : ℝ) (hz : z ≤ 0) :
    0 ≤ (-deriv (deriv conformalFactor) z) / 2 := by
  rcases lt_or_eq_of_le hz with h | rfl
  · exact div_nonneg (neg_nonneg.mpr (conformalFactor_signs_of_neg h).2.2.le) (by norm_num)
  · have hD : deriv (deriv conformalFactor) 0 = 0 := by
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero] using iteratedDeriv_conformalFactor_zero 2
    rw [hD, neg_zero, zero_div]

theorem exists_normalizedDatum_insertedMetric_pinching :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, 2 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
          [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
          [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
          [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
          ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
            let out := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos)
              (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
            (∀ x, 0 < metricScalarAt out x) ∧
              ∀ a : ℝ, 0 < a →
                (∀ q : openCylinder δ⁻¹,
                  (metricScalarAt g (d.controlledMap q),
                    2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
                      (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈
                    fixedHamiltonIveyRegion a) →
                ∀ x, (metricScalarAt out x,
                  2 * leastCurvatureOperatorEigenvalueAt out x
                    (metricAlgebraicCurvatureTensorAt out x)) ∈ fixedHamiltonIveyRegion a := by
  obtain ⟨A, hA, hsmall, hgain⟩ := exists_insertedMetric_outer_curvature_gain
  obtain ⟨τ, hτ, hτhalf, hcore⟩ := exists_normalizedDatum_insertedMetric_core_curvature_pos A hA
  let δ₀ := min τ (1 / 200000000 : ℝ)
  refine ⟨A, hA, hsmall, δ₀, lt_min hτ (by norm_num),
    (min_le_left _ _).trans_lt hτhalf, ?_⟩
  intro δ hδ hδle
  have hδτ : δ ≤ τ := hδle.trans (min_le_left _ _)
  have hδtiny : δ ≤ 1 / 200000000 := hδle.trans (min_le_right _ _)
  obtain ⟨hAB, hc⟩ := hcore δ hδ hδτ
  refine ⟨hAB, ?_⟩
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  let normOut := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  have hclose : metricDerivENormSupOn univ 2 d.controlledMetric
      (cyl.restrictOpen (openCylinder δ⁻¹)) (cyl.restrictOpen (openCylinder δ⁻¹)) <
        ENNReal.ofReal (1 / 100000000 : ℝ) := by
    exact ((metricDerivENormSupOn_mono (subset_refl univ) hk _ _ _).trans_lt
      d.controlledMetric_error_lt).trans
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le).mpr (by linarith))
  have hmono (q : insertionCylinder A δ⁻¹) (hq : -A < q.val.2) :
      metricScalarAt d.controlledMetric (Opens.inclusion (old_subset hAB) q) ≤
          metricScalarAt normOut (insertionMap hA hAB q) ∧
        2 * leastCurvatureOperatorEigenvalueAt d.controlledMetric (Opens.inclusion (old_subset hAB) q)
            (metricAlgebraicCurvatureTensorAt d.controlledMetric (Opens.inclusion (old_subset hAB) q)) ≤
          2 * leastCurvatureOperatorEigenvalueAt normOut (insertionMap hA hAB q)
            (metricAlgebraicCurvatureTensorAt normOut (insertionMap hA hAB q)) := by
    by_cases hz : q.val.2 ≤ 0
    · obtain ⟨hR, hν⟩ := hgain δ⁻¹ hAB (1 - Real.sqrt δ)
        d.controlledMetric_cylinder_lower.1 d.controlledMetric hclose q ⟨hq, hz⟩
      have hn := rounding_gain_nonneg q.val.2 hz
      exact ⟨(le_add_of_nonneg_right hn).trans hR, (le_add_of_nonneg_right hn).trans hν⟩
    · obtain ⟨hR, hν⟩ := insertedMetric_retained_curvature hA hAB
        d.controlledMetric_cylinder_lower.1 d.controlledMetric q (le_of_not_ge hz)
      exact ⟨hR.symm.le, (congrArg (fun t : ℝ => 2 * t) hν.symm).le⟩
  have hRpos (x : insertionBall δ⁻¹) : 0 < metricScalarAt normOut x := by
    by_cases hx : ‖(x : E3)‖ ≤ conformalRadius (-A)
    · exact (hc k hk g x₀ d x hx).2
    · obtain ⟨q, rfl, hq⟩ := outer_point hA hAB x (lt_of_not_ge hx)
      exact (controlled_scalar_pos d hk hδtiny _).trans_le (hmono q hq).1
  have hHI (a : ℝ) (ha : 0 < a)
      (hin : ∀ q : openCylinder δ⁻¹,
        (metricScalarAt g (d.controlledMap q),
          2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
            (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a)
      (x : insertionBall δ⁻¹) :
      (metricScalarAt normOut x,
        2 * leastCurvatureOperatorEigenvalueAt normOut x (metricAlgebraicCurvatureTensorAt normOut x)) ∈
          fixedHamiltonIveyRegion (metricScalarAt g x₀ * a) := by
    by_cases hx : ‖(x : E3)‖ ≤ conformalRadius (-A)
    · have hs := (hc k hk g x₀ d x hx).1
      obtain ⟨B, hB⟩ := exists_orthonormalBasisAt (I := 𝓡 3) normOut x
        (show Module.finrank ℝ E3 = 3 by simp)
      exact Or.inl (mul_nonneg (by norm_num)
        (leastCurvatureOperatorEigenvalueAt_nonneg_of_sectionalCurvature_nonneg
          normOut x B hB (fun u v hv => (hs u v hv).le)))
    · obtain ⟨q, rfl, hq⟩ := outer_point hA hAB x (lt_of_not_ge hx)
      exact mem_fixedHamiltonIveyRegion_of_le (mul_pos d.scalar_pos ha)
        (hmono q hq).1 (hmono q hq).2 (hRpos _).le
        (controlled_HamiltonIvey d a _ (hin _))
  dsimp only
  constructor
  · intro x
    rw [DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_inv]
    exact mul_pos d.scalar_pos (hRpos x)
  · intro a ha hin x
    have ht := (mem_fixedHamiltonIveyRegion_scale_iff (inv_pos.mpr d.scalar_pos)
      (metricScalarAt g x₀ * a) (metricScalarAt normOut x)
      (2 * leastCurvatureOperatorEigenvalueAt normOut x (metricAlgebraicCurvatureTensorAt normOut x))).mpr
        (hHI a ha hin x)
    have hp : (metricScalarAt g x₀)⁻¹ * (metricScalarAt g x₀ * a) = a := by
      rw [← mul_assoc, inv_mul_cancel₀ d.scalar_pos.ne', one_mul]
    rw [hp] at ht
    have hRs : metricScalarAt
        (scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) normOut) x =
        metricScalarAt normOut x / (metricScalarAt g x₀)⁻¹ := by
      rw [DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric]
      ring
    rw [hRs,
      DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric,
      ← mul_div_assoc]
    exact ht

private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) :=
  DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_t2Space transitionEnd_pos hB

section Quotient
open DifferentialGeometry.Topology.Manifold.Attachment
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private theorem quotient_curvature (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (x : InsertionQuotient (inv_pos.mpr d.precision_pos)) :
    let out := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos)
      (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
    let y := radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos) x
    metricScalarAt (d.positiveSideInsertionMetric hA hAB) x = metricScalarAt out y ∧
      leastCurvatureOperatorEigenvalueAt (d.positiveSideInsertionMetric hA hAB) x
          (metricAlgebraicCurvatureTensorAt (d.positiveSideInsertionMetric hA hAB) x) =
        leastCurvatureOperatorEigenvalueAt out y (metricAlgebraicCurvatureTensorAt out y) := by
  let normOut := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  let out := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) normOut
  let D : InsertionQuotient (inv_pos.mpr d.precision_pos) ≃ₘ⟮𝓡 3, 𝓡 3⟯ insertionBall δ⁻¹ :=
    radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)
  have he : d.positiveSideInsertionMetric hA hAB = Diffeomorph.pullbackMetricCross out D := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [normalizedDatum.positiveSideInsertionMetric, scaleMetric_inner,
      insertedQuotientMetric_inner, Diffeomorph.pullbackMetricCross_inner]
    rfl
  dsimp only
  rw [he]
  constructor
  · have hp := metricScalarAt_pullback_scaleMetricCross normOut D
      (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) x
    exact hp.trans ((show metricScalarAt normOut (D x) / (metricScalarAt g x₀)⁻¹ =
        ((metricScalarAt g x₀)⁻¹)⁻¹ * metricScalarAt normOut (D x) by ring).trans
      (DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric
        (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) normOut (D x)).symm)
  · exact leastCurvatureOperatorEigenvalueAt_pullbackMetricCross out D x
end Quotient

theorem exists_normalizedDatum_positiveSideInsertionMetric_pinching :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ hAB : 2 * A < δ⁻¹, ∀ k : ℕ, 2 ≤ k →
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
          [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
          [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
          [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
          ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
            (∀ x, 0 < metricScalarAt (d.positiveSideInsertionMetric hA hAB) x) ∧
              ∀ a : ℝ, 0 < a →
                (∀ q : openCylinder δ⁻¹,
                  (metricScalarAt g (d.controlledMap q),
                    2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
                      (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈
                    fixedHamiltonIveyRegion a) →
                ∀ x, (metricScalarAt (d.positiveSideInsertionMetric hA hAB) x,
                  2 * leastCurvatureOperatorEigenvalueAt (d.positiveSideInsertionMetric hA hAB) x
                    (metricAlgebraicCurvatureTensorAt (d.positiveSideInsertionMetric hA hAB) x)) ∈
                    fixedHamiltonIveyRegion a := by
  obtain ⟨A, hA, hsmall, δ₀, hδ₀, hhalf, hp⟩ := exists_normalizedDatum_insertedMetric_pinching
  refine ⟨A, hA, hsmall, δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hb⟩ := hp δ hδ hle
  refine ⟨hAB, ?_⟩
  intro k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hR, hHI⟩ := hb k hk g x₀ d
  constructor
  · intro x
    rw [(quotient_curvature d hA hAB x).1]
    exact hR _
  · intro a ha hin x
    rw [(quotient_curvature d hA hAB x).1, (quotient_curvature d hA hAB x).2]
    exact hHI a ha hin _

end DifferentialGeometry.PDE.RicciFlow.StandardCap
