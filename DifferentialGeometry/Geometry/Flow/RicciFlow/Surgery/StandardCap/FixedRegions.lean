import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def deepRadius (A : ℝ) : ℝ := min 1 (min transitionEnd (conformalRadius (-7 * A / 4))) / 2

def positiveRadius (A : ℝ) : ℝ := deepRadius A / 2

def positiveRegion (A : ℝ) : Set E3 := {x | ‖x‖ ≤ positiveRadius A}

def deepRegion (A : ℝ) : Set E3 := {x | ‖x‖ ≤ deepRadius A}

theorem fixed_radii_bounds (A : ℝ) :
    0 < positiveRadius A ∧ positiveRadius A < deepRadius A ∧
      deepRadius A < min 1 transitionEnd ∧ deepRadius A < conformalRadius (-7 * A / 4) := by
  let R := min 1 (min transitionEnd (conformalRadius (-7 * A / 4)))
  have hR : 0 < R := lt_min zero_lt_one (lt_min transitionEnd_pos (conformalRadius_pos _))
  have hd : 0 < deepRadius A := half_pos hR
  refine ⟨half_pos hd, half_lt_self hd, ?_, ?_⟩
  · apply lt_min
    · exact (half_lt_self hR).trans_le (min_le_left _ _)
    · exact (half_lt_self hR).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · exact (half_lt_self hR).trans_le ((min_le_right _ _).trans (min_le_right _ _))

theorem fixed_regions_properties (A : ℝ) :
    IsCompact (positiveRegion A) ∧ IsCompact (deepRegion A) ∧
      positiveRegion A ⊆ deepRegion A ∧
      ∀ x ∈ positiveRegion A, ∀ u v : TangentSpace (𝓡 3) x,
        metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0 →
          0 < sectionalCurvature metric x u v := by
  obtain ⟨_hp, hpd, hd, _hc⟩ := fixed_radii_bounds A
  have hpcompact : IsCompact (positiveRegion A) := by
    simpa only [positiveRegion, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : E3) (positiveRadius A)
  have hdcompact : IsCompact (deepRegion A) := by
    simpa only [deepRegion, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : E3) (deepRadius A)
  refine ⟨hpcompact, hdcompact, fun x hx => hx.trans hpd.le, ?_⟩
  intro x hx u v hplane
  have hxL : ‖x‖ < transitionEnd := (hx.trans_lt hpd).trans (hd.trans_le (min_le_right _ _))
  exact sectionalCurvature_pos hxL u v hplane

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

theorem normalizedDatum_positiveSideInsertionMetric_fixed_deep
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    let hB := inv_pos.mpr d.precision_pos
    letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
    letI := closedBallChartedSpace transitionEnd_pos
    ∀ (x : {x : E3 // ‖x‖ ≤ transitionEnd}), x.val ∈ deepRegion A →
      ∀ (v w : TangentSpace (𝓡∂ 3) x),
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)).inner
        (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x)
        (mfderiv (𝓡∂ 3) (𝓡 3) (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x w) =
      (1 - Real.sqrt δ) * metric.inner x.val
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x w) := by
  let := closedBallChartedSpace transitionEnd_pos
  dsimp only
  intro x hx v w
  have hx' : ‖x.val‖ < conformalRadius (-7 * A / 4) := hx.trans_lt (fixed_radii_bounds A).2.2.2
  have h := d.positiveSideInsertionMetric_cap_of_inner hA hAB x hx' v w
  rw [scaleMetric_inner, h]
  field_simp [d.scalar_pos.ne']
end DifferentialGeometry.PDE.RicciFlow.StandardCap
