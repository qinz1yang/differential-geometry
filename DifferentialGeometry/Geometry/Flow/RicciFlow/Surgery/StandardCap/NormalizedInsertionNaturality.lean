import DifferentialGeometry.Geometry.Neck.Naturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Neck.datumIsometry
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Retained (δ : ℝ) := Metric.sphere (0 : E3) 1 × Ico (0 : ℝ) δ⁻¹
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

theorem positiveSideInsertionMetric_eq (F : datumIsometry d d')
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    d'.positiveSideInsertionMetric hA hAB = d.positiveSideInsertionMetric hA hAB := by
  have he : insertedQuotientMetric hA hAB d'.controlledMetric_cylinder_lower.1 d'.controlledMetric =
      insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric :=
    congrArg (fun h => insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 h)
      F.controlledMetric_eq
  apply SmoothRiemannianMetric.ext_inner
  intro p u v
  change (metricScalarAt g' x₀')⁻¹ *
    (insertedQuotientMetric hA hAB d'.controlledMetric_cylinder_lower.1 d'.controlledMetric).inner p u v =
    (metricScalarAt g x₀)⁻¹ *
    (insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric).inner p u v
  rw [F.scalar_eq, he]

theorem modelWindowPullback_eq (F : datumIsometry d d')
    {A R : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (hfit : R ≤ transitionEnd + δ⁻¹) :
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g' x₀') d'.scalar_pos (d'.positiveSideInsertionMetric hA hAB)) =
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) := by
  rw [normalizedDatum_modelWindowPullback, normalizedDatum_modelWindowPullback]
  exact congrArg (fun h => (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 h).restrictOpenOfSubset
    (modelWindow_le_insertionBall hfit)) F.controlledMetric_eq

theorem controlledMap_mem_source (F : datumIsometry d d') (q : openCylinder δ⁻¹) :
    d.controlledMap q ∈ F.source :=
  F.image_source (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q)

theorem controlledMap_eq (F : datumIsometry d d') (q : openCylinder δ⁻¹) :
    (F.equiv ⟨d.controlledMap q, F.controlledMap_mem_source q⟩ : N) = d'.controlledMap q :=
  F.chart_eq (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q)

theorem positiveRetainedMap_mem_source (F : datumIsometry d d') (q : Retained δ) :
    d.positiveRetainedMap q ∈ F.source := by
  rw [normalizedDatum.positiveRetainedMap_apply]
  exact F.image_source _

theorem positiveRetainedMap_eq (F : datumIsometry d d') (q : Retained δ) :
    (F.equiv ⟨d.positiveRetainedMap q, F.positiveRetainedMap_mem_source q⟩ : N) =
      d'.positiveRetainedMap q := by
  let z : bufferedCylinder δ := ⟨(q.1, q.2.val), by
    change -δ⁻¹ - 1 < q.2.val ∧ q.2.val < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr d.precision_pos, q.2.property.1, q.2.property.2]⟩
  have hs : (⟨d.positiveRetainedMap q, F.positiveRetainedMap_mem_source q⟩ : F.source) =
      ⟨d.map z, F.image_source z⟩ := Subtype.ext (d.positiveRetainedMap_apply q)
  exact (congrArg (fun x : F.source => (F.equiv x : N)) hs).trans
    ((F.chart_eq z).trans (d'.positiveRetainedMap_apply q).symm)

theorem controlledImage_le_source (F : datumIsometry d d') : d.controlledImage ≤ F.source := by
  rintro p ⟨q, rfl⟩
  exact F.controlledMap_mem_source q

def controlledImageMap (F : datumIsometry d d') : d.controlledImage → d'.controlledImage :=
  fun p => ⟨(F.equiv ⟨p.val, F.controlledImage_le_source p.property⟩ : N), by
    obtain ⟨q, hq⟩ := p.property
    have he : (F.equiv ⟨p.val, F.controlledImage_le_source p.property⟩ : N) = d'.controlledMap q := by
      have hp : (⟨p.val, F.controlledImage_le_source p.property⟩ : F.source) =
          ⟨d.controlledMap q, F.controlledMap_mem_source q⟩ := Subtype.ext hq.symm
      exact (congrArg (fun x : F.source => (F.equiv x : N)) hp).trans (F.controlledMap_eq q)
    rw [he]
    exact d'.controlledMap_mem_controlledImage q⟩

theorem positiveSideQuotientCollapseMap_eq (F : datumIsometry d d')
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    d'.positiveSideQuotientCollapseMap hA hAB (F.controlledImageMap p) =
      d.positiveSideQuotientCollapseMap hA hAB p := by
  obtain ⟨q, hq⟩ := p.property
  have hp : p = ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ :=
    Subtype.ext hq.symm
  subst p
  have he : F.controlledImageMap ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ =
      ⟨d'.controlledMap q, d'.controlledMap_mem_controlledImage q⟩ :=
    Subtype.ext (F.controlledMap_eq q)
  rw [he, normalizedDatum.positiveSideQuotientCollapseMap_controlledMap,
    normalizedDatum.positiveSideQuotientCollapseMap_controlledMap]

end DifferentialGeometry.Geometry.Neck.datumIsometry
