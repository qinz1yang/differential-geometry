import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseMapDistanceNormalized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem canonicalStaticInsertionWitness_collapse_riemannianEDistOf_le
    {d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k}
    {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (p q : d.oriented.controlledImage) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    riemannianEDistOf w.data.outMetric (w.data.collapse p) (w.data.collapse q) ≤
      riemannianEDistOf (g.restrictOpen d.oriented.controlledImage) p q := by
  rw [w.properties.collapse_eq, w.properties.outMetric_eq]
  exact DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_riemannianEDistOf_le
    d.oriented hA w.properties.cut_fit p q

end DifferentialGeometry.PDE.RicciFlow.StandardCap
