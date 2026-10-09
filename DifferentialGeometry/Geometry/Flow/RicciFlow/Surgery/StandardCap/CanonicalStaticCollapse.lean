import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalRetainedMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalCapChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCollapseLength
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

set_option autoImplicit false
noncomputable section
open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

private def centralOpenMap (δ : ℝ) : C(neckCentralDomain δ, openCylinder δ⁻¹) :=
  ⟨fun q => ⟨q.1.1, q.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private def centralImageMap (d : normalizedDatum g x₀ δ k) :
    C(neckCentralDomain δ, d.oriented.controlledImage) :=
  ⟨fun q => ⟨d.oriented.controlledMap (centralOpenMap δ q),
    d.oriented.controlledMap_mem_controlledImage _⟩,
    (d.oriented.controlledMap_smooth.continuous.comp (centralOpenMap δ).continuous).subtype_mk _⟩

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def collapse : C(neckCentralDomain δ, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.collapse ∘ centralImageMap d, by
    have h : Continuous w.data.collapse := by
      rw [w.properties.collapse_eq]
      exact d.oriented.continuous_positiveSideQuotientCollapseMap hA w.properties.cut_fit
    exact h.comp (centralImageMap d).continuous⟩

theorem collapse_retained (x : neckCentralDomain δ) (hz : 0 ≤ x.1.1.2) :
    w.collapse x = w.retainedMap ⟨x.1.1, hz, x.2.2⟩ := by
  exact w.properties.collapse_retained (x.1.1.1, ⟨x.1.1.2, hz, x.2.2⟩)

theorem collapse_tip (x : neckCentralDomain δ) (hz : x.1.1.2 ≤ w.data.profileTip) :
    w.collapse x = w.data.tip :=
  w.properties.collapse_collapsed (centralOpenMap δ x) hz

theorem collapse_radial (x : neckCentralDomain δ)
    (hlo : w.data.profileTip < x.1.1.2) (hhi : x.1.1.2 ≤ 0)
    (hx : w.data.profile x.1.1.2 • x.1.1.1.1 ∈ standardCapClosedCore) :
    w.collapse x = w.capChart ⟨w.data.profile x.1.1.2 • x.1.1.1.1, hx⟩ := by
  exact w.properties.collapse_radial (centralOpenMap δ x) ⟨hlo.le, hhi⟩

theorem collapse_length (γ : ℝ → neckCentralDomain δ) (a b : ℝ)
    (hγ : ContinuousOn γ (Icc a b)) :
    riemannianCurveLength w.data.outMetric (w.collapse ∘ γ) a b ≤
      riemannianCurveLength g (fun t => d.oriented.map (γ t).1) a b := by
  exact w.collapse_length_of_toNormalizedNeck γ a b hγ

theorem collapse_locallyLipschitz (x : neckCentralDomain δ) :
    ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf w.data.outMetric (w.collapse y) (w.collapse z) ≤
        L * riemannianEDistOf g (d.oriented.map y.1) (d.oriented.map z.1) := by
  let : RegularSpace M := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  obtain ⟨L, V, hV, hL⟩ := w.properties.collapse_locallyLipschitz (centralImageMap d x)
  obtain ⟨W, hW, hdist⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_mem_nhds_riemannianEDistOf_restrictOpen_eq
      g d.oriented.controlledImage (centralImageMap d x)
  refine ⟨(centralImageMap d) ⁻¹' V ∩
      (fun y => (centralImageMap d y).val) ⁻¹' W, ?_, L, ?_⟩
  · exact inter_mem ((centralImageMap d).continuous.continuousAt.preimage_mem_nhds hV)
      ((continuous_subtype_val.comp
        (centralImageMap d).continuous).continuousAt.preimage_mem_nhds hW)
  · intro y hy z hz
    have h := hL (centralImageMap d y) hy.1 (centralImageMap d z) hz.1
    rw [hdist (centralImageMap d y) (centralImageMap d z) hy.2 hz.2] at h
    exact h

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
