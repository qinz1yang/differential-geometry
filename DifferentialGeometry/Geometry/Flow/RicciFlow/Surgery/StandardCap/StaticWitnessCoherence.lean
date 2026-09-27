import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WideModelChart

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k j l : ℕ}
  {A D₀ D₁ ε₀ ε₁ : ℝ} {hA : 0 < A} {m₀ m₁ : ℕ}

theorem CanonicalStaticInsertionWitness.coherent_of_lowerOrder
    (d : normalizedDatum g x₀ δ k) (hj : j ≤ k) (hl : l ≤ k)
    (w₀ : CanonicalStaticInsertionWitness (d.lowerOrder hj) A hA D₀ m₀ ε₀)
    (w₁ : CanonicalStaticInsertionWitness (d.lowerOrder hl) A hA D₁ m₁ ε₁) :
    w₀.data.quotientDiffeomorph = w₁.data.quotientDiffeomorph ∧
    w₀.data.gluingDiffeomorph = w₁.data.gluingDiffeomorph ∧
    w₀.data.capInclusion = w₁.data.capInclusion ∧
    w₀.data.retainedInclusion = w₁.data.retainedInclusion ∧
    w₀.data.tip = w₁.data.tip ∧ w₀.data.outMetric = w₁.data.outMetric ∧
    w₀.data.capMap = w₁.data.capMap ∧ w₀.data.deepMap = w₁.data.deepMap ∧
    w₀.data.profileTip = w₁.data.profileTip ∧ w₀.data.profile = w₁.data.profile ∧
    w₀.data.collapse = w₁.data.collapse ∧
    (∀ x : modelWindow (D₀ + 1), w₀.data.windowMap x =
      wideModelMap (inv_pos.mpr d.precision_pos)
        (Opens.inclusion (modelWindow_le_insertionBall w₀.properties.window_fit) x)) ∧
    (∀ x : modelWindow (D₁ + 1), w₁.data.windowMap x =
      wideModelMap (inv_pos.mpr d.precision_pos)
        (Opens.inclusion (modelWindow_le_insertionBall w₁.properties.window_fit) x)) := by
  have hcap := w₀.properties.capInclusion_eq.trans w₁.properties.capInclusion_eq.symm
  have hcapMap := (w₀.properties.capMap_eq.trans w₀.properties.capInclusion_eq).trans
    (w₁.properties.capMap_eq.trans w₁.properties.capInclusion_eq).symm
  have hmetric₀ := w₀.properties.outMetric_eq.trans
    (d.oriented.lowerOrder_positiveSideInsertionMetric hj hA w₀.properties.cut_fit)
  have hmetric₁ := w₁.properties.outMetric_eq.trans
    (d.oriented.lowerOrder_positiveSideInsertionMetric hl hA w₁.properties.cut_fit)
  have hcollapse₀ := w₀.properties.collapse_eq.trans
    (d.oriented.lowerOrder_positiveSideQuotientCollapseMap hj hA w₀.properties.cut_fit)
  have hcollapse₁ := w₁.properties.collapse_eq.trans
    (d.oriented.lowerOrder_positiveSideQuotientCollapseMap hl hA w₁.properties.cut_fit)
  refine ⟨w₀.properties.quotientDiffeomorph_eq.trans w₁.properties.quotientDiffeomorph_eq.symm,
    w₀.properties.gluingDiffeomorph_eq.trans w₁.properties.gluingDiffeomorph_eq.symm,
    hcap, w₀.properties.retainedInclusion_eq.trans w₁.properties.retainedInclusion_eq.symm,
    ?_, hmetric₀.trans hmetric₁.symm, hcapMap, ?_,
    w₀.properties.profileTip_eq.trans w₁.properties.profileTip_eq.symm,
    w₀.properties.profile_eq.trans w₁.properties.profile_eq.symm,
    hcollapse₀.trans hcollapse₁.symm, ?_, ?_⟩
  · rw [w₀.properties.tip_eq, w₁.properties.tip_eq, hcap]
  · rw [w₀.properties.deepMap_eq, w₁.properties.deepMap_eq, hcapMap]
  · intro x
    rw [w₀.properties.windowMap_eq]
    exact (wideModelMap_restrict _ w₀.properties.window_fit x).symm
  · intro x
    rw [w₁.properties.windowMap_eq]
    exact (wideModelMap_restrict _ w₁.properties.window_fit x).symm
end DifferentialGeometry.PDE.RicciFlow.StandardCap
