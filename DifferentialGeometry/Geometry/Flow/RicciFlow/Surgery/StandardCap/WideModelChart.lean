import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

def wideModelMap {B : ℝ} (hB : 0 < B) : insertionBall B → InsertionQuotient hB :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm

theorem wideModelMap_isSmoothEmbedding {B : ℝ} (hB : 0 < B) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (wideModelMap hB) :=
  isSmoothEmbedding_modelWindowMap hB (le_refl (transitionEnd + B))

theorem wideModelMap_isLocalDiffeomorph {B : ℝ} (hB : 0 < B) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (wideModelMap hB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm.isLocalDiffeomorph

theorem wideModelMap_realization {B : ℝ} (hB : 0 < B) (x : insertionBall B) :
    radialCapAttachmentDiffeomorph transitionEnd_pos hB (wideModelMap hB x) = x :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).apply_symm_apply x

theorem wideModelMap_restrict {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B)
    (x : modelWindow R) :
    wideModelMap hB (Opens.inclusion (modelWindow_le_insertionBall hfit) x) =
      modelWindowMap hB hfit x := rfl

private def capPoint {B : ℝ} (hB : 0 < B) (x : Cap) : insertionBall B :=
  ⟨x.val, x.property.trans_lt (lt_add_of_pos_right transitionEnd hB)⟩

theorem wideModelMap_cap {B : ℝ} (hB : 0 < B) (x : Cap) :
    wideModelMap hB (capPoint hB x) =
      adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos hB).injective
  refine (wideModelMap_realization hB (capPoint hB x)).trans ?_
  apply Subtype.ext
  exact (radialCapAttachmentHomeomorph_cap transitionEnd_pos hB x).symm

private def retainedPoint {B : ℝ} (q : S2 × Ico (0 : ℝ) B) : insertionBall B :=
  ⟨(transitionEnd + q.2.val) • (q.1 : E3), by
    change ‖(transitionEnd + q.2.val) • (q.1 : E3)‖ < transitionEnd + B
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg transitionEnd_pos q.2.property.1),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
    linarith [q.2.property.2]⟩

theorem wideModelMap_retained {B : ℝ} (hB : 0 < B) (q : S2 × Ico (0 : ℝ) B) :
    wideModelMap hB (retainedPoint q) =
      adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB) q := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos hB).injective
  refine (wideModelMap_realization hB (retainedPoint q)).trans ?_
  apply Subtype.ext
  exact (radialCapAttachmentHomeomorph_retained transitionEnd_pos hB q).symm

def wideModelPullback {B : ℝ} (hB : 0 < B)
    (g : SmoothRiemannianMetric (𝓡 3) (InsertionQuotient hB)) :
    SmoothRiemannianMetric (𝓡 3) (insertionBall B) :=
  modelWindowPullback hB (le_refl (transitionEnd + B)) g

theorem wideModelPullback_inner {B : ℝ} (hB : 0 < B)
    (g : SmoothRiemannianMetric (𝓡 3) (InsertionQuotient hB))
    (x : insertionBall B) (v w : TangentSpace (𝓡 3) x) :
    (wideModelPullback hB g).inner x v w =
      g.inner (wideModelMap hB x)
        (mfderiv (𝓡 3) (𝓡 3) (wideModelMap hB) x v)
        (mfderiv (𝓡 3) (𝓡 3) (wideModelMap hB) x w) :=
  modelWindowPullback_inner hB (le_refl (transitionEnd + B)) g x v w

theorem wideModelPullback_insertedQuotientMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    let hB : 0 < B := (mul_pos (by norm_num : (0 : ℝ) < 2) hA).trans hAB
    wideModelPullback hB (insertedQuotientMetric hA hAB hη h) =
      insertedMetric hA hAB hη h := by
  exact modelWindowPullback_insertedQuotientMetric hA hAB hη h (le_refl (transitionEnd + B))

theorem normalizedDatum_wideModelPullback
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    (d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    wideModelPullback (inv_pos.mpr d.precision_pos)
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) =
      insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
  exact normalizedDatum_modelWindowPullback d hA hAB (le_refl (transitionEnd + δ⁻¹))
end DifferentialGeometry.PDE.RicciFlow.StandardCap
