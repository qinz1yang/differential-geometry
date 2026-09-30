import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev OpenE3 := EuclideanSpace ℝ (Fin 3)
private abbrev OpenS2 := Metric.sphere (0 : OpenE3) 1
private abbrev OpenIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ OpenE3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} : ChartedSpace OpenE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

theorem insertionCylinder_subset_original {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

def insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    insertionCylinder A B → InsertionQuotient hB :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm ∘ insertionMap hA hAB

theorem contMDiff_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    ContMDiff OpenIC (𝓡 3) ∞ (insertionQuotientCollarMap hA hAB hB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm.contMDiff.comp (contMDiff_insertionMap hA hAB)

theorem insertionQuotientCollarMap_radial {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    radialCapAttachmentDiffeomorph transitionEnd_pos hB (insertionQuotientCollarMap hA hAB hB q) =
      insertionMap hA hAB q := (radialCapAttachmentDiffeomorph transitionEnd_pos hB).apply_symm_apply _

theorem insertionQuotientCollarMap_radial_mfderiv {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    (mfderiv (𝓡 3) (𝓡 3) (radialCapAttachmentDiffeomorph transitionEnd_pos hB)
      (insertionQuotientCollarMap hA hAB hB q)).comp
        (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q) =
          mfderiv OpenIC (𝓡 3) (insertionMap hA hAB) q := by
  let J := insertionQuotientCollarMap hA hAB hB
  let D := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  have he : D ∘ J = insertionMap hA hAB := funext (insertionQuotientCollarMap_radial hA hAB hB)
  have hd := mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) (J q))
    ((contMDiff_insertionQuotientCollarMap hA hAB hB).mdifferentiable (by simp) q)
  rw [he] at hd
  exact hd.symm

theorem injective_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    Injective (insertionQuotientCollarMap hA hAB hB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm.injective.comp (injective_insertionMap hA hAB)

theorem insertionQuotientCollarMap_mfderiv_injective {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    Injective (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q) := by
  have he := insertionQuotientCollarMap_radial_mfderiv hA hAB hB q
  intro v w hvw
  apply insertionMap_mfderiv_injective hA hAB q
  have hd := congrArg (mfderiv (𝓡 3) (𝓡 3) (radialCapAttachmentDiffeomorph transitionEnd_pos hB)
    (insertionQuotientCollarMap hA hAB hB q)) hvw
  exact (congrArg (fun D => D v) he).symm.trans (hd.trans (congrArg (fun D => D w) he))

theorem isLocalDiffeomorph_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    IsLocalDiffeomorph OpenIC (𝓡 3) ∞ (insertionQuotientCollarMap hA hAB hB) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_insertionQuotientCollarMap hA hAB hB)
    (insertionQuotientCollarMap_mfderiv_injective hA hAB hB) (by simp)

theorem insertionQuotientCollarMap_retained {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) :
    insertionQuotientCollarMap hA hAB hB q =
      adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
        (q.val.1, ⟨q.val.2, hq, q.property.2⟩) := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos hB).injective
  apply Subtype.ext
  have hh := congrArg Subtype.val (insertionQuotientCollarMap_radial hA hAB hB q)
  refine hh.trans ?_
  change conformalRadius q.val.2 • q.val.1.val = (transitionEnd + q.val.2) • q.val.1.val
  rw [conformalRadius_cylindrical hq]

theorem insertedQuotientMetric_openRetained {A B η : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (hη : 0 < η) (h : SmoothRiemannianMetric OpenIC (openCylinder B))
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    (insertedQuotientMetric hA hAB hη h).inner (insertionQuotientCollarMap hA hAB hB q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q w) =
        h.inner (Opens.inclusion (insertionCylinder_subset_original hAB) q) v w := by
  have hd := insertionQuotientCollarMap_radial_mfderiv hA hAB hB q
  have hv := congrArg (fun D => D v) hd
  have hw := congrArg (fun D => D w) hd
  rw [insertedQuotientMetric_inner]
  erw [hv, hw, insertionQuotientCollarMap_radial]
  exact insertedMetric_retained hA hAB hη h q hq v w

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem physicalInsertionMetric_openRetained (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (q : insertionCylinder A δ⁻¹) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    (d.positiveSideInsertionMetric hA hAB).inner
      (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos) q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos)) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos)) q w) =
        g.inner (d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q))
          (mfderiv OpenIC I d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q) v)
          (mfderiv OpenIC I d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q) w) := by
  simp only [normalizedDatum.positiveSideInsertionMetric, scaleMetric_inner]
  erw [insertedQuotientMetric_openRetained hA hAB (inv_pos.mpr d.precision_pos) _ _ q hq,
    normalizedDatum.controlledMetric_inner]
  rw [← mul_assoc, inv_mul_cancel₀ d.scalar_pos.ne', one_mul]

theorem staticWitness_openRetained (d : normalizedDatum g x₀ δ k)
    {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (s : CanonicalStaticInsertionWitness d A hA D m ε)
    (q : insertionCylinder A δ⁻¹) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    s.data.outMetric.inner (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos) q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos)) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos)) q w) =
        g.inner (d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q))
          (mfderiv OpenIC I d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q) v)
          (mfderiv OpenIC I d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q) w) := by
  rw [s.properties.outMetric_eq]
  exact physicalInsertionMetric_openRetained d.oriented hA s.properties.cut_fit q hq v w
end DifferentialGeometry.PDE.RicciFlow.StandardCap
