import DifferentialGeometry.Topology.LocalDegree.Product
import DifferentialGeometry.Topology.LocalDegree.ReflectionDegree

set_option autoImplicit false
open Metric Set
noncomputable section
namespace Poincare.LocalDegree


def euclideanNegativeProductField {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) : EuclideanSpace ℝ (Fin ((d + 1) + 1)) :=
  (EuclideanProductEquator d).reflection (euclideanProductField F y)


@[simp]
theorem euclideanNegativeProductField_point {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanNegativeProductField F (euclideanProductPoint d v t) =
      euclideanProductPoint d (F v) (-t) := by
  unfold euclideanNegativeProductField
  rw [euclideanProductField_point]
  unfold euclideanProductPoint
  rw [map_add, Submodule.reflection_mem_subspace_eq_self
    ((euclideanProductCoordinates d).symm (F v)).property, map_smul,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg]
  simp only [smul_neg, neg_smul]

private theorem IsolatingRadius.reflection_comp {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {F : E → E} {x : E} {R : ℝ} (h : IsolatingRadius F x R) :
    IsolatingRadius (fun y ↦ K.reflection (F y)) x R where
  pos := h.pos
  continuousOn := K.reflection.continuous.comp_continuousOn h.continuousOn
  zero_iff y hy := K.reflection.map_eq_zero_iff.trans (h.zero_iff y hy)


theorem IsolatingRadius.euclideanNegativeProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin ((d + 1) + 1))} {R : ℝ}
    (h : IsolatingRadius (euclideanProductField F) x R) :
    IsolatingRadius (euclideanNegativeProductField F) x R :=
  h.reflection_comp (EuclideanProductEquator d)


theorem isolatedZero_euclideanNegativeProduct_at {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    isolatedZero (euclideanNegativeProductField F) (euclideanProductPoint d x 0) := by
  obtain ⟨R, hR⟩ := isolatedZero_euclideanProduct_at h
  exact ⟨R, hR.euclideanNegativeProduct⟩


theorem sphereMap_euclideanNegativeProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin ((d + 1) + 1))} {R : ℝ}
    (h : IsolatingRadius (euclideanProductField F) x R) (r : Ioc (0 : ℝ) R) :
    sphereMap (euclideanNegativeProductField F) x R
        (h.euclideanNegativeProduct).continuousOn
        (h.euclideanNegativeProduct).nonzero r =
      (unitSphereReflection (euclideanNorth (d + 1)).val).comp
        (sphereMap (euclideanProductField F) x R h.continuousOn h.nonzero r) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [sphereMap_apply, ContinuousMap.comp_apply, unitSphereReflection_apply]
  change ‖(EuclideanProductEquator d).reflection
      (euclideanProductField F (x + (r : ℝ) • v.val))‖⁻¹ •
      (EuclideanProductEquator d).reflection (euclideanProductField F (x + (r : ℝ) • v.val)) =
    (EuclideanProductEquator d).reflection
      (sphereMap (euclideanProductField F) x R h.continuousOn h.nonzero r v).val
  rw [sphereMap_apply, LinearIsometryEquiv.norm_map, map_smul]


theorem euclideanLocalDegree_negativeProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    euclideanLocalDegree (euclideanNegativeProductField F) (euclideanProductPoint d x 0)
        (isolatedZero_euclideanNegativeProduct_at h) = -euclideanLocalDegree F x h := by
  have hp := isolatedZero_euclideanProduct_at h
  have hR := hp.choose_spec
  let r : Ioc (0 : ℝ) hp.choose := ⟨hp.choose, hR.pos, le_rfl⟩
  have he := euclideanLocalDegree_eq_sphereDegree hp hR r
  rw [euclideanLocalDegree_eq_sphereDegree _
    (hR.euclideanNegativeProduct) r,
    sphereMap_euclideanNegativeProduct hR r, euclideanSphereDegree_comp,
    euclideanSphereDegree_reflection_unit, neg_one_mul, ← he,
    euclideanLocalDegree_product h]

end Poincare.LocalDegree
