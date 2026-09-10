import DifferentialGeometry.Topology.LocalDegree.Product.Geometry
import DifferentialGeometry.Topology.LocalDegree.SphereSuspension
import DifferentialGeometry.Topology.LocalDegree.AffineCoordinate

set_option autoImplicit false
open Metric Set
noncomputable section
namespace Poincare.LocalDegree


abbrev EuclideanProductEquator (d : ℕ) := (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮ


def euclideanProductCoordinates (d : ℕ) :
    EuclideanProductEquator d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (d + 1)
    (ne_zero_of_mem_unit_sphere (euclideanNorth (d + 1)))).repr


@[simp]
theorem euclideanProductCoordinates_sphere (d : ℕ)
    (v : sphere (0 : EuclideanProductEquator d) 1) :
    (euclideanSuspensionEquatorHomeomorph d v).val = euclideanProductCoordinates d v.val := rfl


@[simp]
theorem euclideanProductCoordinates_symm_sphere (d : ℕ) (v : EuclideanSphere d) :
    ((euclideanSuspensionEquatorHomeomorph d).symm v).val =
      (euclideanProductCoordinates d).symm v.val := rfl


def euclideanEquatorialField {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanProductEquator d) : EuclideanProductEquator d :=
  (euclideanProductCoordinates d).symm (F (euclideanProductCoordinates d x))


def euclideanProductField {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) → EuclideanSpace ℝ (Fin ((d + 1) + 1)) :=
  orthogonalProductField (EuclideanProductEquator d) (euclideanEquatorialField F)


def euclideanProductPoint (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) :=
  ((euclideanProductCoordinates d).symm v : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    t • (euclideanNorth (d + 1)).val


@[simp]
theorem euclideanProductPoint_projection (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    (EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t) =
      (euclideanProductCoordinates d).symm v := by
  simp [euclideanProductPoint, map_add, map_smul,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]


theorem euclideanProductPoint_orthogonalProjection (d : ℕ)
    (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d v t) =
      t • (euclideanNorth (d + 1)).val := by
  rw [Submodule.starProjection_orthogonal_val]
  change euclideanProductPoint d v t -
    ((EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t) :
      EuclideanSpace ℝ (Fin ((d + 1) + 1))) = _
  rw [euclideanProductPoint_projection]
  exact add_sub_cancel_left _ _


@[simp]
theorem euclideanProductField_point {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanProductField F (euclideanProductPoint d v t) = euclideanProductPoint d (F v) t := by
  change ((euclideanProductCoordinates d).symm
    (F (euclideanProductCoordinates d
      ((EuclideanProductEquator d).orthogonalProjectionOnto (euclideanProductPoint d v t)))) :
        EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d v t) = _
  rw [euclideanProductPoint_projection, LinearIsometryEquiv.apply_symm_apply,
    euclideanProductPoint_orthogonalProjection]
  rfl


@[simp]
theorem euclideanProductPoint_height (d : ℕ) (v : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    inner ℝ (euclideanNorth (d + 1)).val (euclideanProductPoint d v t) = t := by
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((euclideanProductCoordinates d).symm v).property
  change inner ℝ (euclideanNorth (d + 1)).val
    (((euclideanProductCoordinates d).symm v : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
      t • (euclideanNorth (d + 1)).val) = t
  rw [inner_add_right, hi, inner_smul_right]
  simp [norm_eq_of_mem_sphere]


theorem euclideanProduct_orthogonalProjection (d : ℕ)
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    (EuclideanProductEquator d)ᗮ.starProjection y =
      inner ℝ (euclideanNorth (d + 1)).val y • (euclideanNorth (d + 1)).val := by
  change (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮᗮ.starProjection y = _
  simp only [Submodule.orthogonal_orthogonal,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere (euclideanNorth (d + 1)))]


theorem euclideanProductPoint_reconstruct (d : ℕ)
    (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanProductPoint d
      (euclideanProductCoordinates d ((EuclideanProductEquator d).orthogonalProjectionOnto y))
      (inner ℝ (euclideanNorth (d + 1)).val y) = y := by
  unfold euclideanProductPoint
  rw [LinearIsometryEquiv.symm_apply_apply, ← euclideanProduct_orthogonalProjection]
  exact (EuclideanProductEquator d).starProjection_add_starProjection_orthogonal y


def euclideanProductChart (d : ℕ) :
    EuclideanSpace ℝ (Fin ((d + 1) + 1)) ≃L[ℝ] (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun y ↦ (euclideanProductCoordinates d
      ((EuclideanProductEquator d).orthogonalProjectionOnto y),
      inner ℝ (euclideanNorth (d + 1)).val y)
    invFun := fun p ↦ euclideanProductPoint d p.1 p.2
    left_inv := euclideanProductPoint_reconstruct d
    right_inv := by intro p; ext <;> simp
    map_add' := by intro x y; ext <;> simp [map_add, inner_add_right]
    map_smul' := by intro c x; ext <;> simp [map_smul, inner_smul_right] }


@[simp]
theorem euclideanProductChart_symm_apply (d : ℕ) (p : EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :
    (euclideanProductChart d).symm p = euclideanProductPoint d p.1 p.2 := rfl


theorem euclideanProductChart_field {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (p : EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :
    euclideanProductChart d (euclideanProductField F ((euclideanProductChart d).symm p)) =
      (F p.1, p.2) := by
  rw [euclideanProductChart_symm_apply, euclideanProductField_point]
  exact (euclideanProductChart d).apply_symm_apply (F p.1, p.2)


theorem IsolatingRadius.euclideanEquator {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) :
    IsolatingRadius (euclideanEquatorialField F) 0 R := by
  have hm : MapsTo (euclideanProductCoordinates d)
      (closedBall (0 : EuclideanProductEquator d) R)
      (closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) R) := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  refine ⟨h.pos, ?_, ?_⟩
  · exact (euclideanProductCoordinates d).symm.continuous.comp_continuousOn
      (h.continuousOn.comp (euclideanProductCoordinates d).continuous.continuousOn hm)
  · intro x hx
    change (euclideanProductCoordinates d).symm (F (euclideanProductCoordinates d x)) = 0 ↔ x = 0
    rw [(euclideanProductCoordinates d).symm.map_eq_zero_iff, h.zero_iff _ (hm hx),
      (euclideanProductCoordinates d).map_eq_zero_iff]


theorem IsolatingRadius.euclideanProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) :
    IsolatingRadius (euclideanProductField F) 0 R :=
  h.euclideanEquator.orthogonalProduct (EuclideanProductEquator d)


theorem isolatedZero_euclideanProduct {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (h : isolatedZero F 0) : isolatedZero (euclideanProductField F) 0 :=
  ⟨h.choose, h.choose_spec.euclideanProduct⟩


theorem sphereMap_euclideanEquatorialField {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) :
    sphereMap (euclideanEquatorialField F) 0 R h.euclideanEquator.continuousOn
        h.euclideanEquator.nonzero r =
      euclideanSuspensionEquatorMap (sphereMap F 0 R h.continuousOn h.nonzero r) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [sphereMap_apply]
  change ‖(euclideanProductCoordinates d).symm
      (F (euclideanProductCoordinates d (0 + (r : ℝ) • v.val)))‖⁻¹ •
      (euclideanProductCoordinates d).symm
        (F (euclideanProductCoordinates d (0 + (r : ℝ) • v.val))) =
    (euclideanProductCoordinates d).symm
      (sphereMap F 0 R h.continuousOn h.nonzero r (euclideanSuspensionEquatorHomeomorph d v)).val
  rw [sphereMap_apply, zero_add, zero_add, map_smul,
    LinearIsometryEquiv.norm_map, euclideanProductCoordinates_sphere, map_smul]


def euclideanProductSphereHomotopy {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {R : ℝ} (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) :
    (sphereMap (euclideanProductField F) 0 R h.euclideanProduct.continuousOn
        h.euclideanProduct.nonzero r).Homotopy
      (euclideanSphereSuspension (sphereMap F 0 R h.continuousOn h.nonzero r)) :=
  (orthogonalProductSphereHomotopy (EuclideanProductEquator d) h.euclideanEquator r).cast
    rfl (by rw [sphereMap_euclideanEquatorialField h r]; rfl)


theorem euclideanLocalDegree_product_zero {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (h : isolatedZero F 0) :
    euclideanLocalDegree (euclideanProductField F) 0 (isolatedZero_euclideanProduct h) =
      euclideanLocalDegree F 0 h := by
  have hR := h.choose_spec
  let r : Ioc (0 : ℝ) h.choose := ⟨h.choose, hR.pos, le_rfl⟩
  rw [euclideanLocalDegree_eq_sphereDegree _ hR.euclideanProduct r,
    euclideanLocalDegree_eq_sphereDegree h hR r,
    euclideanSphereDegree_eq_of_homotopy (euclideanProductSphereHomotopy hR r),
    euclideanSphereDegree_suspension]


theorem euclideanProductField_translate {d : ℕ}
    (F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (y : EuclideanSpace ℝ (Fin ((d + 1) + 1))) :
    euclideanProductField F (euclideanProductPoint d x 0 + y) =
      euclideanProductField (fun v ↦ F (x + v)) y := by
  change ((euclideanProductCoordinates d).symm
    (F (euclideanProductCoordinates d ((EuclideanProductEquator d).orthogonalProjectionOnto
      (euclideanProductPoint d x 0 + y)))) : EuclideanSpace ℝ (Fin ((d + 1) + 1))) +
    (EuclideanProductEquator d)ᗮ.starProjection (euclideanProductPoint d x 0 + y) = _
  rw [map_add, euclideanProductPoint_projection, map_add,
    LinearIsometryEquiv.apply_symm_apply, map_add, euclideanProductPoint_orthogonalProjection,
    zero_smul, zero_add]
  rfl

private theorem isolatedZero_translate {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {F : D → D} {x : D} (h : isolatedZero F x) : isolatedZero (fun y ↦ F (x + y)) 0 := by
  simpa using isolatedZero_affineCoordinate (ContinuousLinearEquiv.refl ℝ D) 0 x h

private theorem localDegree_translate {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    euclideanLocalDegree (fun y ↦ F (x + y)) 0 (isolatedZero_translate h) =
      euclideanLocalDegree F x h := by
  simpa using euclideanLocalDegree_affineCoordinate
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (d + 1)))) 0 x h


theorem isolatedZero_euclideanProduct_at {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    isolatedZero (euclideanProductField F) (euclideanProductPoint d x 0) := by
  have hshift := isolatedZero_euclideanProduct (isolatedZero_translate h)
  have hh := isolatedZero_affineCoordinate
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))))
    (euclideanProductPoint d x 0) 0 hshift
  have heq : (fun y ↦ euclideanProductField (fun v ↦ F (x + v))
      (y - euclideanProductPoint d x 0)) = euclideanProductField F := by
    funext y
    rw [← euclideanProductField_translate, add_sub_cancel]
  simpa only [ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.refl_symm, zero_add, heq] using hh


theorem euclideanLocalDegree_product {d : ℕ}
    {F : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero F x) :
    euclideanLocalDegree (euclideanProductField F) (euclideanProductPoint d x 0)
        (isolatedZero_euclideanProduct_at h) = euclideanLocalDegree F x h := by
  have heq : (fun y ↦ euclideanProductField F (euclideanProductPoint d x 0 + y)) =
      euclideanProductField (fun v ↦ F (x + v)) :=
    funext (euclideanProductField_translate F x)
  have hp := localDegree_translate (isolatedZero_euclideanProduct_at h)
  have hp' : euclideanLocalDegree (euclideanProductField (fun v ↦ F (x + v))) 0
      (isolatedZero_euclideanProduct (isolatedZero_translate h)) =
    euclideanLocalDegree (euclideanProductField F) (euclideanProductPoint d x 0)
      (isolatedZero_euclideanProduct_at h) := by
    simpa only [heq] using hp
  rw [← hp', euclideanLocalDegree_product_zero (isolatedZero_translate h), localDegree_translate h]

end Poincare.LocalDegree
