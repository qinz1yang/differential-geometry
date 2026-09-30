import DifferentialGeometry.Geometry.Metric.EuclideanCone

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace Metric.EuclideanCone

variable {Y Z : Type*}

def map (f : Y → Z) : EuclideanCone Y → EuclideanCone Z :=
  Option.map (fun x => (x.1, f x.2))

@[simp] theorem map_tip (f : Y → Z) : map f tip = tip := rfl

@[simp] theorem map_mk (f : Y → Z) (r : ℝ≥0) (u : Y) :
    map f (mk r u) = mk r (f u) := by
  by_cases hr : 0 < (r : ℝ)
  · rw [mk_pos hr, mk_pos hr]
    rfl
  · have hz : r = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hr) r.property)
    subst r
    simp only [mk_zero, map_tip]

@[simp] theorem radius_map (f : Y → Z) (x : EuclideanCone Y) :
    radius (map f x) = radius x := by
  cases x <;> rfl

@[simp] theorem map_dilate (f : Y → Z) (c : ℝ≥0) (x : EuclideanCone Y) :
    map f (dilate c x) = dilate c (map f x) := by
  cases x with
  | none => rfl
  | some x => exact map_mk f _ _

variable [MetricSpace Y] [MetricSpace Z]

theorem isometry_map (f : Y → Z) (hf : Isometry f) : Isometry (map f) := by
  apply Isometry.of_dist_eq
  intro x y
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · simp
  · rcases eq_tip_or_eq_mk y with rfl | ⟨s, v, _, rfl⟩
    · simp
    · simp only [map_mk, dist_mk, coneDistance, hf.dist_eq]

def congr (e : Y ≃ᵢ Z) : EuclideanCone Y ≃ᵢ EuclideanCone Z where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    cases x with
    | none => rfl
    | some x =>
      simp only [map, Option.map_some, IsometryEquiv.symm_apply_apply]
      rfl
  right_inv x := by
    cases x with
    | none => rfl
    | some x =>
      simp only [map, Option.map_some, IsometryEquiv.apply_symm_apply]
      rfl
  isometry_toFun := isometry_map e e.isometry

@[simp] theorem congr_apply (e : Y ≃ᵢ Z) (x : EuclideanCone Y) :
    congr e x = map e x := rfl

end Metric.EuclideanCone
