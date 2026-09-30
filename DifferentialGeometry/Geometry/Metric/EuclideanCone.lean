import DifferentialGeometry.Geometry.Metric.ConeDistanceTriangle

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace Metric

def EuclideanCone (Y : Type*) := Option ({r : ℝ // 0 < r} × Y)

namespace EuclideanCone

variable {Y : Type*}

def tip : EuclideanCone Y := none

def radius : EuclideanCone Y → ℝ
  | none => 0
  | some x => x.1

def mk (r : ℝ≥0) (u : Y) : EuclideanCone Y :=
  if hr : 0 < (r : ℝ) then some (⟨r, hr⟩, u) else tip

@[simp] theorem radius_tip : radius (tip : EuclideanCone Y) = 0 := rfl

@[simp] theorem radius_some (r : {r : ℝ // 0 < r}) (u : Y) :
    radius (some (r, u) : EuclideanCone Y) = r := rfl

theorem radius_nonneg (x : EuclideanCone Y) : 0 ≤ radius x := by
  cases x with
  | none => exact le_rfl
  | some x => exact x.1.property.le

@[simp] theorem mk_zero (u : Y) : mk 0 u = tip := by simp [mk]

theorem mk_pos {r : ℝ≥0} (hr : 0 < (r : ℝ)) (u : Y) :
    mk r u = some (⟨r, hr⟩, u) := dite_eq_left hr

@[simp] theorem radius_mk (r : ℝ≥0) (u : Y) : radius (mk r u) = r := by
  by_cases hr : 0 < (r : ℝ)
  · rw [mk_pos hr, radius_some]
  · have hz : r = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hr) r.property)
    subst r
    simp

theorem exists_positive_of_ne_tip {x : EuclideanCone Y} (hx : x ≠ tip) :
    ∃ (r : {r : ℝ // 0 < r}) (u : Y), x = some (r, u) := by
  cases x with
  | none => exact (hx rfl).elim
  | some x => exact ⟨x.1, x.2, rfl⟩

private def coneDist [PseudoMetricSpace Y] : EuclideanCone Y → EuclideanCone Y → ℝ
  | none, none => 0
  | none, some y => y.1
  | some x, none => x.1
  | some x, some y => coneDistance (x.1, x.2) (y.1, y.2)

private theorem scalar_zero_left [PseudoMetricSpace Y] (u : Y) (s : ℝ) (v : Y) :
    coneDistance (0, u) (s, v) = |s| := by
  simp [coneDistance, Real.sqrt_sq_eq_abs]

private theorem scalar_zero_right [PseudoMetricSpace Y] (r : ℝ) (u v : Y) :
    coneDistance (r, u) (0, v) = |r| := by
  rw [coneDistance_comm, scalar_zero_left]

private theorem scalar_le_sum [PseudoMetricSpace Y]
    (r s : {r : ℝ // 0 < r}) (u v : Y) :
    coneDistance ((r : ℝ), u) ((s : ℝ), v) ≤ r + s := by
  have h := coneDistance_triangle (x := ((r : ℝ), u)) (y := (0, u))
    (z := ((s : ℝ), v)) r.property.le le_rfl s.property.le
  simpa [scalar_zero_left, scalar_zero_right, abs_of_pos r.property,
    abs_of_pos s.property] using h

instance [MetricSpace Y] : MetricSpace (EuclideanCone Y) where
  dist := coneDist
  dist_self x := by
    cases x with
    | none => rfl
    | some x => exact coneDistance_self _
  dist_comm x y := by
    cases x <;> cases y
    · rfl
    · rfl
    · rfl
    · exact coneDistance_comm _ _
  dist_triangle x y z := by
    cases x with
    | none =>
      cases y with
      | none => cases z <;> simp [coneDist]
      | some y =>
        cases z with
        | none =>
          change (0 : ℝ) ≤ y.1.val + y.1.val
          linarith [y.1.property]
        | some z =>
          have h := abs_radius_sub_le_coneDistance (x := ((y.1 : ℝ), y.2))
            (y := ((z.1 : ℝ), z.2)) y.1.property.le z.1.property.le
          have hab := neg_le_abs ((y.1 : ℝ) - z.1)
          change (z.1 : ℝ) ≤ y.1 + coneDistance ((y.1 : ℝ), y.2) ((z.1 : ℝ), z.2)
          linarith
    | some x =>
      cases y with
      | none =>
        cases z with
        | none => simp [coneDist]
        | some z => exact scalar_le_sum x.1 z.1 x.2 z.2
      | some y =>
        cases z with
        | none =>
          have h := abs_radius_sub_le_coneDistance (x := ((x.1 : ℝ), x.2))
            (y := ((y.1 : ℝ), y.2)) x.1.property.le y.1.property.le
          have hab := le_abs_self ((x.1 : ℝ) - y.1)
          change (x.1 : ℝ) ≤ coneDistance ((x.1 : ℝ), x.2) ((y.1 : ℝ), y.2) + y.1
          linarith
        | some z => exact coneDistance_triangle x.1.property.le y.1.property.le z.1.property.le
  eq_of_dist_eq_zero := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim (y.1.property.ne' h)
    | some x =>
      cases y with
      | none => exact False.elim (x.1.property.ne' h)
      | some y =>
        have he := (coneDistance_eq_zero_iff x.1.property y.1.property).mp h
        have hr : x.1 = y.1 := Subtype.ext (congrArg Prod.fst he)
        have hu : x.2 = y.2 := congrArg (fun p : ℝ × Y => p.2) he
        exact congrArg some (Prod.ext hr hu)

variable [MetricSpace Y]

@[simp] theorem dist_some_some (r s : {r : ℝ // 0 < r}) (u v : Y) :
    @dist (EuclideanCone Y) _ (some (r, u)) (some (s, v)) =
      coneDistance ((r : ℝ), u) ((s : ℝ), v) := rfl

@[simp] theorem dist_tip (x : EuclideanCone Y) : dist x tip = radius x := by
  cases x <;> rfl

@[simp] theorem tip_dist (x : EuclideanCone Y) : dist tip x = radius x := by
  rw [dist_comm, dist_tip]

@[simp] theorem dist_mk (r s : ℝ≥0) (u v : Y) :
    dist (mk r u) (mk s v) = coneDistance ((r : ℝ), u) ((s : ℝ), v) := by
  by_cases hr : 0 < (r : ℝ)
  · by_cases hs : 0 < (s : ℝ)
    · rw [mk_pos hr, mk_pos hs, dist_some_some]
    · have hz : s = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hs) s.property)
      subst s
      rw [mk_zero, dist_tip, radius_mk, NNReal.coe_zero, scalar_zero_right, abs_of_pos hr]
  · have hz : r = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hr) r.property)
    subst r
    rw [mk_zero, tip_dist, radius_mk, NNReal.coe_zero, scalar_zero_left]
    exact (abs_of_nonneg s.property).symm

theorem abs_radius_sub_le_dist (x y : EuclideanCone Y) :
    |radius x - radius y| ≤ dist x y := by
  rw [← dist_tip x, ← dist_tip y]
  exact abs_dist_sub_le x y tip

theorem isometry_mk (u : Y) : Isometry (fun r : ℝ≥0 => mk r u) := by
  apply Isometry.of_dist_eq
  intro r s
  rw [dist_mk, coneDistance_same_direction]
  rfl


omit [MetricSpace Y] in
theorem radius_eq_zero_iff (x : EuclideanCone Y) : radius x = 0 ↔ x = tip := by
  cases x with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some x =>
    constructor
    · intro h
      exact (x.1.property.ne' h).elim
    · intro h
      cases h

omit [MetricSpace Y] in
@[simp] theorem mk_eq_tip_iff (r : ℝ≥0) (u : Y) : mk r u = tip ↔ r = 0 := by
  rw [← radius_eq_zero_iff, radius_mk, NNReal.coe_eq_zero]

omit [MetricSpace Y] in
theorem eq_tip_or_eq_mk (x : EuclideanCone Y) :
    x = tip ∨ ∃ (r : ℝ≥0) (u : Y), 0 < r ∧ x = mk r u := by
  cases x with
  | none => exact Or.inl rfl
  | some x =>
    refine Or.inr ⟨⟨x.1, x.1.property.le⟩, x.2, x.1.property, ?_⟩
    exact (mk_pos (r := ⟨x.1, x.1.property.le⟩) x.1.property x.2).symm

theorem lipschitzWith_radius : LipschitzWith 1 (radius : EuclideanCone Y → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_radius_sub_le_dist x y

def dilate (c : ℝ≥0) : EuclideanCone Y → EuclideanCone Y
  | none => tip
  | some x => mk (c * ⟨x.1, x.1.property.le⟩) x.2

omit [MetricSpace Y] in
@[simp] theorem dilate_tip (c : ℝ≥0) : dilate c (tip : EuclideanCone Y) = tip := rfl

omit [MetricSpace Y] in
@[simp] theorem dilate_mk (c r : ℝ≥0) (u : Y) : dilate c (mk r u) = mk (c * r) u := by
  by_cases hr : 0 < (r : ℝ)
  · rw [mk_pos hr]
    rfl
  · have hz : r = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hr) r.property)
    subst r
    simp

omit [MetricSpace Y] in
@[simp] theorem radius_dilate (c : ℝ≥0) (x : EuclideanCone Y) :
    radius (dilate c x) = c * radius x := by
  cases x with
  | none => simp only [show (none : EuclideanCone Y) = tip from rfl, dilate_tip, radius_tip, mul_zero]
  | some x =>
    change radius (mk (c * ⟨x.1, x.1.property.le⟩) x.2) = _
    rw [radius_mk]
    rfl

omit [MetricSpace Y] in
@[simp] theorem dilate_zero (x : EuclideanCone Y) : dilate 0 x = tip := by
  apply (radius_eq_zero_iff _).mp
  rw [radius_dilate, NNReal.coe_zero, zero_mul]

omit [MetricSpace Y] in
@[simp] theorem dilate_one (x : EuclideanCone Y) : dilate 1 x = x := by
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩ <;> simp

omit [MetricSpace Y] in
theorem dilate_mul (c d : ℝ≥0) (x : EuclideanCone Y) :
    dilate c (dilate d x) = dilate (c * d) x := by
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩ <;> simp [mul_assoc]

theorem dist_dilate (c : ℝ≥0) (x y : EuclideanCone Y) :
    dist (dilate c x) (dilate c y) = c * dist x y := by
  rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
  · simp
  · rcases eq_tip_or_eq_mk y with rfl | ⟨s, v, _, rfl⟩
    · simp
    · simp only [dilate_mk, dist_mk, NNReal.coe_mul]
      exact (coneDistance_radial_mul (c : ℝ) ((r : ℝ), u) ((s : ℝ), v)).trans
        (congrArg (fun a : ℝ => a * coneDistance ((r : ℝ), u) ((s : ℝ), v))
          (abs_of_nonneg c.property))

end EuclideanCone
end Metric
