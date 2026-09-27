import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Bundle Manifold ContDiff
open DifferentialGeometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def IsUnitTangent (g : SmoothRiemannianMetric I M) {x : M}
    (v : TangentSpace I x) : Prop :=
  g.inner x v v = 1

def tangentAngle (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) : ℝ :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  InnerProductGeometry.angle v w

theorem tangentAngle_eq_arccos (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentAngle g v w =
      Real.arccos
        (g.inner x v w /
          (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w))) := by
  unfold tangentAngle InnerProductGeometry.angle
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  rfl


theorem tangentAngle_nonneg (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    0 ≤ tangentAngle g v w := by
  unfold tangentAngle
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact InnerProductGeometry.angle_nonneg v w


theorem tangentAngle_le_pi (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentAngle g v w ≤ Real.pi := by
  unfold tangentAngle
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact InnerProductGeometry.angle_le_pi v w


theorem tangentAngle_mem_Icc (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentAngle g v w ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨tangentAngle_nonneg g v w, tangentAngle_le_pi g v w⟩


theorem tangentAngle_comm (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentAngle g v w = tangentAngle g w v := by
  unfold tangentAngle
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact InnerProductGeometry.angle_comm v w

theorem cos_tangentAngle (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    Real.cos (tangentAngle g v w) =
      g.inner x v w /
        (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by
  unfold tangentAngle
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [InnerProductGeometry.cos_angle, norm_eq_sqrt_real_inner,
    norm_eq_sqrt_real_inner]
  rfl

theorem cos_tangentAngle_of_unit (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x} (hv : IsUnitTangent g v)
    (hw : IsUnitTangent g w) :
    Real.cos (tangentAngle g v w) = g.inner x v w := by
  rw [cos_tangentAngle, hv, hw, Real.sqrt_one, one_mul, div_one]


theorem sin_tangentAngle_nonneg (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    0 ≤ Real.sin (tangentAngle g v w) := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (tangentAngle_nonneg g v w) (tangentAngle_le_pi g v w)

theorem sin_half_tangentAngle_nonneg (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    0 ≤ Real.sin (tangentAngle g v w / 2) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith [tangentAngle_nonneg g v w]
  · linarith [tangentAngle_le_pi g v w, Real.pi_pos]

theorem two_mul_sin_sq_half_tangentAngle
    (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    2 * Real.sin (tangentAngle g v w / 2) ^ 2 =
      1 - Real.cos (tangentAngle g v w) := by
  have h := Real.cos_two_mul_eq_one_sub (tangentAngle g v w / 2)
  rw [show 2 * (tangentAngle g v w / 2) = tangentAngle g v w by ring] at h
  linarith

theorem two_mul_sin_sq_half_tangentAngle_of_unit
    (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x} (hv : IsUnitTangent g v)
    (hw : IsUnitTangent g w) :
    2 * Real.sin (tangentAngle g v w / 2) ^ 2 =
      1 - g.inner x v w := by
  rw [two_mul_sin_sq_half_tangentAngle,
    cos_tangentAngle_of_unit g hv hw]


theorem sin_half_tangentAngle_eq_sqrt
    (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    Real.sin (tangentAngle g v w / 2) =
      Real.sqrt ((1 - Real.cos (tangentAngle g v w)) / 2) := by
  apply Real.sin_half_eq_sqrt
  · exact tangentAngle_nonneg g v w
  · linarith [tangentAngle_le_pi g v w, Real.pi_pos]


theorem sin_half_tangentAngle_eq_sqrt_of_unit
    (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x} (hv : IsUnitTangent g v)
    (hw : IsUnitTangent g w) :
    Real.sin (tangentAngle g v w / 2) =
      Real.sqrt ((1 - g.inner x v w) / 2) := by
  rw [sin_half_tangentAngle_eq_sqrt,
    cos_tangentAngle_of_unit g hv hw]

end DifferentialGeometry.Geometry
