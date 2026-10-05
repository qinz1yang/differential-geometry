import DifferentialGeometry.Geometry.Thurston.SphericalScrew
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
Finite left-quaternion groups act freely and positively on the round three-sphere and preserve
its actual Hopf fibration. The eight quaternion units construct a noncyclic spherical action,
with its group equivalence and Hopf equivariance retained for quotient Seifert constructions.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace GC.Geometry

def quaternionLeftHom : unitary (Quaternion ℝ) →*
    (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) where
  toFun q := s3Act (q, 1)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    apply s3Quat.injective
    rw [s3Act_apply]
    simp [s3FibreUnit_zero]
  map_mul' q r := by
    apply LinearIsometryEquiv.ext
    intro x
    apply s3Quat.injective
    change s3Quat (s3Act (q * r, 1) x) = s3Quat (s3Act (q, 1) (s3Act (r, 1) x))
    rw [s3Act_apply, s3Act_apply, s3Act_apply]
    simp [s3FibreUnit_zero, mul_assoc]

theorem quaternionLeftHom_apply (q : unitary (Quaternion ℝ))
    (x : EuclideanSpace ℝ (Fin 4)) :
    s3Quat (quaternionLeftHom q x) = (q : Quaternion ℝ) * s3Quat x := by
  rw [show quaternionLeftHom q = s3Act (q, 1) from rfl, s3Act_apply]
  simp [s3FibreUnit_zero]

theorem quaternionLeftHom_injective : Function.Injective quaternionLeftHom := by
  intro q r h
  apply Subtype.ext
  have he := congrArg (fun A => s3Quat (A (s3Quat.symm 1))) h
  simpa only [quaternionLeftHom_apply, s3Quat.apply_symm_apply, mul_one] using he

private theorem quaternionLeft_fixed (q : unitary (Quaternion ℝ))
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : Geometry.sphereDiffeo (n := 3) (quaternionLeftHom q) x = x) : q = 1 := by
  have hval := congrArg (fun y => s3Quat y.val) hx
  change s3Quat (quaternionLeftHom q x) = s3Quat x at hval
  rw [quaternionLeftHom_apply] at hval
  have hn : s3Quat x ≠ 0 := by
    intro h
    have hx0 : (x : EuclideanSpace ℝ (Fin 4)) = 0 := s3Quat.injective (h.trans (map_zero _).symm)
    have hm := mem_sphere_zero_iff_norm.mp x.property
    rw [hx0, norm_zero] at hm
    norm_num at hm
  apply Subtype.ext
  exact mul_right_cancel₀ hn (hval.trans (one_mul _).symm)

def quaternionLeftSpaceForm (H : Subgroup (unitary (Quaternion ℝ))) [instH : Finite H] :
    SphericalSpaceFormGroup where
  group := H.map quaternionLeftHom
  finite := Finite.of_surjective
    (fun q : H => (⟨quaternionLeftHom q.val,
      Subgroup.mem_map.mpr ⟨q.val, q.property, rfl⟩⟩ : H.map quaternionLeftHom))
    (by
      intro γ
      obtain ⟨q, hq, he⟩ := γ.property
      exact ⟨⟨q, hq⟩, Subtype.ext he⟩)
  positive := by
    intro γ
    by_cases he : γ = 1
    · have hv : γ.val = 1 := congrArg Subtype.val he
      rw [hv]
      exact Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _ LinearMap.det_id
    · apply Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free
      intro x hx
      obtain ⟨q, hq, hγ⟩ := γ.property
      have hfix : Geometry.sphereDiffeo (n := 3) (quaternionLeftHom q) x = x := by
        rw [hγ]
        exact hx
      have hq1 := quaternionLeft_fixed q x hfix
      apply he
      apply Subtype.ext
      simp only [← hγ, hq1, map_one, Subgroup.coe_one]
  free := by
    intro γ x hx
    obtain ⟨q, hq, hγ⟩ := γ.property
    have hfix : Geometry.sphereDiffeo (n := 3) (quaternionLeftHom q) x = x := by
      rw [hγ]
      exact hx
    have hq1 := quaternionLeft_fixed q x hfix
    apply Subtype.ext
    simp only [← hγ, hq1, map_one, Subgroup.coe_one]

def quaternionLeftSpaceFormEquiv (H : Subgroup (unitary (Quaternion ℝ))) [instH : Finite H] :
    H ≃* (@quaternionLeftSpaceForm H instH).group :=
  H.equivMapOfInjective quaternionLeftHom quaternionLeftHom_injective

theorem quaternionLeftSpaceForm_hopf (H : Subgroup (unitary (Quaternion ℝ)))
    [instH : Finite H] (γ : H) (x : EuclideanSpace ℝ (Fin 4)) :
    hopfS3 ((@quaternionLeftSpaceFormEquiv H instH γ).val x) = quatRotate γ.val (hopfS3 x) :=
  hopfS3_s3Act (γ.val, 1) x

private def quaternionEightValue : QuaternionGroup 2 → Quaternion ℝ
  | .a i => ![(1 : Quaternion ℝ), ⟨0, 1, 0, 0⟩, -1, ⟨0, -1, 0, 0⟩] i
  | .xa i => ![⟨0, 0, 1, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 1⟩] i

private theorem quaternionEightValue_unitary (q : QuaternionGroup 2) :
    quaternionEightValue q ∈ unitary (Quaternion ℝ) := by
  apply Unitary.mem_iff.mpr
  have hn : Quaternion.normSq (quaternionEightValue q) = 1 := by
    cases q with
    | a i => fin_cases i <;> norm_num [quaternionEightValue, Quaternion.normSq_def']
    | xa i => fin_cases i <;> norm_num [quaternionEightValue, Quaternion.normSq_def']
  constructor
  · rw [Quaternion.star_mul_self, hn]
    rfl
  · rw [Quaternion.self_mul_star, hn]
    rfl

private theorem quaternionEightValue_mul (q r : QuaternionGroup 2) :
    quaternionEightValue (q * r) = quaternionEightValue q * quaternionEightValue r := by
  rcases q with i | i <;> rcases r with j | j
  all_goals simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
    QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
  all_goals fin_cases i <;> fin_cases j
  all_goals first
  | change (1 : Quaternion ℝ) = _
  | change (-1 : Quaternion ℝ) = _
  | change (⟨0, 1, 0, 0⟩ : Quaternion ℝ) = _
  | change (⟨0, -1, 0, 0⟩ : Quaternion ℝ) = _
  | change (⟨0, 0, 1, 0⟩ : Quaternion ℝ) = _
  | change (⟨0, 0, -1, 0⟩ : Quaternion ℝ) = _
  | change (⟨0, 0, 0, 1⟩ : Quaternion ℝ) = _
  | change (⟨0, 0, 0, -1⟩ : Quaternion ℝ) = _
  all_goals apply Quaternion.ext <;> norm_num [quaternionEightValue]

def quaternionEightHom : QuaternionGroup 2 →* unitary (Quaternion ℝ) where
  toFun q := ⟨quaternionEightValue q, quaternionEightValue_unitary q⟩
  map_one' := Subtype.ext (by rfl)
  map_mul' q r := Subtype.ext (quaternionEightValue_mul q r)

theorem quaternionEightHom_injective : Function.Injective quaternionEightHom := by
  intro q r h
  have hv := congrArg Subtype.val h
  cases q with
  | a i =>
    cases r with
    | a j =>
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | norm_num [quaternionEightHom, quaternionEightValue, Quaternion.ext_iff] at hv
    | xa j =>
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | norm_num [quaternionEightHom, quaternionEightValue, Quaternion.ext_iff] at hv
  | xa i =>
    cases r with
    | a j =>
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | norm_num [quaternionEightHom, quaternionEightValue, Quaternion.ext_iff] at hv
    | xa j =>
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | norm_num [quaternionEightHom, quaternionEightValue, Quaternion.ext_iff] at hv

private instance instQuaternionEightRangeFinite : Finite quaternionEightHom.range :=
  Finite.of_surjective quaternionEightHom.rangeRestrict quaternionEightHom.rangeRestrict_surjective

def quaternionEightSpaceForm : SphericalSpaceFormGroup :=
  quaternionLeftSpaceForm quaternionEightHom.range

def quaternionEightSpaceFormEquiv : QuaternionGroup 2 ≃* quaternionEightSpaceForm.group :=
  (MonoidHom.ofInjective quaternionEightHom_injective).trans
    (quaternionLeftSpaceFormEquiv quaternionEightHom.range)

theorem quaternionEightSpaceForm_card : Nat.card quaternionEightSpaceForm.group = 8 := by
  rw [← Nat.card_congr quaternionEightSpaceFormEquiv.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

theorem quaternionEightSpaceForm_noncommutative :
    ∃ γ δ : quaternionEightSpaceForm.group, γ * δ ≠ δ * γ := by
  refine ⟨quaternionEightSpaceFormEquiv (.a 1), quaternionEightSpaceFormEquiv (.xa 0), ?_⟩
  intro h
  have he := quaternionEightSpaceFormEquiv.injective
    ((quaternionEightSpaceFormEquiv.map_mul _ _).trans
      (h.trans (quaternionEightSpaceFormEquiv.map_mul _ _).symm))
  have hn : (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1 := by decide
  exact hn he

end GC.Geometry
