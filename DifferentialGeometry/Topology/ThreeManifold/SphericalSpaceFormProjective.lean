import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private abbrev ProjectiveSphereSpace := EuclideanSpace ℝ (Fin 4)
private abbrev ProjectiveSphereThree := Metric.sphere (0 : ProjectiveSphereSpace) 1

private noncomputable def antipodalIsometry :
    ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace :=
  LinearIsometryEquiv.neg ℝ

private theorem antipodalIsometry_mul_self : antipodalIsometry * antipodalIsometry = 1 := by
  refine LinearIsometryEquiv.ext fun v => ?_
  simp [antipodalIsometry, LinearIsometryEquiv.coe_neg]

private theorem antipodalIsometry_inv : antipodalIsometry⁻¹ = antipodalIsometry := by
  rw [inv_eq_iff_mul_eq_one]
  exact antipodalIsometry_mul_self

private theorem antipodalIsometry_fixed_point_free (x : ProjectiveSphereThree) :
    DifferentialGeometry.Geometry.sphereDiffeo (n := 3) antipodalIsometry x ≠ x := by
  intro h
  have hx : -(x : ProjectiveSphereSpace) = (x : ProjectiveSphereSpace) := by
    have hval := congrArg (fun z : ProjectiveSphereThree => (z : ProjectiveSphereSpace)) h
    simpa [antipodalIsometry, LinearIsometryEquiv.coe_neg] using hval
  exact ne_neg_of_mem_unit_sphere ℝ x (Subtype.ext hx.symm)

private theorem antipodalIsometry_ne_one : antipodalIsometry ≠ 1 := by
  intro h
  have hx := antipodalIsometry_fixed_point_free
    (⟨EuclideanSpace.single 0 1, by simp⟩ : ProjectiveSphereThree)
  rw [h] at hx
  exact hx (Subtype.ext (by simp))

namespace SphericalSpaceFormGroup

noncomputable def antipodal : SphericalSpaceFormGroup where
  group :=
    { carrier := {g | g = 1 ∨ g = antipodalIsometry}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl antipodalIsometry_mul_self
      inv_mem' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact Or.inl inv_one
        · exact Or.inr antipodalIsometry_inv }
  finite := by
    have hfin : ({g : ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace |
        g = 1 ∨ g = antipodalIsometry} : Set _).Finite := by
      rw [show {g : ProjectiveSphereSpace ≃ₗᵢ[ℝ] ProjectiveSphereSpace |
          g = 1 ∨ g = antipodalIsometry} = insert antipodalIsometry {1} by
        ext g
        simp [or_comm]]
      exact (Set.finite_singleton 1).insert antipodalIsometry
    exact hfin.to_subtype
  positive := by
    intro γ
    rcases γ.2 with h | h
    · rw [h]
      exact DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _
        (by
          change LinearMap.det (1 : ProjectiveSphereSpace →ₗ[ℝ] ProjectiveSphereSpace) = 1
          exact LinearMap.det_id)
    · rw [h]
      exact DifferentialGeometry.Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free _
        antipodalIsometry_fixed_point_free
  free := by
    intro γ x hx
    rcases γ.2 with h | h
    · exact Subtype.ext h
    · rw [h] at hx
      exact absurd hx (antipodalIsometry_fixed_point_free x)

theorem not_subsingleton_antipodal_group : ¬ Subsingleton ↥antipodal.group := by
  intro h
  refine antipodalIsometry_ne_one (congrArg Subtype.val (h.elim
    (⟨antipodalIsometry, Or.inr rfl⟩ : ↥antipodal.group) 1))

theorem not_subsingleton_fundamentalGroup_antipodal (p : antipodal.manifold.Carrier) :
    ¬ Subsingleton (FundamentalGroup antipodal.manifold.Carrier p) := fun h =>
  not_subsingleton_antipodal_group
    (@Equiv.subsingleton _ _ (fundamentalGroupManifoldEquiv antipodal p).symm h)

theorem isStandardFactor_antipodal : isStandardFactor antipodal.manifold :=
  isStandardFactor_spherical antipodal

theorem exists_isStandardFactor_not_subsingleton_group :
    ∃ G : SphericalSpaceFormGroup, ¬ Subsingleton ↥G.group ∧ isStandardFactor G.manifold :=
  ⟨antipodal, not_subsingleton_antipodal_group, isStandardFactor_antipodal⟩

theorem exists_isStandardFactor_nonsimplyConnected :
    ∃ N : ConnectedClosedOrientedManifold.{0} 3, isStandardFactor N ∧
      ∀ p : N.Carrier, ¬ Subsingleton (FundamentalGroup N.Carrier p) :=
  ⟨antipodal.manifold, isStandardFactor_antipodal,
    not_subsingleton_fundamentalGroup_antipodal⟩

theorem isPoincareStandard_antipodal :
    isPoincareStandard antipodal.manifold.Carrier :=
  isPoincareStandard_of_standard_factor antipodal.manifold isStandardFactor_antipodal

theorem isPoincareStandard_connectedSum_antipodal :
    isPoincareStandard (connectedSum antipodal.manifold antipodal.manifold).Carrier :=
  isPoincareStandard_connectedSum_of_standardFactor antipodal.manifold antipodal.manifold
    isStandardFactor_antipodal isStandardFactor_antipodal

theorem nonempty_connectedSum_antipodal :
    Nonempty (connectedSum antipodal.manifold antipodal.manifold).Carrier :=
  inferInstance

end SphericalSpaceFormGroup

end DifferentialGeometry.Topology
