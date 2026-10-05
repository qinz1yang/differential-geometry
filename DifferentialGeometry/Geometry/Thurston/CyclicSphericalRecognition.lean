import DifferentialGeometry.Geometry.Thurston.CyclicSphericalRaw
import DifferentialGeometry.Geometry.Thurston.CyclicRotationLens
import DifferentialGeometry.Geometry.Thurston.CyclicRootLens
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Every finite free cyclic orthogonal action is conjugate to an actual lens action. Its lifted sphere
quotient receives the two-solid-torus Raw presentation through its constructed quotient
diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Seifert GC.Endpoint
open scoped Manifold ContDiff

universe u

namespace GC.Geometry.SphericalCyclic

private theorem group_ext (G H : SphericalSpaceFormGroup) (h : G.group = H.group) : G = H := by
  cases G
  cases H
  cases h
  rfl

theorem exists_cyclic_lens_group_conjugacy (G : SphericalSpaceFormGroup)
    [cyclic : IsCyclic G.group] : ∃ p : ℕ, ∃ hp : NeZero p, ∃ q : ℤ,
    ∃ hpq : IsCoprime (p : ℤ) q,
    ∃ φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      conjSphericalSpaceFormGroup G φ = @lensSpaceFormGroup p hp q hpq := by
  obtain ⟨γ, hgen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp cyclic
  have hgroup : G.group = Subgroup.zpowers γ.val := by
    apply le_antisymm
    · intro g hg
      have hh : (⟨g, hg⟩ : G.group) ∈ Subgroup.zpowers γ := by rw [hgen]; trivial
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr γ.property
  have hp : NeZero (orderOf γ) := ⟨(orderOf_pos γ).ne'⟩
  have orderNonzero : NeZero (orderOf γ) := hp
  obtain ⟨u, v, φ, hc, hu, hv⟩ := exists_free_lens_rotation_all_orders G γ
  obtain ⟨q, hpq, hroots⟩ := lensPairRotation_zpowers_of_primitive_roots (orderOf γ) u v hu hv
  refine ⟨orderOf γ, hp, q, hpq, φ, ?_⟩
  apply group_ext
  change G.group.map (MulAut.conj φ) = (lensSpaceFormGroup (orderOf γ) q hpq).group
  have hc' : MulAut.conj φ γ.val = lensPairRotation u v := hc
  calc
    G.group.map (MulAut.conj φ) = (Subgroup.zpowers γ.val).map (MulAut.conj φ) :=
      congrArg (fun H => H.map (MulAut.conj φ).toMonoidHom) hgroup
    _ = Subgroup.zpowers (MulAut.conj φ γ.val) :=
      MonoidHom.map_zpowers (MulAut.conj φ).toMonoidHom γ.val
    _ = (lensSpaceFormGroup (orderOf γ) q hpq).group := by rw [hc', hroots]

end GC.Geometry.SphericalCyclic

namespace GC.GraphManifold

attribute [local instance] uliftChartedSpace isManifold_ulift

theorem exists_rawGraphPresentation_spherical_cyclic (G : SphericalSpaceFormGroup)
    [cyclic : IsCyclic G.group] :
    ∃ R : RawGraphPresentation (NoCuts.carrier G.manifold.ulift.{0, u}),
      R.components.count = 2 ∧ R.pairing.count = 1 ∧ R.externalCount = 0 := by
  obtain ⟨p, hp, q, hpq, φ, hc⟩ :=
    GC.Geometry.SphericalCyclic.exists_cyclic_lens_group_conjugacy G
  have lensOrderNonzero : NeZero p := hp
  let d : G.manifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (lensSpaceFormGroup p q hpq).manifold.Carrier := by
    rw [← hc]
    exact conjOrbitDiffeomorph G φ
  let e : G.manifold.ulift.{0, u}.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (lensSpaceLift.{u} p q hpq).Carrier :=
    ((uliftDiffeomorph.{0, u} (𝓡 3) G.manifold.Carrier).symm.trans d).trans
      (uliftDiffeomorph.{0, u} (𝓡 3) (lensSpaceFormGroup p q hpq).manifold.Carrier)
  exact exists_rawGraphPresentation_of_lensSpaceLift_diffeomorph p q hpq e

theorem rawGraphPresentation_of_sphericalSpaceForm_cyclic (G : SphericalSpaceFormGroup)
    [cyclic : IsCyclic G.group] :
    Nonempty (RawGraphPresentation (NoCuts.carrier G.manifold.ulift.{0, u})) := by
  obtain ⟨R, hR⟩ := exists_rawGraphPresentation_spherical_cyclic.{u} G
  exact ⟨R⟩

end GC.GraphManifold
