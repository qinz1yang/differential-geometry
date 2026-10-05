import DifferentialGeometry.Geometry.Thurston.SphericalProductCyclicQuotient
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereBundle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensSpacePresentation
import DifferentialGeometry.Topology.ThreeManifold.AntipodalPresentation
import DifferentialGeometry.Geometry.Thurston.SphericalProductUniversalCover
import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedral
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawConnectedSumConsumers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawUniverseLift

/-!
Complete spherical-product structures have raw graph presentations via the actual two quotients.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff

namespace GC.GraphManifold

universe u

theorem nonempty_rawGraphPresentation_of_cyclicCylinderPresentation
    (Q : ConnectedClosedOrientedManifold.{u} 3)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (c : ℝ)
    (hA : LinearMap.det (A.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 3)) = 1)
    (hc : c ≠ 0)
    (pr : GC.Geometry.SphericalProduct.CylinderQuotientPresentation
      (Subgroup.zpowers (A, AffineIsometryEquiv.vaddConst ℝ c)) Q.Carrier) :
    Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
  obtain ⟨e⟩ := GC.Geometry.SphericalProduct.nonempty_diffeomorph_of_cyclic_presentation
    A c hA hc pr
  exact Assembly.exists_rawGraphPresentation_of_sphereTwoTimesCircle_diffeomorph
    (NoCuts.carrier Q) e

private theorem rawRecognition_toCircle_two_one : (ZMod.toCircle (1 : ZMod 2) : ℂ) = -1 := by
  have h := ZMod.toCircle_natCast (N := 2) 1
  norm_num at h
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I / 2) := h
    _ = Complex.exp (Real.pi * Complex.I) := by congr 1; ring
    _ = -1 := Complex.exp_pi_mul_I
private theorem rawRecognition_lensPairRotation_neg (u : Circle) (hu : (u : ℂ) = -1) :
    lensPairRotation u u = LinearIsometryEquiv.neg ℝ := by
  ext1 x
  apply lensCoordinates.injective
  rw [lensCoordinates_lensPairRotation]
  simp only [hu, neg_one_mul, LinearIsometryEquiv.coe_neg, map_neg]
  rw [WithLp.ext_iff]
  exact Prod.ext rfl rfl

private theorem rawRecognition_lensAction_two_one :
    lensSpaceFormAction 2 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
      LinearIsometryEquiv.neg ℝ := by
  rw [lensSpaceFormAction_apply, Int.cast_one, one_mul, toAdd_ofAdd]
  exact rawRecognition_lensPairRotation_neg _ rawRecognition_toCircle_two_one

open private antipodalIsometry from
  DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

theorem lensSpaceFormGroup_two_one_eq_antipodal (hpq : IsCoprime (2 : ℤ) 1) :
    lensSpaceFormGroup 2 1 hpq = SphericalSpaceFormGroup.antipodal := by
  have h : (lensSpaceFormGroup 2 1 hpq).group =
      SphericalSpaceFormGroup.antipodal.group := by
    ext g
    change (∃ k, lensSpaceFormAction 2 1 k = g) ↔ g = 1 ∨ g = antipodalIsometry
    constructor
    · rintro ⟨k, rfl⟩
      have hk : Multiplicative.toAdd k = 0 ∨ Multiplicative.toAdd k = 1 := by
        generalize Multiplicative.toAdd k = a
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hk with hk | hk
      · left
        have hzero : k = 1 := Multiplicative.toAdd.injective hk
        rw [hzero, map_one]
      · right
        have hone : k = Multiplicative.ofAdd (1 : ZMod 2) :=
          Multiplicative.toAdd.injective hk
        rw [hone, rawRecognition_lensAction_two_one]
        rfl
    · rintro (rfl | rfl)
      · exact ⟨1, map_one _⟩
      · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), rawRecognition_lensAction_two_one⟩
  generalize lensSpaceFormGroup 2 1 hpq = G at h
  generalize SphericalSpaceFormGroup.antipodal = H at h
  cases G
  cases H
  cases h
  rfl

theorem nonempty_rawGraphPresentation_antipodal :
    Nonempty (RawGraphPresentation
      (NoCuts.carrier SphericalSpaceFormGroup.antipodal.manifold)) := by
  have h := lensSpaceFormGroup_two_one_eq_antipodal isCoprime_one_right
  exact h ▸ (⟨lensSpaceRawGraphPresentation 2 1 isCoprime_one_right⟩ :
    Nonempty (RawGraphPresentation
      (NoCuts.carrier (lensSpaceFormGroup 2 1 isCoprime_one_right).manifold)))

theorem nonempty_rawGraphPresentation_projectiveThreeSpaceLift :
    Nonempty (RawGraphPresentation (NoCuts.carrier projectiveThreeSpaceLift.{u})) := by
  obtain ⟨R⟩ := nonempty_rawGraphPresentation_antipodal
  exact RawUniverseLift.nonempty_rawGraphPresentation_ulift.{u}
    SphericalSpaceFormGroup.antipodal.manifold R

theorem rawGraphPresentation_of_sphericalProduct_proved
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : GC.Geometry.GeometricStructure W.model W.Carrier)
    (hG : G.model = .sphericalProduct) : Nonempty (RawGraphPresentation W) := by
  obtain ⟨Q, e, hOrientation⟩ := Assembly.exists_closedModel_of_boundary_eq_empty W hboundary
  let H := G.pullback e.symm
  have hH : H.model = .sphericalProduct := hG
  obtain ⟨Γ, ⟨pr⟩, hClass⟩ :=
    GC.Geometry.SphericalProduct.exists_classified_presentation_of_universalCover
      GC.Geometry.SphericalProduct.sphericalProductUniversalCover Q H hH
  have hRaw : Nonempty (RawGraphPresentation (NoCuts.carrier Q)) := by
    rcases hClass with ⟨A, c, hA, hc, rfl⟩ | ⟨c₁, c₂, hne, rfl⟩
    · exact nonempty_rawGraphPresentation_of_cyclicCylinderPresentation Q A c hA hc pr
    · obtain ⟨f⟩ := GC.Geometry.SphericalProduct.dihedralCylinderQuotientIsProjectiveSum
        Q.Carrier c₁ c₂ hne pr
      obtain ⟨R⟩ := nonempty_rawGraphPresentation_projectiveThreeSpaceLift.{u}
      obtain ⟨S⟩ := rawGraphPresentation_connectedSum
        projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u} R R
      exact rawGraphPresentation_of_diffeomorph S f.symm
  obtain ⟨R⟩ := hRaw
  exact ⟨R.transport e.symm (Diffeomorph.preservesOrientation_symm hOrientation)⟩

end GC.GraphManifold
