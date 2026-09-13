import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import DifferentialGeometry.Topology.Manifold.SphereLinearIsometry
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSphericalSpaceFormReduction

set_option autoImplicit false
noncomputable section

open Manifold Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev W4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : W4) 1
private local instance instFact : Fact (Module.finrank ℝ W4 = 3 + 1) := ⟨by simp⟩

noncomputable def conjSphericalSpaceFormGroupSubgroup (G : SphericalSpaceFormGroup)
    (φ : W4 ≃ₗᵢ[ℝ] W4) : Subgroup (W4 ≃ₗᵢ[ℝ] W4) :=
  G.group.map (MulAut.conj φ)

theorem conjSphericalSpaceFormGroupSubgroup_finite (G : SphericalSpaceFormGroup)
    (φ : W4 ≃ₗᵢ[ℝ] W4) : Finite ↥(conjSphericalSpaceFormGroupSubgroup G φ) :=
  Finite.of_surjective (fun γ : G.group =>
    (⟨(MulAut.conj φ) γ.val, ⟨γ.val, γ.2, rfl⟩⟩ :
      ↥(conjSphericalSpaceFormGroupSubgroup G φ)))
    (fun η => by
      obtain ⟨γ₀, hγ₀G, hγ₀⟩ := Subgroup.mem_map.mp η.2
      exact ⟨⟨γ₀, hγ₀G⟩, Subtype.ext hγ₀⟩)

theorem sphereDiffeo_conj_apply_iff (φ γ : W4 ≃ₗᵢ[ℝ] W4) (x : S3) :
    Geometry.sphereDiffeo (n := 3) (MulAut.conj φ γ) x = x ↔
      Geometry.sphereDiffeo (n := 3) γ (Geometry.sphereDiffeo (n := 3) φ.symm x) =
        Geometry.sphereDiffeo (n := 3) φ.symm x := by
  constructor
  · intro h
    have hE : ((MulAut.conj φ γ) (x : W4)) = (x : W4) := by
      simpa only [Geometry.sphereDiffeo_coe] using congrArg Subtype.val h
    rw [MulAut.conj_apply] at hE
    apply Subtype.ext
    have := congrArg (fun z => φ.symm z) hE
    simpa using this
  · intro h
    have hE : γ (φ.symm (x : W4)) = φ.symm (x : W4) := by
      simpa only [Geometry.sphereDiffeo_coe] using congrArg Subtype.val h
    apply Subtype.ext
    rw [MulAut.conj_apply]
    have := congrArg (fun z => φ z) hE
    simpa using this

theorem sphereDiffeo_conj_apply (φ γ : W4 ≃ₗᵢ[ℝ] W4) (x : S3) :
    Geometry.sphereDiffeo (n := 3) (MulAut.conj φ γ) (Geometry.sphereDiffeo (n := 3) φ x) =
      Geometry.sphereDiffeo (n := 3) φ (Geometry.sphereDiffeo (n := 3) γ x) := by
  apply Subtype.ext
  simp only [Geometry.sphereDiffeo_coe, MulAut.conj_apply]
  rw [show (φ * γ * φ⁻¹) (φ x) = φ (γ (φ⁻¹ (φ x))) by simp]
  simp

theorem sphereDiffeo_apply_symm (φ : W4 ≃ₗᵢ[ℝ] W4) (x : S3) :
    Geometry.sphereDiffeo (n := 3) φ (Geometry.sphereDiffeo (n := 3) φ.symm x) = x := by
  apply Subtype.ext
  simp only [Geometry.sphereDiffeo_coe]
  exact LinearIsometryEquiv.apply_symm_apply φ (x : W4)

theorem sphereDiffeo_symm_apply (φ : W4 ≃ₗᵢ[ℝ] W4) (x : S3) :
    Geometry.sphereDiffeo (n := 3) φ.symm (Geometry.sphereDiffeo (n := 3) φ x) = x := by
  apply Subtype.ext
  simp only [Geometry.sphereDiffeo_coe]
  exact LinearIsometryEquiv.symm_apply_apply φ (x : W4)

theorem conjSphericalSpaceFormGroupSubgroup_positive (G : SphericalSpaceFormGroup)
    (φ : W4 ≃ₗᵢ[ℝ] W4) (γ : ↥(conjSphericalSpaceFormGroupSubgroup G φ)) :
    (Geometry.sphereDiffeo (n := 3) γ.val).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)) := by
  obtain ⟨γ₀, hγ₀G, hγ₀⟩ := Subgroup.mem_map.mp γ.2
  rw [show γ.val = (MulAut.conj φ) γ₀ from hγ₀.symm]
  by_cases h1 : (⟨γ₀, hγ₀G⟩ : G.group) = 1
  · have hγ₀1 : γ₀ = 1 := congrArg Subtype.val h1
    rw [hγ₀1, map_one]
    refine Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _ ?_
    change LinearMap.det (1 : W4 →ₗ[ℝ] W4) = 1
    exact LinearMap.det_id
  · refine Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free _ (fun x hx => h1 ?_)
    exact G.free ⟨γ₀, hγ₀G⟩ _ ((sphereDiffeo_conj_apply_iff φ γ₀ x).mp hx)

theorem conjSphericalSpaceFormGroupSubgroup_free (G : SphericalSpaceFormGroup)
    (φ : W4 ≃ₗᵢ[ℝ] W4) (γ : ↥(conjSphericalSpaceFormGroupSubgroup G φ)) (x : S3)
    (hx : Geometry.sphereDiffeo (n := 3) γ.val x = x) : γ = 1 := by
  obtain ⟨γ₀, hγ₀G, hγ₀⟩ := Subgroup.mem_map.mp γ.2
  have hsub : (MulAut.conj φ) γ₀ = γ.val := hγ₀
  have hx' : Geometry.sphereDiffeo (n := 3) (MulAut.conj φ γ₀) x = x := by
    rw [hsub]; exact hx
  have h3 : (⟨γ₀, hγ₀G⟩ : G.group) = 1 :=
    G.free ⟨γ₀, hγ₀G⟩ _ ((sphereDiffeo_conj_apply_iff φ γ₀ x).mp hx')
  have hγ₀1 : γ₀ = 1 := by
    have := congrArg (fun y : ↥G.group => (y : W4 ≃ₗᵢ[ℝ] W4)) h3
    simpa using this
  refine Subtype.ext ?_
  rw [← hsub, hγ₀1, map_one]
  rfl

noncomputable def conjSphericalSpaceFormGroup (G : SphericalSpaceFormGroup)
    (φ : W4 ≃ₗᵢ[ℝ] W4) : SphericalSpaceFormGroup where
  group := conjSphericalSpaceFormGroupSubgroup G φ
  finite := conjSphericalSpaceFormGroupSubgroup_finite G φ
  positive := conjSphericalSpaceFormGroupSubgroup_positive G φ
  free := conjSphericalSpaceFormGroupSubgroup_free G φ

theorem orbitSetoid_iff_projection_eq (G : SphericalSpaceFormGroup) (a b : S3) :
    G.orbitSetoid a b ↔ G.projection a = G.projection b := by
  change G.orbitSetoid a b ↔
    Quotient.mk G.orbitSetoid a = Quotient.mk G.orbitSetoid b
  exact Quotient.eq.symm

theorem conjOrbit_projection_eq_iff (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4)
    (a b : S3) :
    G.projection a = G.projection b ↔
      (conjSphericalSpaceFormGroup G φ).projection (Geometry.sphereDiffeo (n := 3) φ a) =
        (conjSphericalSpaceFormGroup G φ).projection (Geometry.sphereDiffeo (n := 3) φ b) := by
  rw [SphericalSpaceFormGroup.projection_eq_iff, SphericalSpaceFormGroup.projection_eq_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨⟨(MulAut.conj φ) γ.val, ⟨γ.val, γ.2, rfl⟩⟩, ?_⟩
    change Geometry.sphereDiffeo (n := 3) (MulAut.conj φ γ.val)
      (Geometry.sphereDiffeo (n := 3) φ a) = Geometry.sphereDiffeo (n := 3) φ b
    rw [sphereDiffeo_conj_apply, hγ]
  · rintro ⟨η, hη⟩
    obtain ⟨γ₀, hγ₀G, hγ₀⟩ := Subgroup.mem_map.mp η.2
    have hη' : Geometry.sphereDiffeo (n := 3) (MulAut.conj φ γ₀)
        (Geometry.sphereDiffeo (n := 3) φ a) = Geometry.sphereDiffeo (n := 3) φ b := by
      rw [show (MulAut.conj φ) γ₀ = η.val from hγ₀]
      exact hη
    rw [sphereDiffeo_conj_apply] at hη'
    exact ⟨⟨γ₀, hγ₀G⟩, (Geometry.sphereDiffeo (n := 3) φ).injective hη'⟩

theorem conjOrbitSetoid_iff (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4) (a b : S3) :
    G.orbitSetoid a b ↔ (conjSphericalSpaceFormGroup G φ).orbitSetoid
      (Geometry.sphereDiffeo (n := 3) φ a) (Geometry.sphereDiffeo (n := 3) φ b) :=
  (orbitSetoid_iff_projection_eq G a b).trans
    ((conjOrbit_projection_eq_iff G φ a b).trans
      (orbitSetoid_iff_projection_eq (conjSphericalSpaceFormGroup G φ) _ _).symm)

noncomputable def conjOrbitEquiv (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4) :
    G.Orbit ≃ (conjSphericalSpaceFormGroup G φ).Orbit :=
  Quotient.congr (Geometry.sphereDiffeo (n := 3) φ).toEquiv (conjOrbitSetoid_iff G φ)

theorem conjOrbitEquiv_projection (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4)
    (x : S3) :
    conjOrbitEquiv G φ (G.projection x) =
      (conjSphericalSpaceFormGroup G φ).projection (Geometry.sphereDiffeo (n := 3) φ x) := by
  change Quotient.congr (Geometry.sphereDiffeo (n := 3) φ).toEquiv (conjOrbitSetoid_iff G φ)
    (Quotient.mk G.orbitSetoid x) =
    Quotient.mk (conjSphericalSpaceFormGroup G φ).orbitSetoid
      (Geometry.sphereDiffeo (n := 3) φ x)
  exact Quotient.congr_mk _ _ x

theorem conjOrbitEquiv_symm_projection (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4)
    (y : S3) :
    (conjOrbitEquiv G φ).symm ((conjSphericalSpaceFormGroup G φ).projection y) =
      G.projection (Geometry.sphereDiffeo (n := 3) φ.symm y) := by
  have h := conjOrbitEquiv_projection G φ (Geometry.sphereDiffeo (n := 3) φ.symm y)
  rw [sphereDiffeo_apply_symm] at h
  rw [← h, Equiv.symm_apply_apply]

theorem conjOrbitEquiv_contMDiff (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (conjOrbitEquiv G φ) := by
  refine IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    G.projection_isLocalDiffeomorph G.projection_surjective ?_
  rw [show ⇑(conjOrbitEquiv G φ) ∘ G.projection =
      (conjSphericalSpaceFormGroup G φ).projection ∘
        (Geometry.sphereDiffeo (n := 3) φ) from
    funext (fun x => conjOrbitEquiv_projection G φ x)]
  exact ((conjSphericalSpaceFormGroup G φ).projection_isLocalDiffeomorph.contMDiff).comp
    (Geometry.sphereDiffeo (n := 3) φ).contMDiff

theorem conjOrbitEquiv_symm_contMDiff (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (conjOrbitEquiv G φ).symm := by
  refine IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    (conjSphericalSpaceFormGroup G φ).projection_isLocalDiffeomorph
    (conjSphericalSpaceFormGroup G φ).projection_surjective ?_
  rw [show ⇑(conjOrbitEquiv G φ).symm ∘ (conjSphericalSpaceFormGroup G φ).projection =
      G.projection ∘ (Geometry.sphereDiffeo (n := 3) φ.symm) from
    funext (fun y => conjOrbitEquiv_symm_projection G φ y)]
  exact (G.projection_isLocalDiffeomorph.contMDiff).comp
    (Geometry.sphereDiffeo (n := 3) φ.symm).contMDiff

noncomputable def conjOrbitDiffeomorph (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4) :
    Diffeomorph (𝓡 3) (𝓡 3) G.Orbit (conjSphericalSpaceFormGroup G φ).Orbit ∞ where
  toEquiv := conjOrbitEquiv G φ
  contMDiff_toFun := conjOrbitEquiv_contMDiff G φ
  contMDiff_invFun := conjOrbitEquiv_symm_contMDiff G φ

theorem sphereDiffeo_eq_sphereLinearIsometryDiffeomorph (φ : W4 ≃ₗᵢ[ℝ] W4) :
    Geometry.sphereDiffeo (n := 3) φ = sphereLinearIsometryDiffeomorph φ := by
  apply Diffeomorph.ext
  intro x
  apply Subtype.ext
  rfl

theorem conjOrbitDiffeomorph_preservesOrientation_opposite
    (G : SphericalSpaceFormGroup) (φ : W4 ≃ₗᵢ[ℝ] W4)
    (hφ : (Geometry.sphereDiffeo (n := 3) φ).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)).opposite) :
    (conjOrbitDiffeomorph G φ).preservesOrientation
      G.manifold.orientation.opposite
      (conjSphericalSpaceFormGroup G φ).manifold.orientation := by
  let oM : ManifoldOrientation (𝓡 3) G.Orbit 3 := G.manifold.orientation
  let oN : ManifoldOrientation (𝓡 3) (conjSphericalSpaceFormGroup G φ).Orbit 3 :=
    (conjSphericalSpaceFormGroup G φ).manifold.orientation
  change (conjOrbitDiffeomorph G φ).preservesOrientation oM.opposite oN
  intro q
  obtain ⟨x, rfl⟩ := G.projection_surjective q
  let L : TangentSpace (𝓡 3) (G.projection x) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) ((conjOrbitDiffeomorph G φ) (G.projection x)) :=
    ((conjOrbitDiffeomorph G φ).mfderivToContinuousLinearEquiv (by simp)
      (G.projection x)).toLinearEquiv
  let Lπ : TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (G.projection x) :=
    (G.projection_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let Ls : TangentSpace (𝓡 3) x ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (Geometry.sphereDiffeo (n := 3) φ x) :=
    ((Geometry.sphereDiffeo (n := 3) φ).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let Lπ' : TangentSpace (𝓡 3) (Geometry.sphereDiffeo (n := 3) φ x) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) ((conjOrbitDiffeomorph G φ) (G.projection x)) :=
    ((conjSphericalSpaceFormGroup G φ).projection_isLocalDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (Geometry.sphereDiffeo (n := 3) φ x)).toLinearEquiv
  have hL : ⇑L = ⇑(mfderiv (𝓡 3) (𝓡 3)
      ((conjOrbitDiffeomorph G φ) : G.Orbit → (conjSphericalSpaceFormGroup G φ).Orbit)
      (G.projection x)) := by
    change ⇑(((conjOrbitDiffeomorph G φ).mfderivToContinuousLinearEquiv (by simp)
      (G.projection x)).toLinearEquiv) = _
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hLπ : ⇑Lπ = ⇑(mfderiv (𝓡 3) (𝓡 3) (G.projection : S3 → G.Orbit) x) := by
    change ⇑((G.projection_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp)
      x).toLinearEquiv) = _
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hLs : ⇑Ls = ⇑(mfderiv (𝓡 3) (𝓡 3)
      ((Geometry.sphereDiffeo (n := 3) φ) : S3 → S3) x) := by
    change ⇑(((Geometry.sphereDiffeo (n := 3) φ).mfderivToContinuousLinearEquiv (by simp)
      x).toLinearEquiv) = _
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hπ'loc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (conjSphericalSpaceFormGroup G φ).projection :=
    (conjSphericalSpaceFormGroup G φ).projection_isLocalDiffeomorph
  have hLπ' : ⇑Lπ' = ⇑(mfderiv (𝓡 3) (𝓡 3)
      ((conjSphericalSpaceFormGroup G φ).projection :
        S3 → (conjSphericalSpaceFormGroup G φ).Orbit)
      (Geometry.sphereDiffeo (n := 3) φ x)) := by
    change ⇑((hπ'loc.mfderivToContinuousLinearEquiv (by simp)
      (Geometry.sphereDiffeo (n := 3) φ x)).toLinearEquiv) = _
    rw [ContinuousLinearEquiv.coe_toLinearEquiv]
    rfl
  have hπ_md : MDifferentiableAt (𝓡 3) (𝓡 3) (G.projection : S3 → G.Orbit) x :=
    G.projection_isLocalDiffeomorph.mdifferentiable (by simp) x
  have hf_md : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((conjOrbitDiffeomorph G φ) : G.Orbit → (conjSphericalSpaceFormGroup G φ).Orbit)
      (G.projection x) :=
    (conjOrbitDiffeomorph G φ).mdifferentiable (by simp) (G.projection x)
  have hLs_md : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((Geometry.sphereDiffeo (n := 3) φ) : S3 → S3) x :=
    (Geometry.sphereDiffeo (n := 3) φ).mdifferentiable (by simp) x
  have hπ'_md : MDifferentiableAt (𝓡 3) (𝓡 3)
      ((conjSphericalSpaceFormGroup G φ).projection :
        S3 → (conjSphericalSpaceFormGroup G φ).Orbit)
      (Geometry.sphereDiffeo (n := 3) φ x) :=
    hπ'loc.mdifferentiable (by simp) _
  have hcomp :
      ((conjOrbitDiffeomorph G φ) : G.Orbit → (conjSphericalSpaceFormGroup G φ).Orbit) ∘
        (G.projection : S3 → G.Orbit) =
      ((conjSphericalSpaceFormGroup G φ).projection :
          S3 → (conjSphericalSpaceFormGroup G φ).Orbit) ∘
        ((Geometry.sphereDiffeo (n := 3) φ) : S3 → S3) :=
    funext (fun y => conjOrbitEquiv_projection G φ y)
  have hlin : Lπ.trans L = Ls.trans Lπ' := by
    apply LinearEquiv.ext
    intro v
    change ⇑L (⇑Lπ v) = ⇑Lπ' (⇑Ls v)
    rw [hL, hLπ, hLs, hLπ']
    rw [← mfderiv_comp_apply (x := x) (f := (G.projection : S3 → G.Orbit))
      (g := ((conjOrbitDiffeomorph G φ) : G.Orbit → (conjSphericalSpaceFormGroup G φ).Orbit))
      hf_md hπ_md v]
    rw [hcomp]
    exact mfderiv_comp_apply (x := x) (f := ((Geometry.sphereDiffeo (n := 3) φ) : S3 → S3))
      (g := ((conjSphericalSpaceFormGroup G φ).projection :
        S3 → (conjSphericalSpaceFormGroup G φ).Orbit)) hπ'_md hLs_md v
  have hpos : Orientation.map (Fin 3) Lπ ((sphereOrientation 3 (by decide)).orientation x)
      = oM.orientation (G.projection x) :=
    G.projection_positive x
  have hpos' : Orientation.map (Fin 3) Lπ'
      ((sphereOrientation 3 (by decide)).orientation (Geometry.sphereDiffeo (n := 3) φ x))
      = oN.orientation ((conjOrbitDiffeomorph G φ) (G.projection x)) :=
    (conjSphericalSpaceFormGroup G φ).projection_positive (Geometry.sphereDiffeo (n := 3) φ x)
  have hφx : Orientation.map (Fin 3) Ls ((sphereOrientation 3 (by decide)).orientation x)
      = - (sphereOrientation 3 (by decide)).orientation
          (Geometry.sphereDiffeo (n := 3) φ x) :=
    hφ x
  rw [ManifoldOrientation.opposite_orientation, Orientation.map_neg, ← hpos]
  rw [← orientation_map_trans Lπ L ((sphereOrientation 3 (by decide)).orientation x)]
  rw [hlin]
  rw [orientation_map_trans Ls Lπ' ((sphereOrientation 3 (by decide)).orientation x)]
  rw [hφx, Orientation.map_neg]
  exact (neg_neg _).trans hpos'

theorem sphericalSpaceFormOrientationClosure_holds : sphericalSpaceFormOrientationClosure := by
  intro G
  let v : W4 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis 0
  have hv : v ≠ 0 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.ne_zero 0
  have hφ : (Geometry.sphereDiffeo (n := 3) ((ℝ ∙ v)ᗮ.reflection)).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)).opposite := by
    rw [sphereDiffeo_eq_sphereLinearIsometryDiffeomorph]
    exact sphereReflectionDiffeomorph_preservesOrientation_opposite v hv
  exact ⟨conjSphericalSpaceFormGroup G ((ℝ ∙ v)ᗮ.reflection),
    ⟨conjOrbitDiffeomorph G ((ℝ ∙ v)ᗮ.reflection),
      conjOrbitDiffeomorph_preservesOrientation_opposite G ((ℝ ∙ v)ᗮ.reflection) hφ⟩⟩

theorem factorOrientationClosure_holds : factorOrientationClosure.{u} :=
  factorOrientationClosure_of_sphericalSpaceFormOrientationClosure
    sphericalSpaceFormOrientationClosure_holds

theorem poincareStandardOrientationRefinement_holds : poincareStandardOrientationRefinement.{u} :=
  poincareStandardOrientationRefinement_of_factorOrientationClosure factorOrientationClosure_holds

theorem poincareStandardSumClosed_holds : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_factorOrientationClosure factorOrientationClosure_holds

end DifferentialGeometry.Topology
