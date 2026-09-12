import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm
import DifferentialGeometry.Geometry.Curvature.Metric.Conditions

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.Geometry

universe u

private instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

private abbrev RoundSphereE4 := EuclideanSpace ℝ (Fin 4)
private abbrev RoundSphereS3 := sphere (0 : RoundSphereE4) 1

private theorem sphereOutwardDeterminant_eq_basisFunDet
    (y : RoundSphereS3) (c : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) y)) :
    sphereOutwardDeterminant 3 y c =
      ((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).det
        (fun j => Fin.cases (motive := fun _ => RoundSphereE4) (y : RoundSphereE4)
          (fun k => dIncl (n := 3) y (c k)) j) := by
  rw [Module.Basis.det_apply]
  rfl

theorem sphereOutwardDeterminant_sphereDiffeo
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4) (x : RoundSphereS3)
    (b : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) :
    sphereOutwardDeterminant 3 (sphereDiffeo (n := 3) e x)
        (b.map (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv)) =
      LinearMap.det (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4)
        * sphereOutwardDeterminant 3 x b := by
  have hv : (fun j => Fin.cases (motive := fun _ => RoundSphereE4)
        ((sphereDiffeo (n := 3) e x : RoundSphereS3) : RoundSphereE4)
        (fun k => dIncl (n := 3) (sphereDiffeo (n := 3) e x)
          ((b.map (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv
            (by simp) x).toLinearEquiv)) k)) j) =
      (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) ∘
        (fun j => Fin.cases (motive := fun _ => RoundSphereE4) (x : RoundSphereE4)
          (fun k => dIncl (n := 3) x (b k)) j) := by
    funext j
    induction j using Fin.cases with
    | zero =>
      simp only [Function.comp_apply, Fin.cases_zero, sphereDiffeo_coe]
      rfl
    | succ k =>
      simp only [Function.comp_apply, Fin.cases_succ, Module.Basis.map_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
      exact mfderiv_incl_sphereDiffeo (n := 3) e x (b k)
  rw [sphereOutwardDeterminant_eq_basisFunDet (sphereDiffeo (n := 3) e x) _,
    sphereOutwardDeterminant_eq_basisFunDet x b, hv, Module.Basis.det_comp]

namespace Geometry

theorem sphereDiffeo_preservesOrientation_of_det_eq_one
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4)
    (hdet : LinearMap.det (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) = 1) :
    (sphereDiffeo (n := 3) e).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)) := by
  intro x
  let L : TangentSpace (𝓡 3) x ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (sphereDiffeo (n := 3) e x) :=
    (((sphereDiffeo (n := 3) e).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv)
  let b : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hkey : b.orientation = (sphereOrientation 3 (by decide)).orientation x ↔
      (b.map L).orientation =
        (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x) := by
    rw [sphereOrientation_characterization 3 (by decide) x b,
      sphereOrientation_characterization 3 (by decide) _ (b.map L),
      sphereOutwardDeterminant_sphereDiffeo, hdet, one_mul]
  rcases b.orientation_eq_or_eq_neg
    ((sphereOrientation 3 (by decide)).orientation x) with hb | hb
  · have hmap : (b.map L).orientation =
        (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x) :=
      hkey.mp hb.symm
    change Orientation.map (Fin 3) L ((sphereOrientation 3 (by decide)).orientation x) =
      (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)
    rw [hb, ← Module.Basis.orientation_map b L]
    exact hmap
  · have hne : b.orientation ≠ (sphereOrientation 3 (by decide)).orientation x := by
      intro h
      exact Module.Ray.ne_neg_self b.orientation (h.trans hb)
    change Orientation.map (Fin 3) L ((sphereOrientation 3 (by decide)).orientation x) =
      (sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)
    rw [hb, Orientation.map_neg, ← Module.Basis.orientation_map b L]
    rcases Module.Basis.orientation_eq_or_eq_neg (b.map L)
      ((sphereOrientation 3 (by decide)).orientation (sphereDiffeo (n := 3) e x)) with
      hcon | hcon
    · exact absurd (hkey.mpr hcon.symm) hne
    · exact hcon.symm

theorem linearIsometryEquiv_det_eq_one_of_fixed_point_free
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4)
    (hfree : ∀ x : RoundSphereS3, sphereDiffeo (n := 3) e x ≠ x) :
    LinearMap.det (e.toLinearEquiv : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) = 1 := by
  classical
  let b := stdOrthonormalBasis ℝ RoundSphereE4
  let f : Module.End ℝ RoundSphereE4 := e.toLinearEquiv.toLinearMap
  let A : Matrix (Fin (finrank ℝ RoundSphereE4)) (Fin (finrank ℝ RoundSphereE4)) ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis f
  have horth : A ∈ Matrix.orthogonalGroup (Fin (finrank ℝ RoundSphereE4)) ℝ :=
    e.toMatrix_mem_unitaryGroup b b
  have hAtA : A.transpose * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin (finrank ℝ RoundSphereE4)) ℝ).mp horth
  have hcard : Fintype.card (Fin (finrank ℝ RoundSphereE4)) = 4 := by
    simp [RoundSphereE4]
  have hdet : A.det = 1 ∨ A.det = -1 := by
    rw [← sq_eq_one_iff]
    simpa [unitary, sq] using! Matrix.det_of_mem_unitary horth
  have hne : A.det ≠ -1 := by
    intro hdetneg
    have hdet_sub : (A - 1).det = 0 := by
      have hident : (A - 1).transpose * A = -(A - 1) := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul, hAtA]
        ext i j
        simp
      have hneg : (-(A - 1)).det = (A - 1).det := by
        rw [Matrix.det_neg]
        have hpow : ((-1 : ℝ) ^ Fintype.card (Fin (finrank ℝ RoundSphereE4))) = 1 := by
          rw [hcard]
          norm_num
        rw [hpow, one_mul]
      have h := congrArg Matrix.det hident
      rw [Matrix.det_mul, hneg, Matrix.det_transpose, hdetneg] at h
      linarith
    have hfdet : LinearMap.det (f - 1) = 0 := by
      rw [← LinearMap.det_toMatrix b.toBasis]
      simpa only [A, map_sub, LinearMap.toMatrix_one] using hdet_sub
    obtain ⟨v, hv, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hfdet)
    have hv' : f v - v = 0 := hv
    have hev : e v = v := by
      change e.toLinearEquiv v - v = 0 at hv'
      exact sub_eq_zero.mp hv'
    let x : RoundSphereS3 :=
      ⟨‖v‖⁻¹ • v, by
        rw [mem_sphere_zero_iff_norm, norm_smul]
        simp [hv_ne]⟩
    apply hfree x
    apply Subtype.ext
    change e (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    rw [map_smul, hev]
  have hA1 : A.det = 1 := by
    rcases hdet with h | h
    · exact h
    · exact absurd h hne
  have : LinearMap.det f = A.det := by simp only [A, LinearMap.det_toMatrix]
  change LinearMap.det f = 1
  rw [this, hA1]

theorem sphereDiffeo_preservesOrientation_of_fixed_point_free
    (e : RoundSphereE4 ≃ₗᵢ[ℝ] RoundSphereE4)
    (hfree : ∀ x : RoundSphereS3, sphereDiffeo (n := 3) e x ≠ x) :
    (sphereDiffeo (n := 3) e).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)) :=
  sphereDiffeo_preservesOrientation_of_det_eq_one e
    (linearIsometryEquiv_det_eq_one_of_fixed_point_free e hfree)

theorem roundSphereQuotient_subgroup_finite
    (D : RoundSphereQuotient (RoundSphereE4) 3) :
    Finite ↥(D.ρ.range) :=
  Finite.of_surjective (fun γ : D.Γ => (⟨D.ρ γ, ⟨γ, rfl⟩⟩ : ↥(D.ρ.range)))
    (fun g => by
      obtain ⟨γ, hγ⟩ := g.2
      exact ⟨γ, Subtype.ext hγ⟩)

noncomputable def sphericalSpaceFormGroupOfRoundSphereQuotient
    (D : RoundSphereQuotient (RoundSphereE4) 3) :
    Topology.SphericalSpaceFormGroup where
  group := D.ρ.range
  finite := roundSphereQuotient_subgroup_finite D
  positive := by
    intro γ
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    rw [← hγ₀]
    by_cases h1 : γ₀ = 1
    · subst h1
      rw [map_one]
      exact sphereDiffeo_preservesOrientation_of_det_eq_one _ (by
        change LinearMap.det (1 : RoundSphereE4 →ₗ[ℝ] RoundSphereE4) = 1
        exact LinearMap.det_id)
    · exact sphereDiffeo_preservesOrientation_of_fixed_point_free _
        (fun x hx => h1 (D.action_free γ₀ x hx))
  free := by
    intro γ x hγx
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    have hx : sphereDiffeo (n := 3) (D.ρ γ₀) x = x := by
      rw [hγ₀]
      exact hγx
    have h1 : γ₀ = 1 := D.action_free γ₀ x hx
    exact Subtype.ext (by rw [← hγ₀, h1, map_one]; rfl)

variable (D : RoundSphereQuotient (RoundSphereE4) 3)

theorem orbitMk_eq_iff (x y : RoundSphereS3) :
    (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection x =
        (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection y ↔
      ∃ γ : D.Γ, sphereDiffeo (n := 3) (D.ρ γ) x = y := by
  rw [Topology.SphericalSpaceFormGroup.projection_eq_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    exact ⟨γ₀, by rw [← hγ₀] at hγ; exact hγ⟩
  · rintro ⟨γ₀, hγ₀⟩
    exact ⟨⟨D.ρ γ₀, ⟨γ₀, rfl⟩⟩, hγ₀⟩

noncomputable def orbitToQuotient :
    (sphericalSpaceFormGroupOfRoundSphereQuotient D).Orbit → D.Q :=
  Quotient.lift D.proj (fun a b hab => by
    obtain ⟨γ₀, hγ₀⟩ := (orbitMk_eq_iff D a b).mp (Quotient.sound hab)
    rw [← hγ₀]
    exact (D.proj_smul γ₀ a).symm)

theorem orbitToQuotient_projection (x : RoundSphereS3) :
    orbitToQuotient D
      ((sphericalSpaceFormGroupOfRoundSphereQuotient D).projection x) = D.proj x :=
  rfl

theorem orbitToQuotient_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (orbitToQuotient D) :=
  IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    (Topology.SphericalSpaceFormGroup.projection_isLocalDiffeomorph
      (sphericalSpaceFormGroupOfRoundSphereQuotient D))
    (Topology.SphericalSpaceFormGroup.projection_surjective
      (sphericalSpaceFormGroupOfRoundSphereQuotient D))
    (by
      have h : (orbitToQuotient D) ∘
          (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection = D.proj := by
        funext x
        exact orbitToQuotient_projection D x
      rw [h]
      exact D.proj_smooth)

theorem orbitToQuotient_surjective : Function.Surjective (orbitToQuotient D) := by
  intro q
  obtain ⟨x, hx⟩ := D.proj_surjective q
  exact ⟨(sphericalSpaceFormGroupOfRoundSphereQuotient D).projection x,
    by rw [orbitToQuotient_projection, hx]⟩

theorem orbitToQuotient_injective : Function.Injective (orbitToQuotient D) := by
  intro a b hab
  obtain ⟨x, rfl⟩ :=
    (Topology.SphericalSpaceFormGroup.projection_surjective
      (sphericalSpaceFormGroupOfRoundSphereQuotient D)) a
  obtain ⟨y, rfl⟩ :=
    (Topology.SphericalSpaceFormGroup.projection_surjective
      (sphericalSpaceFormGroupOfRoundSphereQuotient D)) b
  rw [orbitToQuotient_projection, orbitToQuotient_projection] at hab
  obtain ⟨γ₀, hγ₀⟩ := D.proj_eq_imp x y hab
  exact (orbitMk_eq_iff D x y).mpr ⟨γ₀, hγ₀⟩

theorem orbitToQuotient_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (orbitToQuotient D) := by
  classical
  intro q
  obtain ⟨x, rfl⟩ :=
    (Topology.SphericalSpaceFormGroup.projection_surjective
      (sphericalSpaceFormGroupOfRoundSphereQuotient D)) q
  let S := D.sectionAt (D.proj x)
  let ψ : D.Q → (sphericalSpaceFormGroupOfRoundSphereQuotient D).Orbit := fun r =>
    if hr : r ∈ S.baseNeighborhood then
      (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection
        (S.toSphere ⟨r, hr⟩ : RoundSphereS3)
    else
      (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection x
  have hψsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun r : S.baseNeighborhood =>
        (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection
          (S.toSphere r : RoundSphereS3)) :=
    ((Topology.SphericalSpaceFormGroup.projection_isLocalDiffeomorph
        (sphericalSpaceFormGroupOfRoundSphereQuotient D)).contMDiff).comp
      S.toSphere_contMDiff
  have hψtarget : ∀ r ∈ (S.baseNeighborhood : Set D.Q),
      orbitToQuotient D (ψ r) = r := by
    intro r hr
    dsimp only [ψ]
    split_ifs with h
    · exact (orbitToQuotient_projection D _).trans (S.toSphere_proj _)
    · exact absurd hr h
  refine ⟨{
    toFun := orbitToQuotient D
    invFun := ψ
    source := (orbitToQuotient D) ⁻¹' (S.baseNeighborhood : Set D.Q)
    target := (S.baseNeighborhood : Set D.Q)
    map_source' := fun y hy => hy
    map_target' := fun r hr => by
      change orbitToQuotient D (ψ r) ∈ (S.baseNeighborhood : Set D.Q)
      rw [hψtarget r hr]
      exact hr
    left_inv' := fun y hy => orbitToQuotient_injective D (hψtarget _ hy)
    right_inv' := fun r hr => hψtarget r hr
    open_source := S.baseNeighborhood.isOpen.preimage
      (orbitToQuotient_contMDiff D).continuous
    open_target := S.baseNeighborhood.isOpen
    contMDiffOn_toFun := (orbitToQuotient_contMDiff D).contMDiffOn
    contMDiffOn_invFun := by
      intro r hr
      apply ContMDiffAt.contMDiffWithinAt
      rw [← contMDiffAt_subtype_iff (U := S.baseNeighborhood) (x := ⟨r, hr⟩)]
      refine hψsmooth.contMDiffAt.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
      funext z
      dsimp only [ψ]
      split_ifs with h
      · exact congrArg (fun z : S.baseNeighborhood =>
          (sphericalSpaceFormGroupOfRoundSphereQuotient D).projection
            (S.toSphere z : RoundSphereS3)) (Subtype.ext rfl)
      · exact absurd z.2 h }, ?_, ?_⟩
  · change orbitToQuotient D
      ((sphericalSpaceFormGroupOfRoundSphereQuotient D).projection x) ∈
        (S.baseNeighborhood : Set D.Q)
    rw [orbitToQuotient_projection]
    exact S.mem_baseNeighborhood
  · intro y hy
    rfl

theorem orbitToQuotient_bijective : Function.Bijective (orbitToQuotient D) :=
  ⟨orbitToQuotient_injective D, orbitToQuotient_surjective D⟩

noncomputable def sphericalSpaceFormOrbitDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3)
      (sphericalSpaceFormGroupOfRoundSphereQuotient D).Orbit D.Q ∞ :=
  (orbitToQuotient_isLocalDiffeomorph D).diffeomorphOfBijective
    (orbitToQuotient_bijective D)

theorem sphericalSpaceFormOrbitDiffeomorph_apply
    (x : (sphericalSpaceFormGroupOfRoundSphereQuotient D).Orbit) :
    sphericalSpaceFormOrbitDiffeomorph D x = orbitToQuotient D x :=
  rfl

theorem exists_diffeomorph_sphericalSpaceFormOrbit_of_roundSphereQuotient
    {M : Topology.ClosedOrientedManifold.{u} 3}
    (e : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ D.Q) :
    ∃ G : Topology.SphericalSpaceFormGroup,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M.Carrier G.Orbit ∞) :=
  ⟨sphericalSpaceFormGroupOfRoundSphereQuotient D,
    ⟨e.trans (sphericalSpaceFormOrbitDiffeomorph D).symm⟩⟩

end Geometry

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def sectionalCurvatureMetricBridge : Prop :=
  ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric ThreeModel M.Carrier),
    IsConstantPositiveSectionalCurvature g →
      DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric
        (I := ThreeModel) (M := M.Carrier) g

def roundSphereQuotientOrientedCovering : Prop :=
  ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (D : DifferentialGeometry.Geometry.RoundSphereQuotient.{0, u}
      (EuclideanSpace ℝ (Fin 4)) 3),
    Nonempty (M.Carrier ≃ₘ⟮ThreeModel, 𝓡 3⟯ D.Q) →
    ∃ G : DifferentialGeometry.Topology.SphericalSpaceFormGroup,
      Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold)

def sphericalSpaceFormCoveringGeneralized : Prop :=
  ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric ThreeModel M.Carrier),
    IsConstantPositiveSectionalCurvature g →
    ∃ G : DifferentialGeometry.Topology.SphericalSpaceFormGroup,
      Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold)

theorem sphericalSpaceFormCoveringGeneralized_of_inputs
    (hbridge : sectionalCurvatureMetricBridge.{u})
    (horient : roundSphereQuotientOrientedCovering.{u}) :
    sphericalSpaceFormCoveringGeneralized.{u} := by
  intro M g hg
  have hclosed : DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold
      (I := ThreeModel) (M := M.Carrier) :=
    ⟨inferInstance, inferInstance, inferInstance, by rw [finrank_euclideanSpace_fin]⟩
  have hconst : DifferentialGeometry.Geometry.Curvature.admitsConstantPositiveSectionalCurvature
      (I := ThreeModel) (M := M.Carrier) :=
    ⟨g, hbridge M g hg⟩
  obtain ⟨S⟩ :=
    DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form
      (I := ThreeModel) (M := M.Carrier) hclosed hconst
  exact horient M S.quotient ⟨S.equiv⟩

theorem sphericalSpaceFormCovering_of_inputs
    (hbridge : sectionalCurvatureMetricBridge.{u})
    (horient : roundSphereQuotientOrientedCovering.{u}) :
    sphericalSpaceFormCovering.{u} :=
  sphericalSpaceFormCoveringGeneralized_of_inputs hbridge horient

theorem sphericalSpaceFormCovering_iff_generalized :
    sphericalSpaceFormCovering.{u} ↔ sphericalSpaceFormCoveringGeneralized.{u} :=
  Iff.rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
