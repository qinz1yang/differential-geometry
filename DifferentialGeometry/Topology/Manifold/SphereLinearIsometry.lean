import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere
import DifferentialGeometry.Topology.Manifold.ULift
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section

universe u

open Manifold Metric Module Set
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.Topology

private abbrev W4 := EuclideanSpace ℝ (Fin 4)
private abbrev T3 := Metric.sphere (0 : W4) 1

private local instance instSphereFact : Fact (Module.finrank ℝ W4 = 3 + 1) := ⟨by simp⟩

noncomputable def sphereLinearIsometryDiffeomorph (A : W4 ≃ₗᵢ[ℝ] W4) :
    T3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ T3 where
  toFun x := ⟨A x, by
    have hx : ‖(x : W4)‖ = 1 := by
      rw [← dist_zero_right (x : W4)]
      exact Metric.mem_sphere.mp x.2
    rw [Metric.mem_sphere, dist_zero_right, A.norm_map, hx]⟩
  invFun y := ⟨A.symm y, by
    have hy : ‖(y : W4)‖ = 1 := by
      rw [← dist_zero_right (y : W4)]
      exact Metric.mem_sphere.mp y.2
    rw [Metric.mem_sphere, dist_zero_right, A.symm.norm_map, hy]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  contMDiff_toFun := by
    apply ContMDiff.codRestrict_sphere
    exact (A.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).comp contMDiff_coe_sphere
  contMDiff_invFun := by
    apply ContMDiff.codRestrict_sphere
    exact (A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).comp contMDiff_coe_sphere

theorem mfderiv_coe_sphereLinearIsometryDiffeomorph (A : W4 ≃ₗᵢ[ℝ] W4) (x : T3)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) 𝓘(ℝ, W4) (Subtype.val : T3 → W4)
        (sphereLinearIsometryDiffeomorph A x)
        (mfderiv (𝓡 3) (𝓡 3) (sphereLinearIsometryDiffeomorph A) x v) =
      (A.toContinuousLinearEquiv.toContinuousLinearMap : W4 → W4)
        (mfderiv (𝓡 3) 𝓘(ℝ, W4) (Subtype.val : T3 → W4) x v) := by
  set f := sphereLinearIsometryDiffeomorph A with hf
  have hc := mfderiv_comp_apply (x := x)
    ((contMDiff_coe_sphere (n := 3) (m := ∞)).mdifferentiableAt (by simp))
    (f.contMDiff.mdifferentiableAt (by simp)) v
  have hfun : (Subtype.val : T3 → W4) ∘ f =
      (A.toContinuousLinearEquiv.toContinuousLinearMap : W4 →L[ℝ] W4) ∘ (Subtype.val : T3 → W4) := by
    funext y
    rfl
  rw [hfun] at hc
  have h2 := mfderiv_comp_apply (x := x)
    ((A.toContinuousLinearEquiv.toContinuousLinearMap).mdifferentiableAt)
    ((contMDiff_coe_sphere (n := 3) (m := ∞)).mdifferentiableAt (by simp)) v
  rw [ContinuousLinearMap.mfderiv_eq] at h2
  rw [h2] at hc
  exact hc.symm

theorem sphereOutwardDeterminant_sphereLinearIsometryDiffeomorph
    (A : W4 ≃ₗᵢ[ℝ] W4) (x : T3) (b : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) :
    sphereOutwardDeterminant 3 (sphereLinearIsometryDiffeomorph A x)
        (b.map ((sphereLinearIsometryDiffeomorph A).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv) =
      LinearMap.det (A.toContinuousLinearEquiv.toContinuousLinearMap : W4 →ₗ[ℝ] W4) *
        sphereOutwardDeterminant 3 x b := by
  classical
  set f := sphereLinearIsometryDiffeomorph A with hf
  let B : Basis (Fin 4) ℝ W4 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  let D : TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (f x) :=
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let c : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (f x)) := b.map D
  have hc : ∀ k, c k = mfderiv (𝓡 3) (𝓡 3) f x (b k) := by
    intro k
    have hck : c k = D (b k) := Basis.map_apply b D k
    rw [hck]
    exact congrArg (fun (L : TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) (f x)) => L (b k))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe f (by simp))
  let xframe : Fin 4 → W4 := fun j => Fin.cases (x : W4)
    (fun k => NormedSpace.fromTangentSpace (x : W4)
      (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : T3 → W4) x (b k))) j
  let rframe : Fin 4 → W4 := fun j => Fin.cases ((f x : T3) : W4)
    (fun k => NormedSpace.fromTangentSpace ((f x : T3) : W4)
      (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : T3 → W4) (f x) (c k))) j
  have hxdet : sphereOutwardDeterminant 3 x b = B.det xframe := by
    rw [Module.Basis.det_apply]
    rfl
  have hrdet : sphereOutwardDeterminant 3 (f x) c = B.det rframe := by
    rw [Module.Basis.det_apply]
    rfl
  have hframe : (A.toContinuousLinearEquiv.toContinuousLinearMap : W4 →ₗ[ℝ] W4) ∘ xframe = rframe := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Function.comp_apply, xframe, rframe, Fin.cases_zero]
      rfl
    · intro k
      simp only [Function.comp_apply, xframe, rframe, Fin.cases_succ]
      rw [hc k, mfderiv_coe_sphereLinearIsometryDiffeomorph A x (b k)]
      rfl
  rw [hxdet, hrdet, ← Module.Basis.det_comp B
    (A.toContinuousLinearEquiv.toContinuousLinearMap : W4 →ₗ[ℝ] W4) xframe, hframe]

theorem sphereReflectionDiffeomorph_preservesOrientation_opposite (v : W4) (hv : v ≠ 0) :
    (sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection)).preservesOrientation
      (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide)).opposite := by
  intro x
  set o : ManifoldOrientation (𝓡 3) T3 3 := sphereOrientation 3 (by decide) with ho
  have hfin : Module.Finite ℝ (TangentSpace (𝓡 3) x) := by
    change Module.Finite ℝ (EuclideanSpace ℝ (Fin 3))
    infer_instance
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace (𝓡 3) x) := by
    change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp
  let b : Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x) := Orientation.someBasis (o.orientation x) hcard
  have hb : b.orientation = o.orientation x := Orientation.someBasis_orientation _ _
  let D := ((sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection)).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv
  let c := b.map D
  have hpos : 0 < sphereOutwardDeterminant 3 x b :=
    (sphereOrientation_characterization 3 (by decide) x b).mp hb
  have hdet : LinearMap.det
      ((((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap :
        W4 →L[ℝ] W4) : W4 →ₗ[ℝ] W4) = -1 := by
    have h := Submodule.det_reflection (𝕜 := ℝ) (K := (ℝ ∙ v)ᗮ)
    have hcoe : ((((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap :
        W4 →L[ℝ] W4) : W4 →ₗ[ℝ] W4) = ((ℝ ∙ v)ᗮ.reflection).toLinearMap := rfl
    rw [hcoe]
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hv] at h
    simpa using h
  have hneg : sphereOutwardDeterminant 3 (sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection) x) c < 0 := by
    rw [sphereOutwardDeterminant_sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection) x b, hdet]
    linarith
  have hne : c.orientation ≠ o.orientation (sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection) x) := by
    intro h
    have hlt := (sphereOrientation_characterization 3 (by decide)
      (sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection) x) c).mp h
    exact absurd hlt (not_lt.mpr (le_of_lt hneg))
  have hmap : Orientation.map (Fin 3) D (o.orientation x) = c.orientation := by
    rw [← hb]
    exact (Module.Basis.orientation_map b D).symm
  rcases Basis.orientation_eq_or_eq_neg c
    (o.orientation (sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection) x)) with h | h
  · exact absurd h.symm hne
  · rw [hmap, ManifoldOrientation.opposite_orientation, h]
    exact (neg_neg c.orientation).symm

theorem standardThreeSphere_orientationReversing_diffeomorph :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphere.opposite.toClosedOrientedManifold
      standardThreeSphere.toClosedOrientedManifold) := by
  let v : W4 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis 0
  have hv : v ≠ 0 := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.ne_zero 0
  refine ⟨⟨(sphereLinearIsometryDiffeomorph ((ℝ ∙ v)ᗮ.reflection)).symm, ?_⟩⟩
  have h := Diffeomorph.preservesOrientation_symm
    (sphereReflectionDiffeomorph_preservesOrientation_opposite v hv)
  have h1 : (standardThreeSphere.opposite.toClosedOrientedManifold).orientation =
      (sphereOrientation 3 (by decide)).opposite := rfl
  have h2 : (standardThreeSphere.toClosedOrientedManifold).orientation =
      sphereOrientation 3 (by decide) := rfl
  rw [h1, h2]
  exact h

theorem standardThreeSphereLift_orientationReversing_diffeomorph :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨r⟩ := standardThreeSphere_orientationReversing_diffeomorph
  let F : ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphere.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold :=
    ClosedOrientedManifold.uliftOrientedDiffeomorph standardThreeSphere.toClosedOrientedManifold
  let Fop : ClosedOrientedManifold.OrientedDiffeomorph
      standardThreeSphere.opposite.toClosedOrientedManifold
      standardThreeSphereLift.{u}.opposite.toClosedOrientedManifold :=
    ⟨F.1, Diffeomorph.preservesOrientation_opposite F.2⟩
  exact ⟨Fop.symm.trans (r.trans F)⟩

end DifferentialGeometry.Topology
