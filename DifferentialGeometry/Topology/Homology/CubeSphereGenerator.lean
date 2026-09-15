import DifferentialGeometry.Topology.Homology.EuclideanSimplexGenerator
import DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality
import DifferentialGeometry.Topology.Homology.CubeLocalClass
import DifferentialGeometry.Topology.Homology.CubeLocalHomology
import DifferentialGeometry.Topology.Homology.CubeSphereLocalHomology
import DifferentialGeometry.Topology.Homology.SpherePunctureHomology

noncomputable section

open Set

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private def staircaseBarycenter : Fin 3 → ℝ := ![3 / 4, 1 / 2, 1 / 4]

private def tetrahedronStaircaseHomeomorph : liftedSphereSpace.{0} 1 ≃ₜ (Fin 3 → ℝ) where
  toFun v := ![3 / 4 + (v.down 0 + v.down 1 + v.down 2) / 4,
    1 / 2 + (-v.down 0 + v.down 1 + v.down 2) / 2,
    1 / 4 + (-v.down 0 - v.down 1 + 3 * v.down 2) / 4]
  invFun t := ULift.up (WithLp.toLp 2 ![2 * t 0 - t 1 - 1,
    t 0 + t 1 - t 2 - 1, t 0 + t 2 - 1])
  left_inv v := by
    apply ULift.ext
    ext i
    fin_cases i <;> simp <;> ring
  right_inv t := by
    funext i
    fin_cases i <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] private theorem tetrahedronStaircaseHomeomorph_zero :
    tetrahedronStaircaseHomeomorph 0 = staircaseBarycenter := by
  ext i
  fin_cases i <;> norm_num [tetrahedronStaircaseHomeomorph, staircaseBarycenter]

private theorem tetrahedronStaircaseHomeomorph_standardTetrahedronSimplex
    (q : stdSimplex ℝ (Fin 4)) :
    tetrahedronStaircaseHomeomorph (SimplexDegree.standardTetrahedronSimplex q) =
      fun i => (staircaseSimplex (Equiv.refl (Fin 3)) q i).val := by
  have hq := q.property.2
  simp [Fin.sum_univ_succ] at hq
  change tetrahedronStaircaseHomeomorph (ULift.up (positiveTetrahedron q)) = _
  funext i
  fin_cases i <;>
    simp [tetrahedronStaircaseHomeomorph,
      positiveTetrahedron_coordinate, staircaseSimplex, staircaseCoordinate,
      Fin.sum_univ_succ] <;> linarith

universe u

private def liftedTetrahedronStaircaseHomeomorph :
    liftedSphereSpace.{u} 1 ≃ₜ ULift.{u} (Fin 3 → ℝ) :=
  Homeomorph.ulift.trans ((Homeomorph.ulift.symm.trans tetrahedronStaircaseHomeomorph).trans
    Homeomorph.ulift.symm)

private def liftedStaircaseSimplex : C(stdSimplex ℝ (Fin 4), ULift.{u} (Fin 3 → ℝ)) :=
  ⟨fun q => ULift.up (fun i => (staircaseSimplex (Equiv.refl (Fin 3)) q i).val),
    continuous_uliftUp.comp (continuous_pi fun i =>
      continuous_subtype_val.comp ((continuous_apply i).comp (staircaseSimplex _).continuous))⟩

@[simp] private theorem liftedTetrahedronStaircaseHomeomorph_zero :
    liftedTetrahedronStaircaseHomeomorph.{u} 0 = ULift.up staircaseBarycenter := by
  exact congrArg ULift.up tetrahedronStaircaseHomeomorph_zero

private theorem liftedTetrahedronStaircaseHomeomorph_standardTetrahedronSimplex :
    (⟨liftedTetrahedronStaircaseHomeomorph.{u},
      liftedTetrahedronStaircaseHomeomorph.continuous⟩ :
        C(liftedSphereSpace.{u} 1, ULift.{u} (Fin 3 → ℝ))).comp
      SimplexDegree.standardTetrahedronSimplex = liftedStaircaseSimplex := by
  ext q i
  exact congrFun (tetrahedronStaircaseHomeomorph_standardTetrahedronSimplex q) i

private theorem liftedStaircaseSimplex_face_ne_barycenter (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    liftedStaircaseSimplex.{u} (SimplexDegree.orientedSimplexFace i q) ≠
      ULift.up staircaseBarycenter := by
  rw [← liftedTetrahedronStaircaseHomeomorph_standardTetrahedronSimplex,
    ← liftedTetrahedronStaircaseHomeomorph_zero]
  exact liftedTetrahedronStaircaseHomeomorph.injective.ne
    (SimplexDegree.standardTetrahedronSimplex_face_ne_zero i q)

private theorem liftedStaircaseSimplex_localClass_generator_aux :
    Function.Bijective (fun z : ℤ => z •
      SimplexDegree.simplexLocalClass (liftedTetrahedronStaircaseHomeomorph.{u} 0)
        liftedStaircaseSimplex.{u} (fun i q => by
          rw [← liftedTetrahedronStaircaseHomeomorph_standardTetrahedronSimplex]
          apply liftedTetrahedronStaircaseHomeomorph.injective.ne
          exact SimplexDegree.standardTetrahedronSimplex_face_ne_zero i q)) := by
  let e := (integralLocalHomologyHomeomorphIso 3
    liftedTetrahedronStaircaseHomeomorph.{u} 0).toLinearEquiv
  have hf : (fun z : ℤ => z • e SimplexDegree.euclideanStandardSimplexClass) =
      e ∘ (fun z : ℤ => z • SimplexDegree.euclideanStandardSimplexClass.{u}) := by
    funext z
    exact (map_zsmul e z _).symm
  have hgen : Function.Bijective (fun z : ℤ => z • e SimplexDegree.euclideanStandardSimplexClass) := by
    rw [hf]
    exact e.bijective.comp SimplexDegree.euclideanStandardSimplexClass_generator
  change Function.Bijective (fun z : ℤ => z •
    (integralLocalHomologyHomeomorphIso 3 liftedTetrahedronStaircaseHomeomorph.{u} 0).hom.hom
      (SimplexDegree.simplexLocalClass 0 SimplexDegree.standardTetrahedronSimplex
        SimplexDegree.standardTetrahedronSimplex_face_ne_zero)) at hgen
  simpa only [SimplexDegree.integralLocalHomologyHomeomorphIso_simplexLocalClass,
    liftedTetrahedronStaircaseHomeomorph_standardTetrahedronSimplex] using hgen

private theorem liftedStaircaseSimplex_localClass_generator :
    Function.Bijective (fun z : ℤ => z •
      SimplexDegree.simplexLocalClass (ULift.up staircaseBarycenter)
        liftedStaircaseSimplex.{u} liftedStaircaseSimplex_face_ne_barycenter) := by
  have transport (p q : ULift.{u} (Fin 3 → ℝ)) (heq : p = q)
      (hp : ∀ i t, liftedStaircaseSimplex (SimplexDegree.orientedSimplexFace i t) ≠ p)
      (hq : ∀ i t, liftedStaircaseSimplex (SimplexDegree.orientedSimplexFace i t) ≠ q) :
      Function.Bijective (fun z : ℤ => z •
        SimplexDegree.simplexLocalClass p liftedStaircaseSimplex hp) →
      Function.Bijective (fun z : ℤ => z •
        SimplexDegree.simplexLocalClass q liftedStaircaseSimplex hq) := by
    subst q
    exact id
  exact transport _ _ liftedTetrahedronStaircaseHomeomorph_zero _ _
    liftedStaircaseSimplex_localClass_generator_aux

end DifferentialGeometry.Topology

noncomputable section

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem cubeStaircasePoint_mem_interior : cubeStaircasePoint ∈ cubeInterior (Fin 3) := by
  intro i
  fin_cases i <;> norm_num [cubeStaircasePoint]

private theorem liftedCubeCoordinateInclusion_point :
    liftedCubeCoordinateInclusion (Fin 3) (ULift.up cubeStaircasePoint : ULift.{u} _) =
      ULift.up staircaseBarycenter := by
  apply ULift.ext
  funext i
  fin_cases i <;> norm_num [liftedCubeCoordinateInclusion, cubeCoordinateInclusion,
    cubeStaircasePoint, staircaseBarycenter]


theorem liftedCubeLocalClass_generator :
    Function.Bijective (fun z : ℤ => z • liftedCubeLocalClass.{u}) := by
  let f := integralRelativeHomologyMap 3 (liftedCubeCoordinateInclusion (Fin 3))
    (liftedCubeCoordinateInclusion_mapsTo_pointComplement (Fin 3)
      (ULift.up cubeStaircasePoint : ULift.{u} _))
  have hf : Function.Bijective f :=
    integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective (Fin 3) 3 _
      cubeStaircasePoint_mem_interior
  have hfaces (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
      liftedStaircaseSimplex.{u} (SimplexDegree.orientedSimplexFace i q) ≠
        liftedCubeCoordinateInclusion (Fin 3) (ULift.up cubeStaircasePoint) := by
    rw [liftedCubeCoordinateInclusion_point]
    exact liftedStaircaseSimplex_face_ne_barycenter i q
  have himg : f liftedCubeLocalClass =
      SimplexDegree.simplexLocalClass
        (liftedCubeCoordinateInclusion (Fin 3) (ULift.up cubeStaircasePoint))
        liftedStaircaseSimplex hfaces := by
    rw [liftedCubeLocalClass_eq_simplexLocalClass]
    exact SimplexDegree.integralRelativeHomologyMap_simplexLocalClass
      (liftedCubeCoordinateInclusion (Fin 3)) _ _ _ _ _
  have htarget : Function.Bijective (fun z : ℤ => z •
      SimplexDegree.simplexLocalClass
        (liftedCubeCoordinateInclusion (Fin 3) (ULift.up cubeStaircasePoint))
        liftedStaircaseSimplex hfaces) := by
    have transport (p q : ULift.{u} (Fin 3 → ℝ)) (heq : p = q)
        (hp : ∀ i t, liftedStaircaseSimplex (SimplexDegree.orientedSimplexFace i t) ≠ p)
        (hq : ∀ i t, liftedStaircaseSimplex (SimplexDegree.orientedSimplexFace i t) ≠ q) :
        Function.Bijective (fun z : ℤ => z •
          SimplexDegree.simplexLocalClass p liftedStaircaseSimplex hp) →
        Function.Bijective (fun z : ℤ => z •
          SimplexDegree.simplexLocalClass q liftedStaircaseSimplex hq) := by
      subst q
      exact id
    exact transport _ _ liftedCubeCoordinateInclusion_point.symm _ _
      liftedStaircaseSimplex_localClass_generator
  have hgen : Function.Bijective (fun z : ℤ => f (z • liftedCubeLocalClass)) := by
    simpa only [map_zsmul, himg] using htarget
  exact ⟨fun a b h => hgen.1 (congrArg f h), fun y => by
    obtain ⟨z, hz⟩ := hgen.2 (f y)
    exact ⟨z, hf.1 hz⟩⟩

theorem cubeSphereFundamentalClass_isSphereHomologyGenerator :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass := by
  apply (isSphereHomologyGenerator_iff_forall_exists_zsmul 2 cubeSphereFundamentalClass).mpr
  intro y
  let p := liftedCubeSphereProjection.{u} 2 (ULift.up cubeStaircasePoint)
  let hfmap := liftedCubeSphereProjection_mapsTo 2
    (ULift.up cubeStaircasePoint : ULift.{u} _)
    cubeStaircasePoint_mem_interior
  let f := integralRelativeHomologyMap 3 (liftedCubeSphereProjection.{u} 2) hfmap
  let g := integralAbsoluteToRelative 3 ({p}ᶜ : Set (liftedHomotopySphere.{u} 2))
  have hf : Function.Bijective f :=
    integralRelativeHomologyMap_liftedCubeSphereProjection_bijective
      2 3 (ULift.up cubeStaircasePoint) cubeStaircasePoint_mem_interior
  have hg : Function.Bijective g :=
    integralAbsoluteToRelative_liftedSphere_puncture_bijective 2 1 p
  have heq : f liftedCubeLocalClass = g cubeSphereFundamentalClass :=
    integralRelativeHomologyMap_liftedCubeLocalClass (liftedCubeSphereProjection 2) p
      hfmap (cubeSphereCollapse 2) rfl
  obtain ⟨a, ha⟩ := hf.2 (g y)
  obtain ⟨k, hk⟩ := liftedCubeLocalClass_generator.2 a
  change k • liftedCubeLocalClass = a at hk
  refine ⟨k, hg.1 ?_⟩
  change g y = g (k • cubeSphereFundamentalClass)
  rw [map_zsmul, ← heq, ← map_zsmul, hk, ha]

variable {X : Type u} [TopologicalSpace X]

theorem sphereHurewicz_three_mul (x : X) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 2 cubeSphereFundamentalClass).mp
    cubeSphereFundamentalClass_isSphereHomologyGenerator c
  exact sphereHurewicz_mul_of_eq_zsmul_cubeSphereFundamentalClass c k hk x a b

end DifferentialGeometry.Topology
