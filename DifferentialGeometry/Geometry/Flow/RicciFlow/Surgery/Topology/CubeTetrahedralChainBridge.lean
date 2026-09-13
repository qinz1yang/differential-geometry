import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CubeBoundaryFaceChain
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap
open scoped Topology Simplicial

universe u v

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem moduleCat_sum_apply {ι : Type*} {M N : ModuleCat.{v} ℤ} (s : Finset ι)
    (f : ι → (M ⟶ N)) (y : M) : (Finset.sum s f) y = Finset.sum s fun i => f i y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

private theorem uliftCoefficients_hom_ext {N : ModuleCat.{v} ℤ}
    (f g : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ N)
    (h : f (ULift.up (1 : ℤ)) = g (ULift.up (1 : ℤ))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  have hk : (ULift.up k : ULift.{v} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{v} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul, h]

private theorem hurewiczCubeChain_apply_one_eq_sum (c : GenLoop (Fin 3) X x) :
    hurewiczCubeChain c (ULift.up (1 : ℤ)) =
      ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
        DifferentialGeometry.Topology.integralSimplexChain 3
          ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋3⦌)).symm
            (c.val.comp (staircaseSimplex e))) := by
  rw [hurewiczCubeChain]
  erw [moduleCat_sum_apply]
  exact Finset.sum_congr rfl fun e _ => rfl

private theorem cubeTetrahedralChain_eq_sum :
    DifferentialGeometry.Topology.cubeTetrahedralChain =
      ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
        DifferentialGeometry.Topology.integralSimplexChain 3
          ((TopCat.toSSetObjEquiv (TopCat.of (Fin 3 → unitInterval)) (Opposite.op ⦋3⦌)).symm
            (staircaseSimplex e)) := by
  rw [DifferentialGeometry.Topology.cubeTetrahedralChain, cubeChain]
  erw [moduleCat_sum_apply]
  exact Finset.sum_congr rfl fun e _ => rfl

theorem hurewiczCubeChain_apply_one (c : GenLoop (Fin 3) X x) :
    hurewiczCubeChain c (ULift.up (1 : ℤ)) =
      DifferentialGeometry.Topology.singularChainImageGen 3 c.val
        DifferentialGeometry.Topology.cubeTetrahedralChain := by
  rw [hurewiczCubeChain_apply_one_eq_sum c, cubeTetrahedralChain_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul, DifferentialGeometry.Topology.singularChainImageGen_simplex]
  have hσ : ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋3⦌)).symm
        (c.val.comp (staircaseSimplex e))) =
      DifferentialGeometry.Topology.singularSimplexImageGen 3 c.val
        ((TopCat.toSSetObjEquiv (TopCat.of (Fin 3 → unitInterval)) (Opposite.op ⦋3⦌)).symm
          (staircaseSimplex e)) := by
    have h := DifferentialGeometry.Topology.singularSimplexImageGen_val (n := 3) (f := c.val)
      (σ := ((TopCat.of (Fin 3 → unitInterval)).toSSetObjEquiv (Opposite.op ⦋3⦌)).symm
        (staircaseSimplex e))
    rw [Equiv.apply_symm_apply] at h
    exact (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋3⦌)).symm_apply_eq).mpr h.symm
  rw [hσ]

private theorem integralChainHom_apply_one (n : ℕ)
    (y : (DifferentialGeometry.Topology.integralSingularChains X).X n) :
    DifferentialGeometry.Topology.integralChainHom n y (ULift.up (1 : ℤ)) = y := by
  change (DifferentialGeometry.Topology.integralChainHom n y).hom (ULift.up (1 : ℤ)) = y
  rw [DifferentialGeometry.Topology.integralChainHom_hom, LinearMap.comp_apply]
  exact LinearMap.toSpanSingleton_apply_one ℤ _ y

private theorem integralChainHom_injective (n : ℕ) :
    Function.Injective (fun y : (DifferentialGeometry.Topology.integralSingularChains X).X n =>
      DifferentialGeometry.Topology.integralChainHom n y) := by
  intro y z h
  have h' := congrArg (fun phi => phi (ULift.up (1 : ℤ))) h
  erw [integralChainHom_apply_one, integralChainHom_apply_one] at h'
  exact h'

theorem hurewiczCubeChain_eq_integralChainHom_cubeTetrahedralChain (c : GenLoop (Fin 3) X x) :
    hurewiczCubeChain c = DifferentialGeometry.Topology.integralChainHom 3
      (DifferentialGeometry.Topology.singularChainImageGen 3 c.val
        DifferentialGeometry.Topology.cubeTetrahedralChain) := by
  apply uliftCoefficients_hom_ext
  erw [hurewiczCubeChain_apply_one c, integralChainHom_apply_one]

theorem cubeTetrahedralChain_image_boundary_eq_faces (c : GenLoop (Fin 3) X x) :
    (DifferentialGeometry.Topology.integralSingularChains X).d 3 2
        (DifferentialGeometry.Topology.singularChainImageGen 3 c.val
          DifferentialGeometry.Topology.cubeTetrahedralChain) =
      DifferentialGeometry.Topology.singularChainImageGen 2 c.val
        (∑ i : Fin 3, (DifferentialGeometry.Topology.cubeTopFaceElement i -
          DifferentialGeometry.Topology.cubeBottomFaceElement i)) := by
  rw [DifferentialGeometry.Topology.singularChainImageGen_d_eq 2 c.val
      DifferentialGeometry.Topology.cubeTetrahedralChain,
    DifferentialGeometry.Topology.cubeTetrahedralChain_boundary]

theorem cubeTetrahedralChain_image_boundary (c : GenLoop (Fin 3) X x) :
    (IntegralChains X).d 3 2 (DifferentialGeometry.Topology.singularChainImageGen 3 c.val
      DifferentialGeometry.Topology.cubeTetrahedralChain) = 0 := by
  have h := hurewiczCubeChain_boundary c
  erw [hurewiczCubeChain_eq_integralChainHom_cubeTetrahedralChain c,
    DifferentialGeometry.Topology.integralChainHom_d 2] at h
  exact integralChainHom_injective 2
    (h.trans (DifferentialGeometry.Topology.integralChainHom_zero 2).symm)

theorem hurewiczCubeClass_eq_integralHomologyClass_cubeTetrahedralChain (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass c = DifferentialGeometry.Topology.integralHomologyClass 2
      (DifferentialGeometry.Topology.singularChainImageGen 3 c.val
        DifferentialGeometry.Topology.cubeTetrahedralChain)
      (cubeTetrahedralChain_image_boundary c) := by
  unfold hurewiczCubeClass DifferentialGeometry.Topology.integralHomologyClass
  exact DifferentialGeometry.Topology.integralHomologyClassOf_congr
    (hurewiczCubeChain_eq_integralChainHom_cubeTetrahedralChain c)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem integralChainHom_cubeTetrahedralChain_image_comp_d (c : GenLoop (Fin 3) X x) :
    integralChainHom 3 (singularChainImageGen 3 c.val cubeTetrahedralChain) ≫
      (integralSingularChains X).d 3 2 = 0 := by
  rw [integralChainHom_d 2]
  erw [cubeTetrahedralChain_image_boundary c]
  exact integralChainHom_zero 2

theorem cubeTetrahedralChain_image_relative_boundary (c : GenLoop (Fin 3) X x) (A : Set X) :
    (integralChainHom 3 (singularChainImageGen 3 c.val cubeTetrahedralChain) ≫
      (integralRelativeProjection A).f 3) ≫ (integralRelativeChains A).d 3 2 = 0 :=
  integralRelativeChain_projection_boundary 1 A
    (integralChainHom 3 (singularChainImageGen 3 c.val cubeTetrahedralChain)) 0 (by
      rw [CategoryTheory.Limits.zero_comp]
      erw [integralChainHom_cubeTetrahedralChain_image_comp_d c])

theorem integralAbsoluteToRelative_hurewiczCubeClass_eq_integralRelativeClassOf_cubeTetrahedralChain
    (c : GenLoop (Fin 3) X x) (A : Set X) :
    integralAbsoluteToRelative 3 A (hurewiczCubeClass c) =
      integralRelativeClassOf 2 A
        (integralChainHom 3 (singularChainImageGen 3 c.val cubeTetrahedralChain) ≫
          (integralRelativeProjection A).f 3)
        (cubeTetrahedralChain_image_relative_boundary c A) := by
  rw [hurewiczCubeClass_eq_integralHomologyClass_cubeTetrahedralChain c]
  unfold integralHomologyClass
  exact integralAbsoluteToRelative_homologyClassOf 2 A _
    (integralChainHom_cubeTetrahedralChain_image_comp_d c)
    (cubeTetrahedralChain_image_relative_boundary c A)

end DifferentialGeometry.Topology
