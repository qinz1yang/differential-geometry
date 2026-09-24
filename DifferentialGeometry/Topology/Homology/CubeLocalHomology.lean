import DifferentialGeometry.Topology.Homotopy.CubeInterior
import DifferentialGeometry.Topology.Homology.RelativeHomeomorphism

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

open Set

def cubeCoordinateInclusion (N : Type u) : C(N → unitInterval, N → ℝ) :=
  ⟨fun x i => (x i : ℝ), by fun_prop⟩

theorem cubeCoordinateInclusion_injective (N : Type u) :
    Function.Injective (cubeCoordinateInclusion N) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

private def openCube (N : Type u) : Set (N → ℝ) :=
  {x | ∀ i, 0 < x i ∧ x i < 1}

private theorem isOpen_openCube (N : Type u) [Finite N] : IsOpen (openCube N) := by
  have h : openCube N = ⋂ i : N, (fun x : N → ℝ => x i) ⁻¹' Ioo (0 : ℝ) 1 := by
    ext x
    simp only [openCube, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioo]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

private def cubeInteriorCoordinateHomeomorph (N : Type u) :
    cubeInterior N ≃ₜ openCube N where
  toFun x := ⟨cubeCoordinateInclusion N x, x.property⟩
  invFun x := ⟨fun i => ⟨x.val i, (x.property i).1.le, (x.property i).2.le⟩, x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

theorem cubeCoordinateInclusion_mapsTo_pointComplement (N : Type u)
    (p : N → unitInterval) :
    MapsTo (cubeCoordinateInclusion N) ({p}ᶜ : Set (N → unitInterval))
      ({cubeCoordinateInclusion N p}ᶜ : Set (N → ℝ)) :=
  fun _ hx => (cubeCoordinateInclusion_injective N).ne hx

theorem integralRelativeHomologyMap_cubeCoordinateInclusion_bijective
    (N : Type u) [Finite N] (k : ℕ) (p : N → unitInterval) (hp : p ∈ cubeInterior N) :
    Function.Bijective (integralRelativeHomologyMap k (cubeCoordinateInclusion N)
      (cubeCoordinateInclusion_mapsTo_pointComplement N p)) := by
  let f := cubeCoordinateInclusion N
  let e := cubeInteriorCoordinateHomeomorph N
  have hUV : MapsTo f (cubeInterior N) (openCube N) := fun _ h => h
  let Jx := integralLocalHomologyNeighborhoodIso k p (cubeInterior N) (isOpen_cubeInterior N) hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p) (openCube N) (isOpen_openCube N) (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e (⟨p, hp⟩ : cubeInterior N)
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (cubeCoordinateInclusion_mapsTo_pointComplement N p) (cubeInterior N) (openCube N)
    (isOpen_cubeInterior N) (isOpen_openCube N) hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (cubeCoordinateInclusion_mapsTo_pointComplement N p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp


def liftedCubeCoordinateInclusion (N : Type u) :
    C(ULift.{v} (N → unitInterval), ULift.{v} (N → ℝ)) :=
  ⟨fun x => ULift.up (cubeCoordinateInclusion N x.down), by fun_prop⟩

theorem liftedCubeCoordinateInclusion_injective (N : Type u) :
    Function.Injective (liftedCubeCoordinateInclusion.{u,v} N) := by
  intro x y h
  apply ULift.ext
  exact cubeCoordinateInclusion_injective N (congrArg ULift.down h)

theorem liftedCubeCoordinateInclusion_mapsTo_pointComplement (N : Type u)
    (p : ULift.{v} (N → unitInterval)) :
    MapsTo (liftedCubeCoordinateInclusion N) ({p}ᶜ : Set (ULift.{v} (N → unitInterval)))
      ({liftedCubeCoordinateInclusion N p}ᶜ : Set (ULift.{v} (N → ℝ))) :=
  fun _ hx => (liftedCubeCoordinateInclusion_injective N).ne hx

private def liftedCubeInterior (N : Type u) : Set (ULift.{v} (N → unitInterval)) :=
  {x | x.down ∈ cubeInterior N}

private def liftedOpenCube (N : Type u) : Set (ULift.{v} (N → ℝ)) :=
  {x | ∀ i, 0 < x.down i ∧ x.down i < 1}

private theorem isOpen_liftedCubeInterior (N : Type u) [Finite N] :
    IsOpen (liftedCubeInterior.{u,v} N) :=
  (isOpen_cubeInterior N).preimage continuous_uliftDown

private theorem isOpen_liftedOpenCube (N : Type u) [Finite N] :
    IsOpen (liftedOpenCube.{u,v} N) := by
  have h : liftedOpenCube.{u,v} N =
      ⋂ i : N, (fun x : ULift.{v} (N → ℝ) => x.down i) ⁻¹' Ioo (0 : ℝ) 1 := by
    ext x
    simp only [liftedOpenCube, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioo]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage ((continuous_apply i).comp continuous_uliftDown)

private def liftedCubeInteriorCoordinateHomeomorph (N : Type u) :
    liftedCubeInterior.{u,v} N ≃ₜ liftedOpenCube.{u,v} N where
  toFun x := ⟨liftedCubeCoordinateInclusion N x, x.property⟩
  invFun x := ⟨ULift.up (fun i => ⟨x.val.down i,
    (x.property i).1.le, (x.property i).2.le⟩), x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp
      (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _

theorem integralRelativeHomologyMap_liftedCubeCoordinateInclusion_bijective
    (N : Type u) [Finite N] (k : ℕ) (p : ULift.{v} (N → unitInterval))
    (hp : p.down ∈ cubeInterior N) :
    Function.Bijective (integralRelativeHomologyMap k (liftedCubeCoordinateInclusion N)
      (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)) := by
  let f := liftedCubeCoordinateInclusion N
  let e := liftedCubeInteriorCoordinateHomeomorph.{u,v} N
  have hUV : MapsTo f (liftedCubeInterior N) (liftedOpenCube N) := fun _ h => h
  let Jx := integralLocalHomologyNeighborhoodIso k p (liftedCubeInterior N)
    (isOpen_liftedCubeInterior N) hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p) (liftedOpenCube N)
    (isOpen_liftedOpenCube N) (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e (⟨p, hp⟩ : liftedCubeInterior N)
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)
    (liftedCubeInterior N) (liftedOpenCube N)
    (isOpen_liftedCubeInterior N) (isOpen_liftedOpenCube N) hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (liftedCubeCoordinateInclusion_mapsTo_pointComplement N p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp


end DifferentialGeometry.Topology
