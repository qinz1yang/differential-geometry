import DifferentialGeometry.Topology.FundamentalGroup.CirclePowerDegree
import DifferentialGeometry.Topology.FundamentalGroup.BasedMapComposition
import DifferentialGeometry.Topology.FundamentalGroup.TorusSlope
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology
open scoped ContinuousMap Matrix

namespace Circle

@[simp] theorem slopeContinuousMap_one (v : Fin 2 → ℤ) :
    slopeContinuousMap v 1 = (1, 1) := by
  simp [slopeContinuousMap, slopeMap]

def matrixContinuousMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    C(Circle × Circle, Circle × Circle) :=
  ⟨matrixMap A, (matrixMap_contMDiff A).continuous⟩

@[simp] theorem matrixContinuousMap_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    matrixContinuousMap A (1, 1) = (1, 1) := by
  simp [matrixContinuousMap, matrixMap]

theorem matrixContinuousMap_comp_slope (A : Matrix (Fin 2) (Fin 2) ℤ)
    (v : Fin 2 → ℤ) :
    (matrixContinuousMap A).comp (slopeContinuousMap v) =
      slopeContinuousMap (A *ᵥ v) := by
  apply ContinuousMap.ext
  intro z
  exact matrixMap_slopeMap A v z

end Circle

namespace GC.Topology

theorem torusFundamentalGroup_map_slope (v : Fin 2 → ℤ)
    (a : FundamentalGroup Circle 1) :
    torusFundamentalGroup
      (FundamentalGroup.mapOfEq (Circle.slopeContinuousMap v)
        (Circle.slopeContinuousMap_one v) a) =
      (Multiplicative.ofAdd (v 0 * (fundamentalGroupCircleEquivInt a).toAdd),
       Multiplicative.ofAdd (v 1 * (fundamentalGroupCircleEquivInt a).toAdd)) := by
  change (fundamentalGroupCircleEquivInt.prodCongr fundamentalGroupCircleEquivInt)
    (fundamentalGroupProdEquiv (1 : Circle) (1 : Circle)
      (FundamentalGroup.mapOfEq
        ((circlePowerMap (v 0)).prodMk (circlePowerMap (v 1)))
        (show ((circlePowerMap (v 0)).prodMk (circlePowerMap (v 1))) (1 : Circle) = (1, 1) from
          Prod.ext (circlePowerMap_one (v 0)) (circlePowerMap_one (v 1))) a)) = _
  rw [fundamentalGroup_mapOfEq_prodMk (circlePowerMap (v 0)) (circlePowerMap (v 1))
    (circlePowerMap_one (v 0)) (circlePowerMap_one (v 1))]
  exact Prod.ext (fundamentalGroupCircleEquivInt_map_power (v 0) a)
    (fundamentalGroupCircleEquivInt_map_power (v 1) a)

private theorem torus_split_coordinate_inclusions (a : FundamentalGroup Torus (1, 1)) :
    a = FundamentalGroup.mapOfEq (Circle.slopeContinuousMap ![1, 0])
        (Circle.slopeContinuousMap_one ![1, 0])
        ((fundamentalGroupProdEquiv (1 : Circle) (1 : Circle) a).1) *
      FundamentalGroup.mapOfEq (Circle.slopeContinuousMap ![0, 1])
        (Circle.slopeContinuousMap_one ![0, 1])
        ((fundamentalGroupProdEquiv (1 : Circle) (1 : Circle) a).2) := by
  apply torusFundamentalGroup.injective
  rw [map_mul, torusFundamentalGroup_map_slope, torusFundamentalGroup_map_slope]
  change (torusFundamentalGroup a) =
    (Multiplicative.ofAdd (1 * (torusFundamentalGroup a).1.toAdd),
      Multiplicative.ofAdd (0 * (torusFundamentalGroup a).1.toAdd)) *
    (Multiplicative.ofAdd (0 * (torusFundamentalGroup a).2.toAdd),
      Multiplicative.ofAdd (1 * (torusFundamentalGroup a).2.toAdd))
  simp

theorem fundamentalGroup_map_matrix_slope (A : Matrix (Fin 2) (Fin 2) ℤ)
    (v : Fin 2 → ℤ) (a : FundamentalGroup Circle 1) :
    FundamentalGroup.mapOfEq (Circle.matrixContinuousMap A)
      (Circle.matrixContinuousMap_one A)
      (FundamentalGroup.mapOfEq (Circle.slopeContinuousMap v)
        (Circle.slopeContinuousMap_one v) a) =
    FundamentalGroup.mapOfEq (Circle.slopeContinuousMap (A *ᵥ v))
      (Circle.slopeContinuousMap_one (A *ᵥ v)) a := by
  have h := congrArg (fun f => f a)
    (fundamentalGroup_mapOfEq_comp (Circle.slopeContinuousMap v)
      (Circle.matrixContinuousMap A) (Circle.slopeContinuousMap_one v)
      (Circle.matrixContinuousMap_one A))
  simpa only [Circle.matrixContinuousMap_comp_slope, MonoidHom.comp_apply] using h.symm

theorem torusFundamentalGroup_map_matrix (A : Matrix (Fin 2) (Fin 2) ℤ)
    (a : FundamentalGroup Torus (1, 1)) :
    torusFundamentalGroup
      (FundamentalGroup.mapOfEq (Circle.matrixContinuousMap A)
        (Circle.matrixContinuousMap_one A) a) =
      (Multiplicative.ofAdd ((A *ᵥ
        ![(torusFundamentalGroup a).1.toAdd, (torusFundamentalGroup a).2.toAdd]) 0),
       Multiplicative.ofAdd ((A *ᵥ
        ![(torusFundamentalGroup a).1.toAdd, (torusFundamentalGroup a).2.toAdd]) 1)) := by
  have h := congrArg (fun q => torusFundamentalGroup
    (FundamentalGroup.mapOfEq (Circle.matrixContinuousMap A)
      (Circle.matrixContinuousMap_one A) q)) (torus_split_coordinate_inclusions a)
  rw [map_mul, map_mul, fundamentalGroup_map_matrix_slope,
    fundamentalGroup_map_matrix_slope, torusFundamentalGroup_map_slope,
    torusFundamentalGroup_map_slope] at h
  change torusFundamentalGroup
    (FundamentalGroup.mapOfEq (Circle.matrixContinuousMap A)
      (Circle.matrixContinuousMap_one A) a) =
    (Multiplicative.ofAdd ((A *ᵥ ![1, 0]) 0 * (torusFundamentalGroup a).1.toAdd),
     Multiplicative.ofAdd ((A *ᵥ ![1, 0]) 1 * (torusFundamentalGroup a).1.toAdd)) *
    (Multiplicative.ofAdd ((A *ᵥ ![0, 1]) 0 * (torusFundamentalGroup a).2.toAdd),
     Multiplicative.ofAdd ((A *ᵥ ![0, 1]) 1 * (torusFundamentalGroup a).2.toAdd)) at h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← ofAdd_add] using h

end GC.Topology
