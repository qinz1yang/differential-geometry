import DifferentialGeometry.Topology.Homotopy.CubeSphereLocalHomeomorph
import DifferentialGeometry.Topology.Homology.LocalGerm

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomologyMap_liftedCubeSphereProjection_bijective (n k : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval))
    (hx : x.down ∈ cubeInterior (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (liftedCubeSphereProjection n)
      (liftedCubeSphereProjection_mapsTo n x hx)) := by
  let e := liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n
  have hmap := integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph k
    (liftedCubeSphereProjection n) e x e.source e.open_source hx Subset.rfl
    (fun _ _ => rfl) (liftedCubeSphereProjection_mapsTo n x hx)
  have hbij : Function.Bijective
      (integralLocalHomologyOpenPartialHomeomorphIso k e x hx).hom.hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact hmap.symm ▸ hbij

end DifferentialGeometry.Topology
