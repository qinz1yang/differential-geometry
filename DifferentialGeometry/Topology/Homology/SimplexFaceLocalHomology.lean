import DifferentialGeometry.Topology.Simplex.FaceLocalHomeomorph
import DifferentialGeometry.Topology.Homology.LocalGerm

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomologyMap_liftedFaceToBoundary_bijective
    {n : ℕ} (k : ℕ) (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1))))
    (hp : p.down ∉ Simplex.boundary (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (Simplex.liftedFaceToBoundary i)
      (Simplex.liftedFaceToBoundary_mapsTo i p)) := by
  let e := Simplex.liftedFaceOpenPartialHomeomorph.{u} i
  have hmap := integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph k
    (Simplex.liftedFaceToBoundary i) e p e.source e.open_source hp Subset.rfl
    (fun _ _ => rfl) (Simplex.liftedFaceToBoundary_mapsTo i p)
  have hbij : Function.Bijective
      (integralLocalHomologyOpenPartialHomeomorphIso k e p hp).hom.hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact hmap.symm ▸ hbij

theorem integralRelativeHomologyMap_liftedFaceToBoundary_barycenter_bijective
    {n : ℕ} (k : ℕ) (i : Fin (n + 2)) :
    Function.Bijective (integralRelativeHomologyMap k (Simplex.liftedFaceToBoundary.{u} i)
      (Simplex.liftedFaceToBoundary_mapsTo i (ULift.up stdSimplex.barycenter))) := by
  apply integralRelativeHomologyMap_liftedFaceToBoundary_bijective
  exact fun h => Simplex.boundary_ne_barycenter h rfl

end DifferentialGeometry.Topology
