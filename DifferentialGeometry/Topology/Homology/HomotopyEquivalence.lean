import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

theorem isIso_singularHomologyMap_of_homotopyEquiv
    {k : Type u} [Ring k] (R : ModuleCat.{u} k) {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (TopCat.ofHom e.toFun)) := by
  let H := (singularHomologyFunctor (ModuleCat.{u} k) n).obj R
  refine ⟨⟨H.map (TopCat.ofHom e.invFun), ?_, ?_⟩⟩
  · rw [← Functor.map_comp]
    have h : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    exact (h.congr_homologyMap_singularChainComplexFunctor R n).trans (H.map_id X)
  · rw [← Functor.map_comp]
    have h : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    exact (h.congr_homologyMap_singularChainComplexFunctor R n).trans (H.map_id Y)

end DifferentialGeometry.Homology
