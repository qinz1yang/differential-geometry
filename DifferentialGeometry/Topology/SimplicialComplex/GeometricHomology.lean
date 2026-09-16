import DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationHomeomorphism
import DifferentialGeometry.Topology.SimplicialSet.FiniteRealizationHomology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u

theorem isZero_singularHomology_geometricSpace_of_card_le
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {k : Type u} [Ring k] (R : ModuleCat.{u} k) (d : ℕ)
    (hd : ∀ s ∈ K.faces, s.card ≤ d) (q : ℕ) (hq : d ≤ q) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj R).obj (TopCat.of K.space)) := by
  classical
  let _ := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let X := orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let _ : X.HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K.toPreAbstractSimplicialComplex d hd
  have hX := X.isZero_homology_of_hasDimensionLT R q d hq
  have hT := hX.of_iso (DifferentialGeometry.SSet.realizationHomologyIso R X q).symm
  exact hT.of_iso (((singularHomologyFunctor (ModuleCat.{u} k) q).obj R).mapIso
    (TopCat.isoOfHomeo (geometricRealizationHomeomorphism K))).symm

end DifferentialGeometry.Topology.SimplicialComplex
