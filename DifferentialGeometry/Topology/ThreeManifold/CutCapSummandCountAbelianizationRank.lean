import DifferentialGeometry.Topology.Algebra.Group.FinitelyGeneratedFundamentalGroup
import DifferentialGeometry.Topology.Algebra.Module.RankInvariant
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSumSummandCountUnique
import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentRealizationReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountTopologicalAssembly
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff TensorProduct

namespace DifferentialGeometry.Topology

universe u

theorem finrank_tensorProduct_abelianization_fundamentalGroup_of_isSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3} (hF : isSphereTwoTimesCircleFactor F)
    (x : F.Carrier) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Additive
      (Abelianization (FundamentalGroup F.Carrier x))) = 1 := by
  have e : Abelianization (FundamentalGroup F.Carrier x) ≃* Multiplicative ℤ :=
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x
      (chosenPoint F)).abelianizationCongr).trans
      (abelianization_fundamentalGroup_of_isSphereTwoTimesCircleFactor hF).some
  have h := (LinearEquiv.baseChange ℤ ℚ _ _
    (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive e))).finrank_eq
  rw [h]
  exact DifferentialGeometry.Algebra.Module.finrank_tensorProduct_int

theorem finrank_tensorProduct_abelianization_fundamentalGroup_finiteConnectedSum_append
    (L K : List (ConnectedClosedOrientedManifold.{u} 3))
    (hK : ∀ F ∈ K, isSphereTwoTimesCircleFactor F)
    (hfin : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup
      (finiteConnectedSum L).Carrier (chosenPoint (finiteConnectedSum L)))))) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup
        (finiteConnectedSum (L ++ K)).Carrier
        (chosenPoint (finiteConnectedSum (L ++ K)))))) =
      Module.finrank ℚ (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup
        (finiteConnectedSum L).Carrier (chosenPoint (finiteConnectedSum L))))) + K.length := by
  have e : Abelianization (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier
      (chosenPoint (finiteConnectedSum (L ++ K)))) ≃*
      Abelianization (FundamentalGroup (finiteConnectedSum L).Carrier
        (chosenPoint (finiteConnectedSum L))) × (Fin K.length → Multiplicative ℤ) :=
    (abelianization_fundamentalGroup_finiteConnectedSum_append L K).some.trans
      ((MulEquiv.refl _).prodCongr
        (abelianization_fundamentalGroup_finiteConnectedSum_sphereTwoTimesCircleFactors
          K hK).some)
  have h := (LinearEquiv.baseChange ℤ ℚ _ _
    (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive e))).finrank_eq
  rw [h]
  exact DifferentialGeometry.Algebra.Module.finrank_tensorProduct_prod_fin_int
    (Additive (Abelianization (FundamentalGroup (finiteConnectedSum L).Carrier
      (chosenPoint (finiteConnectedSum L))))) K.length

def RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (p : M.Carrier),
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup M.Carrier p)))

theorem rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_finitelyGenerated
    (h : FinitelyGeneratedAbelianizationFundamentalGroupClosedThreeManifold.{u}) :
    RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{u} :=
  fun M p => Module.Finite.base_change (R := ℤ) (A := ℚ)
    (M := Additive (Abelianization (FundamentalGroup M.Carrier p))) (h := h M p)

theorem rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_finitelyGeneratedFundamentalGroup
    (h : FinitelyGeneratedFundamentalGroupClosedThreeManifold.{u}) :
    RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{u} :=
  fun M p => Module.Finite.base_change (R := ℤ) (A := ℚ)
    (M := Additive (Abelianization (FundamentalGroup M.Carrier p)))
    (h := moduleFinite_int_additive_abelianization_of_groupFG (h M p))

private theorem forall_mem_cons_cons_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    ∀ F ∈ [S, S], isSphereTwoTimesCircleFactor F := by
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> exact hS

theorem finiteConnectedSumSummandCountUnique_cons_cons_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    finiteConnectedSumSummandCountUnique [S, S] :=
  finiteConnectedSumSummandCountUnique_of_sphereTwoTimesCircleFactors [S, S]
    (forall_mem_cons_cons_of_isSphereTwoTimesCircleFactor hS)

theorem exists_sphereTwoTimesCircleSummands_length_eq_two_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = 2 ∧ (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum K).toClosedOrientedManifold
          (finiteConnectedSum [S, S]).toClosedOrientedManifold) :=
  ⟨[S, S], rfl, forall_mem_cons_cons_of_isSphereTwoTimesCircleFactor hS,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem length_eq_two_of_orientedDiffeomorph_cons_cons_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    {K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hK : ∀ F ∈ K, isSphereTwoTimesCircleFactor F)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum K).toClosedOrientedManifold
      (finiteConnectedSum [S, S]).toClosedOrientedManifold)) :
    K.length = 2 :=
  finiteConnectedSumSummandCountUnique_nil K [S, S] hK
    (forall_mem_cons_cons_of_isSphereTwoTimesCircleFactor hS) h

theorem not_orientedDiffeomorph_cons_cons_singleton_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    ¬ Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum [S, S]).toClosedOrientedManifold
      (finiteConnectedSum [S]).toClosedOrientedManifold) := by
  intro h
  have hlen := finiteConnectedSumSummandCountUnique_nil [S, S] [S]
    (forall_mem_cons_cons_of_isSphereTwoTimesCircleFactor hS)
    (by simpa using hS) h
  simp only [List.length_cons, List.length_nil] at hlen
  omega

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutCapFactorAbelianizationRationalFinite : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (i : Fin (E.canonicalEnumeration C).length),
    connectedClosedOrientedManifoldAbelianizationRationalFinite ((E.canonicalEnumeration C).get i)

theorem cutCapFactorAbelianizationRationalFinite_of_rationalFiniteAbelianizationFundamentalGroup
    (h : RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{u}) :
    E.cutCapFactorAbelianizationRationalFinite :=
  fun C i => h ((E.canonicalEnumeration C).get i) (chosenPoint ((E.canonicalEnumeration C).get i))

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_cutCapFactorAbelianizationRationalFinite
    (h : E.graphSumRealization) (hfin : E.cutCapFactorAbelianizationRationalFinite) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_canonicalSummandCountUnique h
    fun C => finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationRationalFinite
      (E.canonicalEnumeration C) (hfin C)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_rationalFiniteAbelianizationFundamentalGroup
    (h : E.graphSumRealization)
    (hfin : RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{u}) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_cutCapFactorAbelianizationRationalFinite
    h (E.cutCapFactorAbelianizationRationalFinite_of_rationalFiniteAbelianizationFundamentalGroup
      hfin)

theorem cutCapSummandCountDetermined_of_componentConnectedSumDecomposition_of_cutCapFactorAbelianizationRationalFinite
    (h : E.componentConnectedSumDecomposition)
    (hfin : E.cutCapFactorAbelianizationRationalFinite) : E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_componentConnectedSumDecomposition_of_summandCountUnique h
    fun C => finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationRationalFinite
      (E.canonicalEnumeration C) (hfin C)

theorem cutCapSummandAbsorptionFree_of_cutCapFactorAbelianizationRationalFinite
    (hfin : E.cutCapFactorAbelianizationRationalFinite) : E.cutCapSummandAbsorptionFree :=
  E.cutCapSummandAbsorptionFree_of_summandCountUnique fun C =>
    finiteConnectedSumSummandCountUnique_of_forall_factor_abelianizationRationalFinite
      (E.canonicalEnumeration C) (hfin C)

theorem cutCapSummandCountDetermined_of_noTubeRealization_of_forall_cutIndices_eq_empty_of_cutCapFactorAbelianizationRationalFinite
    (hr : E.NoTubeRealization)
    (hC : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅)
    (hfin : E.cutCapFactorAbelianizationRationalFinite) : E.cutCapSummandCountDetermined :=
  (E.cutCapSummandCountDetermined_iff_cutCapSummandAbsorptionFree_of_forall_cutIndices_eq_empty
    hr hC).mpr (E.cutCapSummandAbsorptionFree_of_cutCapFactorAbelianizationRationalFinite hfin)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
