import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.CoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Tensor.Multilinear.Basis

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.Multilinear
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

private theorem rm04_chart_contMDiffAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => S.base.rm04 q.1 q.2
        (fun a : Fin 4 => chartBasisVecFiber (I := I) x (K a) q.2)) (t, x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (D.regular_isOpen.mem_nhds ht)
  obtain ⟨c, hac, hct⟩ := exists_between hat
  let D' := RealTimeInterval.closedOpen c b (hct.trans htb)
  have hcar : D'.carrier ⊆ D.carrier := by
    intro s hs
    exact D.regular_subset (hab ⟨hac.trans_le hs.1, hs.2⟩)
  have hreg : D'.regular ⊆ D.regular := by
    intro s hs
    exact hab ⟨hac.trans hs.1, hs.2⟩
  have hS' : IsSolutionOn (S.timeRestrict D') := isSoln_timeRestrict hS hcar hreg
  exact coordRmSmoothInf (I := I) hS' x ⟨t, hct, htb⟩ x
    (self_mem_chartLeviCivitaGoodSet (I := I) x) K

theorem rm04_contMDiffOn_regular_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, S.base.rm04 p.1 p.2⟩ :
        TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
          (Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I : M → Type _))))
      (D.regular ×ˢ (Set.univ : Set M)) := by
  intro p hp
  rw [contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let B := continuousMultilinearMapBasis (chartModelBasis E) 4
  let f := fun q : ℝ × M =>
    (trivializationAt (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
      (Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I)) p.2
      ⟨q.2, S.base.rm04 q.1 q.2⟩).2
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
    𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) ∞ f
      (D.regular ×ˢ (Set.univ : Set M)) p
  rw [show f = fun q => B.equivFun.symm (B.equivFun (f q)) from
    funext fun q => (B.equivFun.symm_apply_apply (f q)).symm]
  refine B.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p ?_
  refine contMDiffWithinAt_pi_space.mpr fun K => ?_
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun q => B.repr (f q) K) (D.regular ×ˢ (Set.univ : Set M)) p
  simp only [B, continuousMultilinearMap_basis_repr]
  change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun q : ℝ × M => S.base.rm04 q.1 q.2
      (fun a : Fin 4 => chartBasisVecFiber (I := I) p.2 (K a) q.2))
    (D.regular ×ˢ (Set.univ : Set M)) p
  exact (rm04_chart_contMDiffAt_of_solution S hS hp.1 p.2 K).contMDiffWithinAt

omit [I.Boundaryless] in
theorem rm04_continuousOn_carrier_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) :
    ContinuousOn
      (fun p : ℝ × M => (⟨p.2, S.base.rm04 p.1 p.2⟩ :
        TotalSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
          (Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I : M → Type _))))
      (D.carrier ×ˢ (Set.univ : Set M)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact hS.rm04Cont.comp
    (((continuous_fst.comp continuous_subtype_val).subtype_mk fun p => p.property.1).prodMk
      (continuous_snd.comp continuous_subtype_val))

end DifferentialGeometry.PDE.RicciFlow
