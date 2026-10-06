import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalCh5Port
open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_isPLHomeomorphInto_dist_lt_of_isOpen_three
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) (η : M₁ → ℝ)
    (hηc : ContinuousOn η U) (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ ∀ x ∈ U, dist (f x) (h x) < η x := by
  rcases isEmpty_or_nonempty M₁ with hM | hM
  · have hUe : U = ∅ := eq_empty_iff_forall_notMem.mpr fun x _ => (hM.false x).elim
    exact ⟨h, by rw [hUe]; exact isPLHomeomorphInto_empty h, fun x _ => (hM.false x).elim⟩
  · have : Nonempty M₂ := ⟨h (Classical.arbitrary M₁)⟩
    obtain ⟨Λ, dim, face, P, Q, r, s, u, v, sourceCell, targetCell, carrier, hdim, hr, hs, hu,
      hv, hsourceCell, htargetCell, hfaceDim, hsourceBoundary, htargetBoundary, hsourceInter,
      htargetInter, hLFs, hLFt, hcover, hcarrier, hsmall⟩ := exists_controlled_cell_decomposition hU hh η hηc hηpos
    exact exists_isPLHomeomorphInto_dist_lt_of_cellDiagram dim face P Q r s u v sourceCell
      targetCell carrier U h η hdim hr hs hu hv hsourceCell htargetCell hfaceDim
      hsourceBoundary htargetBoundary hsourceInter htargetInter hLFs hLFt hcover hcarrier hsmall

end DifferentialGeometry.Topology.PiecewiseLinear
