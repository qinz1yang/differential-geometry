import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem IsSolutionOn.eventually_lt_time_of_scalar_tendsto_atTop
    {a T : ℝ} {haT : a < T}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a T haT)}
    (hS : IsSolutionOn S) {α : Type*} {l : Filter α} {x : α → M} {t : α → ℝ}
    (htmem : ∀ᶠ i in l, t i ∈ Ico a T)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) l atTop)
    {b : ℝ} (hb : b < T) : ∀ᶠ i in l, b < t i := by
  have hK : IsCompact (Icc a b ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
  have hsub : Icc a b ×ˢ (univ : Set M) ⊆
      (RealTimeInterval.closedOpen a T haT).carrier ×ˢ univ :=
    prod_mono (fun _ hz => ⟨hz.1, hz.2.trans_lt hb⟩) subset_rfl
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hS.scalarCont.mono hsub)
  filter_upwards [htmem, hscalar.eventually_gt_atTop B] with i hi hBi
  by_contra hnot
  have hbound := hB ⟨(t i, x i), ⟨⟨hi.1, le_of_not_gt hnot⟩, mem_univ _⟩, rfl⟩
  exact (not_lt_of_ge hbound) hBi

theorem IsSolutionOn.tendsto_time_of_scalar_tendsto_atTop
    {a T : ℝ} {haT : a < T}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a T haT)}
    (hS : IsSolutionOn S) {α : Type*} {l : Filter α} {x : α → M} {t : α → ℝ}
    (htmem : ∀ᶠ i in l, t i ∈ Ico a T)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) l atTop) :
    Tendsto t l (𝓝 T) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact hS.eventually_lt_time_of_scalar_tendsto_atTop htmem hscalar hb
  · intro b hb
    exact htmem.mono fun _ hi => hi.2.trans hb

end DifferentialGeometry.PDE.RicciFlow
