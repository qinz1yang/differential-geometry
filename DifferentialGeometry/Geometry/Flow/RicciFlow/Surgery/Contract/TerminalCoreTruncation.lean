import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected
import DifferentialGeometry.Topology.Embedding.CompactFrontier

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

def truncatedCore (c : ConnectedComponents D.slab.terminalRegularOpen)
    (t : P.hornIndex c → ℝ) : Set D.slab.terminalRegularOpen :=
  P.core c ∪ ⋃ e, P.horn c e '' (univ ×ˢ Icc (0 : ℝ) (t e))

def hornTail (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (a : ℝ) : Set D.slab.terminalRegularOpen :=
  P.horn c e '' (univ ×ˢ Ici a)

theorem truncatedCore_isCompact
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (t : P.hornIndex c → ℝ) : IsCompact (P.truncatedCore c t) := by
  let : Finite (P.hornIndex c) := P.hornIndex_finite c
  apply (P.core_isCompact c hc).union
  apply isCompact_iUnion
  intro e
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply (P.horn_smooth c e).continuousOn.mono
  rintro p ⟨hp, ht⟩
  exact ⟨hp, ht.1⟩

theorem hornTail_isClosed
    (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (a : ℝ) (ha : 0 ≤ a) : IsClosed (P.hornTail c e a) := by
  have heq : P.hornTail c e a =
      (fun p : HalfNeckCylinder => P.horn c e p.val) '' {p : HalfNeckCylinder | a ≤ p.val.2} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, ha.trans hp.2⟩, hp.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.val, ⟨mem_univ _, hp⟩, rfl⟩
  rw [heq]
  exact (P.horn_proper c e).isClosedMap _
    (isClosed_le continuous_const continuous_subtype_val.snd)

theorem truncatedCore_subset_component
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (t : P.hornIndex c → ℝ) :
    P.truncatedCore c t ⊆ {x | ConnectedComponents.mk x = c} := by
  intro x hx
  rw [P.horn_covers_component c hc]
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨e, p, hp, rfl⟩ := mem_iUnion.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨e, ⟨⟨p, hp.2.1⟩, rfl⟩⟩)

theorem component_subset_truncatedCore_union_tails
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (t : P.hornIndex c → ℝ) :
    {x | ConnectedComponents.mk x = c} ⊆ P.truncatedCore c t ∪ ⋃ e, P.hornTail c e (t e) := by
  intro x hx
  rw [P.horn_covers_component c hc] at hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · obtain ⟨e, p, rfl⟩ := mem_iUnion.mp hx
    by_cases hp : p.val.2 ≤ t e
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨e, p.val, ⟨mem_univ _, p.property, hp⟩, rfl⟩))
    · exact Or.inr (mem_iUnion.mpr ⟨e, p.val, ⟨mem_univ _, (lt_of_not_ge hp).le⟩, rfl⟩)

theorem truncatedCore_inter_tail_subset_slice
    (c : ConnectedComponents D.slab.terminalRegularOpen)
    (t : P.hornIndex c → ℝ) (ht : ∀ e, 0 < t e) (e : P.hornIndex c) :
    P.truncatedCore c t ∩ P.hornTail c e (t e) ⊆
      range (fun y : Sphere 2 => P.horn c e (y, t e)) := by
  rintro x ⟨hx, p, hp, hpx⟩
  rcases hx with hx | hx
  · have hpos : 0 < p.2 := lt_of_lt_of_le (ht e) hp.2
    exact False.elim (P.horn_pos_notMem_core c e p.1 hpos (hpx.symm ▸ hx))
  · obtain ⟨e', q, hq, hqx⟩ := mem_iUnion.mp hx
    have he : e' = e := by
      by_contra hne
      exact Set.disjoint_left.mp (P.horn_range_disjoint c e' e hne)
        ⟨⟨q, hq.2.1⟩, hqx⟩ ⟨⟨p, (ht e).le.trans hp.2⟩, hpx⟩
    subst e'
    have hqp : q = p := P.horn_injOn c e ⟨hq.1, hq.2.1⟩
      ⟨hp.1, (ht e).le.trans hp.2⟩ (hqx.trans hpx.symm)
    have htq : p.2 = t e := le_antisymm (hqp ▸ hq.2.2) hp.2
    refine ⟨p.1, ?_⟩
    simpa only [← htq] using hpx

theorem truncatedCore_frontier_subset_slices
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (t : P.hornIndex c → ℝ) (ht : ∀ e, 0 < t e) :
    frontier (P.truncatedCore c t) ⊆
      ⋃ e, range (fun y : Sphere 2 => P.horn c e (y, t e)) := by
  let : Finite (P.hornIndex c) := P.hornIndex_finite c
  let : LocallyPathConnectedSpace D.slab.terminalRegularOpen :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
  have hopen : IsOpen {x : D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} :=
    (isOpen_discrete ({c} : Set (ConnectedComponents D.slab.terminalRegularOpen))).preimage
      ConnectedComponents.continuous_coe
  have hclosed : IsClosed (⋃ e, P.hornTail c e (t e)) :=
    isClosed_iUnion_of_finite fun e => P.hornTail_isClosed c e (t e) (ht e).le
  intro x hx
  have hxK := (P.truncatedCore_isCompact c hc t).isClosed.frontier_subset hx
  have hxc := P.truncatedCore_subset_component c hc t hxK
  by_contra hxS
  have hxT : x ∉ ⋃ e, P.hornTail c e (t e) := by
    intro hxT
    obtain ⟨e, he⟩ := mem_iUnion.mp hxT
    exact hxS (mem_iUnion.mpr ⟨e, P.truncatedCore_inter_tail_subset_slice c t ht e ⟨hxK, he⟩⟩)
  have hsub : {x : D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} ∩
      (⋃ e, P.hornTail c e (t e))ᶜ ⊆ P.truncatedCore c t := by
    rintro y ⟨hyc, hyT⟩
    exact (P.component_subset_truncatedCore_union_tails c hc t hyc).resolve_right hyT
  exact hx.2 (mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset ((hopen.inter hclosed.isOpen_compl).mem_nhds ⟨hxc, hxT⟩) hsub))

end TerminalCorePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

def truncatedRegion (t : ∀ c, P.hornIndex c → ℝ) : Set D.slab.terminalRegularOpen :=
  ⋃ c ∈ P.component, P.truncatedCore c (t c)

theorem truncatedRegion_isCompact (t : ∀ c, P.hornIndex c → ℝ) :
    IsCompact (P.truncatedRegion t) :=
  P.component_finite.isCompact_biUnion (fun c hc => P.truncatedCore_isCompact c hc (t c))

theorem truncatedRegion_frontier_subset_slices (t : ∀ c, P.hornIndex c → ℝ)
    (ht : ∀ c e, 0 < t c e) :
    frontier (P.truncatedRegion t) ⊆
      ⋃ c ∈ P.component, ⋃ e, range (fun y : Sphere 2 => P.horn c e (y, t c e)) := by
  intro x hx
  have hxK := (P.truncatedRegion_isCompact t).isClosed.frontier_subset hx
  obtain ⟨c, hc, hxC⟩ := mem_iUnion₂.mp hxK
  have hxF : x ∈ frontier (P.truncatedCore c (t c)) := by
    refine ⟨subset_closure hxC, ?_⟩
    intro hxc
    have hsub : P.truncatedCore c (t c) ⊆ P.truncatedRegion t :=
      fun y hy => mem_iUnion₂.mpr ⟨c, hc, hy⟩
    exact hx.2 (interior_mono hsub hxc)
  exact mem_iUnion₂.mpr ⟨c, hc, P.truncatedCore_frontier_subset_slices c hc (t c) (ht c) hxF⟩

theorem low_subset_truncatedRegion (t : ∀ c, P.hornIndex c → ℝ) :
    {x : D.slab.terminalRegularOpen | metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹} ⊆
      P.truncatedRegion t := by
  intro x hx
  have hc : ConnectedComponents.mk x ∈ P.component :=
    (P.component_iff_meets_low _).mpr ⟨x, rfl, hx⟩
  exact mem_iUnion₂.mpr ⟨ConnectedComponents.mk x, hc,
    Or.inl (interior_subset (P.low_mem_interior_core _ hc x rfl hx))⟩

theorem ambient_truncatedRegion_frontier_subset_slices
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e) :
    frontier ((Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.truncatedRegion t) ⊆
      ⋃ c ∈ P.component, ⋃ e, range (fun y : Sphere 2 => (P.horn c e (y, t c e)).val) := by
  erw [← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
    D.slab.terminalRegularOpen.isOpen.isOpenEmbedding_subtypeVal (P.truncatedRegion_isCompact t)]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨c, hc, e, z, hz⟩ := by
    simpa only [mem_iUnion, mem_range] using P.truncatedRegion_frontier_subset_slices t ht hy
  exact mem_iUnion₂.mpr ⟨c, hc, mem_iUnion.mpr ⟨e, z, congrArg Subtype.val hz⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end
