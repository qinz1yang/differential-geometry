import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Terminal.CorePresentation.Defs

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem core_subset_component (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (hc : c ∈ P.component) :
    P.core c ⊆ {x | ConnectedComponents.mk x = c} := by
  intro x hx
  have h : x ∈ P.core c ∪ ⋃ e : P.hornIndex c,
      Set.range fun p : HalfNeckCylinder => P.horn c e p.1 := Or.inl hx
  rw [← P.horn_covers_component c hc] at h
  exact h

theorem horn_base_mem_core (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (y : Sphere 2) : P.horn c e (y, 0) ∈ P.core c := by
  have h : P.horn c e (y, 0) ∈
      (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) ∩ P.core c := by
    rw [P.horn_meets_core]
    exact ⟨y, rfl⟩
  exact h.2

theorem horn_pos_notMem_core (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (y : Sphere 2) {t : ℝ} (ht : 0 < t) :
    P.horn c e (y, t) ∉ P.core c := by
  intro hx
  have h : P.horn c e (y, t) ∈
      (Set.range fun p : HalfNeckCylinder => P.horn c e p.1) ∩ P.core c :=
    ⟨⟨⟨(y, t), ht.le⟩, rfl⟩, hx⟩
  rw [P.horn_meets_core] at h
  obtain ⟨z, hz⟩ := h
  have hzmem : (z, (0 : ℝ)) ∈ Set.univ ×ˢ Set.Ici (0 : ℝ) :=
    ⟨Set.mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
  have hymem : (y, t) ∈ Set.univ ×ˢ Set.Ici (0 : ℝ) := ⟨Set.mem_univ _, ht.le⟩
  have he := P.horn_injOn c e hzmem hymem hz
  exact (ne_of_gt ht) (congrArg Prod.snd he).symm

theorem frontier_scalar_le (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (hc : c ∈ P.component) {x : ↥D.slab.terminalRegularOpen}
    (hx : x ∈ frontier (P.core c)) :
    metricScalarAt D.terminal.metric x ≤ Λ * (P.coreRadius ^ 2)⁻¹ := by
  rw [P.horn_base_covers_boundary c hc] at hx
  obtain ⟨e, y, rfl⟩ := Set.mem_iUnion.mp hx
  exact P.horn_base_scalar c e y

theorem nonempty_hornIndex_of_not_isCompact_component
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (h : ¬ IsCompact {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c}) :
    Nonempty (P.hornIndex c) := by
  by_contra he
  let : IsEmpty (P.hornIndex c) := not_nonempty_iff.mp he
  apply h
  rw [P.horn_covers_component c hc, Set.iUnion_of_empty, Set.union_empty]
  exact P.core_isCompact c hc

end TerminalCorePresentation

variable {D : OneStepIncoming.{u}}

def TerminalCorePresentation.monoLambda {ε Λ Λ' : ℝ}
    (P : TerminalCorePresentation D ε Λ) (hΛ : Λ ≤ Λ') :
    TerminalCorePresentation D ε Λ' where
  epsilon_pos := P.epsilon_pos
  Lambda_ge_one := le_trans P.Lambda_ge_one hΛ
  coreRadius := P.coreRadius
  coreRadius_pos := P.coreRadius_pos
  coreRadius_eq := P.coreRadius_eq
  component := P.component
  component_finite := P.component_finite
  core := P.core
  core_isCompact := P.core_isCompact
  core_isConnected := P.core_isConnected
  core_empty := P.core_empty
  coreCharts := P.coreCharts
  core_smooth := P.core_smooth
  core_induced := P.core_induced
  core_interior_eq := P.core_interior_eq
  core_boundary_eq := P.core_boundary_eq
  component_iff_meets_low := P.component_iff_meets_low
  low_mem_interior_core := P.low_mem_interior_core
  hornIndex := P.hornIndex
  hornIndex_finite := P.hornIndex_finite
  hornIndex_empty := P.hornIndex_empty
  horn := P.horn
  horn_smooth := P.horn_smooth
  horn_interior_embedding := P.horn_interior_embedding
  horn_injOn := P.horn_injOn
  horn_proper := P.horn_proper
  horn_range_disjoint := P.horn_range_disjoint
  horn_meets_core := P.horn_meets_core
  horn_base_covers_boundary := P.horn_base_covers_boundary
  hornCollar := P.hornCollar
  horn_collar_core_side := P.horn_collar_core_side
  horn_collar_eq := P.horn_collar_eq
  horn_covers_component := P.horn_covers_component
  horn_scalar_large := P.horn_scalar_large
  horn_base_scalar := fun c e y =>
    (P.horn_base_scalar c e y).trans
      (mul_le_mul_of_nonneg_right hΛ (inv_nonneg.mpr (sq_nonneg P.coreRadius)))
  horn_scalar_diverges := P.horn_scalar_diverges
  horn_spatial_neck := P.horn_spatial_neck

def TerminalCorePresentation.monoEpsilon {ε ε' Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) (hε : ε ≤ ε') :
    TerminalCorePresentation D ε' Λ where
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  Lambda_ge_one := P.Lambda_ge_one
  coreRadius := P.coreRadius
  coreRadius_pos := P.coreRadius_pos
  coreRadius_eq := P.coreRadius_eq
  component := P.component
  component_finite := P.component_finite
  core := P.core
  core_isCompact := P.core_isCompact
  core_isConnected := P.core_isConnected
  core_empty := P.core_empty
  coreCharts := P.coreCharts
  core_smooth := P.core_smooth
  core_induced := P.core_induced
  core_interior_eq := P.core_interior_eq
  core_boundary_eq := P.core_boundary_eq
  component_iff_meets_low := P.component_iff_meets_low
  low_mem_interior_core := P.low_mem_interior_core
  hornIndex := P.hornIndex
  hornIndex_finite := P.hornIndex_finite
  hornIndex_empty := P.hornIndex_empty
  horn := P.horn
  horn_smooth := P.horn_smooth
  horn_interior_embedding := P.horn_interior_embedding
  horn_injOn := P.horn_injOn
  horn_proper := P.horn_proper
  horn_range_disjoint := P.horn_range_disjoint
  horn_meets_core := P.horn_meets_core
  horn_base_covers_boundary := P.horn_base_covers_boundary
  hornCollar := P.hornCollar
  horn_collar_core_side := P.horn_collar_core_side
  horn_collar_eq := P.horn_collar_eq
  horn_covers_component := P.horn_covers_component
  horn_scalar_large := P.horn_scalar_large
  horn_base_scalar := P.horn_base_scalar
  horn_scalar_diverges := P.horn_scalar_diverges
  horn_spatial_neck := fun c e x hx => by
    obtain ⟨δ, k, neck, hcenter, hδε, hk⟩ := P.horn_spatial_neck c e x hx
    exact ⟨δ, k, neck, hcenter, hδε.trans hε,
      le_trans (Nat.add_le_add_right
        (Nat.floor_mono (inv_anti₀ P.epsilon_pos hε)) 1) hk⟩

theorem TerminalCorePresentation.lowComponents_finite {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) :
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen |
      ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹}.Finite :=
  P.component_finite.subset fun _ hc => (P.component_iff_meets_low _).mpr hc

theorem TerminalCorePresentation.low_mem_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) {x : ↥D.slab.terminalRegularOpen}
    (hx : metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹) :
    ∃ c ∈ P.component, x ∈ P.core c := by
  have hc : ConnectedComponents.mk x ∈ P.component :=
    (P.component_iff_meets_low (ConnectedComponents.mk x)).mpr ⟨x, rfl, hx⟩
  exact ⟨_, hc, interior_subset (P.low_mem_interior_core _ hc x rfl hx)⟩

theorem TerminalCorePresentation.lowSet_subset_iUnion_core {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) :
    {x : ↥D.slab.terminalRegularOpen |
        metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹} ⊆
      ⋃ c ∈ P.component, P.core c := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := P.low_mem_core hx
  exact Set.mem_biUnion hc hxc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
