import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialTerminalRegionCompletion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

theorem exists_initialTerminalRegion_with_empty_boundary_of_compact_low_components
    (D : OneStepIncoming.{u}) {ε Λ r : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hΛ : 1 ≤ Λ)
    (hr : 0 < r) (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hcompact : ∀ c : ConnectedComponents D.slab.terminalRegularOpen,
      ∀ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c → metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ →
        IsCompact (connectedComponent x)) :
    ∃ R : InitialTerminalRegion D ε Λ,
      ∀ c : {c // c ∈ R.component}, IsEmpty (R.core c).Boundary := by
  classical
  let component : Set (ConnectedComponents D.slab.terminalRegularOpen) :=
    {c | ∃ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c ∧ metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹}
  have hcomponent_finite : component.Finite := by
    exact D.terminal.finite_components_meeting_scalar_sublevel ((r ^ 2)⁻¹)
  have hrep (c : {c // c ∈ component}) :
      ∃ x : D.slab.terminalRegularOpen,
        ConnectedComponents.mk x = c.1 ∧ metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ := c.2
  let rep : ∀ c : {c // c ∈ component}, D.slab.terminalRegularOpen :=
    fun c => Classical.choose (hrep c)
  have hrep_spec (c : {c // c ∈ component}) :
      ConnectedComponents.mk (rep c) = c.1 ∧
        metricScalarAt D.terminal.metric (rep c) ≤ (r ^ 2)⁻¹ :=
    Classical.choose_spec (hrep c)
  have hcore (c : {c // c ∈ component}) :
      ∃ S : SmoothSphericalRegion D.stage,
        S.region = Subtype.val '' connectedComponent (rep c) ∧ IsEmpty S.Boundary ∧
        S.interiorImage = Subtype.val '' connectedComponent (rep c) ∧
        ∀ x : D.slab.terminalRegularOpen,
          ConnectedComponents.mk x = ConnectedComponents.mk (rep c) →
            x.val ∈ interior S.region := by
    obtain ⟨S, hregion, hboundary, hinterior⟩ :=
      exists_smoothSphericalRegion_of_isCompact_connectedComponent (rep c)
        (hcompact c.1 (rep c) (hrep_spec c).1 (hrep_spec c).2)
    refine ⟨S, hregion, hboundary, hinterior, ?_⟩
    intro x hx
    apply SmoothSphericalRegion.interiorImage_subset_interior S
    rw [hinterior]
    exact ⟨x, ConnectedComponents.coe_eq_coe'.mp hx, rfl⟩
  let core : {c // c ∈ component} → SmoothSphericalRegion D.stage :=
    fun c => Classical.choose (hcore c)
  have hcore_spec (c : {c // c ∈ component}) :
      (core c).region = Subtype.val '' connectedComponent (rep c) ∧
      IsEmpty (core c).Boundary ∧
      (core c).interiorImage = Subtype.val '' connectedComponent (rep c) ∧
      ∀ x : D.slab.terminalRegularOpen,
        ConnectedComponents.mk x = ConnectedComponents.mk (rep c) →
          x.val ∈ interior (core c).region :=
    Classical.choose_spec (hcore c)
  have hcore_terminal : ∀ c, (core c).region ⊆ D.slab.terminalRegularRegion := by
    intro c x hx
    rw [hcore_spec c |>.1] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hcore_component : ∀ c (x : (core c).region),
      ConnectedComponents.mk (⟨x.1, hcore_terminal c x.2⟩ : D.slab.terminalRegularOpen) = c.1 := by
    intro c x
    have hximage : x.1 ∈ Subtype.val '' connectedComponent (rep c) :=
      (hcore_spec c).1 ▸ x.2
    obtain ⟨y, hy, hxy⟩ := hximage
    have hyid : ConnectedComponents.mk y = ConnectedComponents.mk (rep c) :=
      ConnectedComponents.coe_eq_coe'.mpr hy
    have hxy' : (⟨x.1, hcore_terminal c x.2⟩ : D.slab.terminalRegularOpen) = y := by
      apply Subtype.ext
      exact hxy.symm
    rw [hxy']
    exact hyid.trans (hrep_spec c).1
  have hlow_mem_interior : ∀ c (x : D.slab.terminalRegularOpen),
      ConnectedComponents.mk x = c.1 → metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ →
        x.1 ∈ interior (core c).region := by
    intro c x hxid hlow
    exact (hcore_spec c).2.2.2 x (hxid.trans (hrep_spec c).1.symm)
  have hneck : ∀ c, TerminalNeckFrontier D (core c) ε := by
    intro c
    let _ : IsEmpty (core c).Boundary := (hcore_spec c).2.1
    refine {
      chart := fun b => isEmptyElim b
      level := fun b => isEmptyElim b
      level_mem := fun b => isEmptyElim b
      chart_domain := fun b y t ht => isEmptyElim b
      boundary_eq := fun b y hy => isEmptyElim b
      metric_close := ?_
      collar := fun b => isEmptyElim b
      collarSign := fun b => isEmptyElim b
      collar_sign_unit := fun b => isEmptyElim b
      collar_chart := fun b => isEmptyElim b
      collar_region := fun b => isEmptyElim b }
    exact ⟨ε / 2, by linarith, fun b => isEmptyElim b⟩
  refine ⟨{
    epsilon_pos := hε
    epsilon_lt_one := hε1
    Lambda_ge_one := hΛ
    coreRadius := r
    coreRadius_pos := hr
    coreRadius_eq := hradius
    component := component
    component_finite := hcomponent_finite
    component_iff_meets_low := by intro c; rfl
    core := core
    core_terminal := hcore_terminal
    core_component := hcore_component
    low_mem_interior := hlow_mem_interior
    neckFrontier := hneck
    boundary_scalar := ?_ }, ?_⟩
  · intro c b y
    let _ : IsEmpty (core c).Boundary := (hcore_spec c).2.1
    exact isEmptyElim b
  · intro c
    exact (hcore_spec c).2.1

theorem exists_initialTerminalRegion_of_compact_low_components
    (D : OneStepIncoming.{u}) {ε Λ r : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hΛ : 1 ≤ Λ)
    (hr : 0 < r) (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hcompact : ∀ c : ConnectedComponents D.slab.terminalRegularOpen,
      ∀ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c → metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ →
        IsCompact (connectedComponent x)) :
    Nonempty (InitialTerminalRegion D ε Λ) := by
  obtain ⟨R, _⟩ := exists_initialTerminalRegion_with_empty_boundary_of_compact_low_components
    D hε hε1 hΛ hr hradius hcompact
  exact ⟨R⟩

theorem exists_terminalCorePresentation_of_compact_low_components
    (D : OneStepIncoming.{u}) {ε Λ r : ℝ}
    (hε : 0 < ε) (hΛ : 1 ≤ Λ)
    (hr : 0 < r) (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hcompact : ∀ c : ConnectedComponents D.slab.terminalRegularOpen,
      ∀ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c → metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ →
        IsCompact (connectedComponent x)) :
    ∃ P : TerminalCorePresentation D ε Λ, ∀ c, IsEmpty (P.hornIndex c) := by
  obtain ⟨R, hboundary⟩ := exists_initialTerminalRegion_with_empty_boundary_of_compact_low_components
    D (ε := min ε (1 / 2)) (lt_min hε (by norm_num))
      ((min_le_right ε (1 / 2)).trans_lt (by norm_num)) hΛ hr hradius hcompact
  obtain ⟨P, _, _, _, hhorns⟩ := R.exists_terminalCorePresentation_of_isEmpty_boundary hboundary
  exact ⟨P.monoEpsilon (min_le_left _ _), hhorns⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
