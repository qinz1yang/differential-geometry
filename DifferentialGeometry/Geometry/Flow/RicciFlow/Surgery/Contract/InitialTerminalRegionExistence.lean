import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalRegionSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

private theorem exists_initialTerminalRegion_of_component_regions
    (D : OneStepIncoming.{u}) {ε r : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hr : 0 < r) (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hnoncompact : ∀ y : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric y ≤ (r ^ 2)⁻¹ →
      ¬ IsCompact (connectedComponent y) →
      ∃ B : ℝ, (r ^ 2)⁻¹ < B ∧ ∃ S : SmoothSphericalRegion D.stage,
        Nonempty (TerminalNeckFrontier D S ε) ∧
        S.region ⊆ Subtype.val '' connectedComponent y ∧
        (∀ x : D.slab.terminalRegularOpen, x ∈ connectedComponent y →
          metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ → x.val ∈ interior S.region) ∧
        ∀ x : D.slab.terminalRegularOpen, x.val ∈ S.region →
          metricScalarAt D.terminal.metric x ≤ B) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ Nonempty (InitialTerminalRegion D ε Λ) := by
  classical
  let component : Set (ConnectedComponents D.slab.terminalRegularOpen) :=
    {c | ∃ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c ∧ metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹}
  have hcomponent_finite : component.Finite :=
    D.terminal.finite_components_meeting_scalar_sublevel ((r ^ 2)⁻¹)
  let _ : Finite {c // c ∈ component} := hcomponent_finite.to_subtype
  have hrep (c : {c // c ∈ component}) :
      ∃ x : D.slab.terminalRegularOpen,
        ConnectedComponents.mk x = c.1 ∧ metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ := c.2
  choose rep hrep_component hrep_low using hrep
  have hcore (c : {c // c ∈ component}) :
      ∃ (S : SmoothSphericalRegion D.stage)
        (ht : S.region ⊆ D.slab.terminalRegularRegion) (B : ℝ), 1 ≤ B ∧
        (∀ x : S.region,
          ConnectedComponents.mk (⟨x.1, ht x.2⟩ : D.slab.terminalRegularOpen) = c.1) ∧
        (∀ x : D.slab.terminalRegularOpen, ConnectedComponents.mk x = c.1 →
          metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ → x.val ∈ interior S.region) ∧
        Nonempty (TerminalNeckFrontier D S ε) ∧
        ∀ (b : S.Boundary) (z : Sphere 2),
          metricScalarAt D.terminal.metric ⟨(S.sphere b z).1, ht (S.sphere b z).2⟩ ≤
            B * (r ^ 2)⁻¹ := by
    by_cases hc : IsCompact (connectedComponent (rep c))
    · obtain ⟨S, hregion, hboundary, hinterior⟩ :=
        exists_smoothSphericalRegion_of_isCompact_connectedComponent (rep c) hc
      have ht : S.region ⊆ D.slab.terminalRegularRegion := by
        rintro x hx
        rw [hregion] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact y.property
      let _ : IsEmpty S.Boundary := hboundary
      have hneck : TerminalNeckFrontier D S ε := by
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
      refine ⟨S, ht, 1, le_rfl, ?_, ?_, ⟨hneck⟩, fun b => isEmptyElim b⟩
      · intro x
        have hximage : x.1 ∈ Subtype.val '' connectedComponent (rep c) := hregion ▸ x.2
        obtain ⟨y, hy, hxy⟩ := hximage
        have hxy' : (⟨x.1, ht x.2⟩ : D.slab.terminalRegularOpen) = y :=
          Subtype.ext hxy.symm
        rw [hxy']
        exact (ConnectedComponents.coe_eq_coe'.mpr hy).trans (hrep_component c)
      · intro x hx _
        apply SmoothSphericalRegion.interiorImage_subset_interior S
        rw [hinterior]
        exact ⟨x, ConnectedComponents.coe_eq_coe'.mp (hx.trans (hrep_component c).symm), rfl⟩
    · obtain ⟨B, hB, S, hneck, hregion, hlow, hscalar⟩ :=
        hnoncompact (rep c) (hrep_low c) hc
      have ht : S.region ⊆ D.slab.terminalRegularRegion := by
        rintro x hx
        obtain ⟨y, hy, rfl⟩ := hregion hx
        exact y.property
      refine ⟨S, ht, max 1 (B * r ^ 2), le_max_left _ _, ?_, ?_, hneck, ?_⟩
      · intro x
        obtain ⟨y, hy, hxy⟩ := hregion x.2
        have hxy' : (⟨x.1, ht x.2⟩ : D.slab.terminalRegularOpen) = y :=
          Subtype.ext hxy.symm
        rw [hxy']
        exact (ConnectedComponents.coe_eq_coe'.mpr hy).trans (hrep_component c)
      · intro x hx hxlow
        exact hlow x (ConnectedComponents.coe_eq_coe'.mp (hx.trans (hrep_component c).symm)) hxlow
      · intro b z
        apply (hscalar ⟨(S.sphere b z).1, ht (S.sphere b z).2⟩ (S.sphere b z).2).trans
        calc
          B = (B * r ^ 2) * (r ^ 2)⁻¹ := by field_simp
          _ ≤ max 1 (B * r ^ 2) * (r ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr (sq_nonneg r))
  choose core hcore_terminal bound hbound_ge_one hcore_component hlow_mem_interior hneck hbound using hcore
  obtain ⟨Λ, hΛ, hΛbound⟩ := exists_one_le_forall_le_of_finite bound hbound_ge_one
  refine ⟨Λ, hΛ, ⟨{
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
    neckFrontier := fun c => (hneck c).some
    boundary_scalar := ?_ }⟩⟩
  intro c b z
  exact (hbound c b z).trans
    (mul_le_mul_of_nonneg_right (hΛbound c) (inv_nonneg.mpr (sq_nonneg r)))

theorem exists_initialTerminalRegion (D : OneStepIncoming.{u}) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ Nonempty (InitialTerminalRegion D ε Λ) := by
  have ht : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  let r := D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  have hr : 0 < r :=
    mul_pos (D.parameters.delta_pos _ ht) (D.parameters.neckRadius_pos _ ht)
  apply exists_initialTerminalRegion_of_component_regions D hε hε1 hr rfl
  intro y hy hnoncompact
  exact exists_smoothSphericalRegion_covering_scalar_sublevel_noncompact D hε
    (inv_pos.mpr (pow_pos hr 2)) y hy hnoncompact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
