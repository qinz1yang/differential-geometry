import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalRegionSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel

noncomputable section
open Set Manifold
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

private theorem exists_initialTerminalRegion_of_component_regions
    (D : OneStepIncoming.{u}) {ε r δ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hr : 0 < r) (hradius : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hnoncompact : ∀ y : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric y ≤ (r ^ 2)⁻¹ →
      ¬ IsCompact (connectedComponent y) →
      ∃ B : ℝ, (r ^ 2)⁻¹ < B ∧ ∃ S : SmoothSphericalRegion D.stage,
        ∃ (F : TerminalNeckFrontier D S ε)
          (v : S.Boundary → D.slab.terminalRegularOpen)
          (neck : ∀ b, SpatialNeck D.terminal.metric δ (v b)),
          (∀ b, F.chart b = (neck b).cylindricalChart ∧ |F.level b| ≤ 3) ∧
        S.region ⊆ Subtype.val '' connectedComponent y ∧
        (∀ x : D.slab.terminalRegularOpen, x ∈ connectedComponent y →
          metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹ → x.val ∈ interior S.region) ∧
        ∀ x : D.slab.terminalRegularOpen, x.val ∈ S.region →
          metricScalarAt D.terminal.metric x ≤ B) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ (R : InitialTerminalRegion D ε Λ)
      (v : ∀ c : {c // c ∈ R.component}, (R.core c).Boundary → D.slab.terminalRegularOpen)
      (neck : ∀ c b, SpatialNeck D.terminal.metric δ (v c b)),
      ∀ c b, (R.neckFrontier c).chart b = (neck c b).cylindricalChart ∧
        |(R.neckFrontier c).level b| ≤ 3 := by
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
        ∃ (F : TerminalNeckFrontier D S ε)
          (v : S.Boundary → D.slab.terminalRegularOpen)
          (neck : ∀ b, SpatialNeck D.terminal.metric δ (v b)),
          (∀ b, F.chart b = (neck b).cylindricalChart ∧ |F.level b| ≤ 3) ∧
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
      refine ⟨S, ht, 1, le_rfl, ?_, ?_, hneck, (fun b => isEmptyElim b),
        (fun b => isEmptyElim b), (fun b => isEmptyElim b), (fun b => isEmptyElim b)⟩
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
    · obtain ⟨B, hB, S, F, v, neck, hpreserved, hregion, hlow, hscalar⟩ :=
        hnoncompact (rep c) (hrep_low c) hc
      have ht : S.region ⊆ D.slab.terminalRegularRegion := by
        rintro x hx
        obtain ⟨y, hy, rfl⟩ := hregion hx
        exact y.property
      refine ⟨S, ht, max 1 (B * r ^ 2), le_max_left _ _, ?_, ?_, F, v, neck,
        hpreserved, ?_⟩
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
  choose core hcore_terminal bound hbound_ge_one hcore_component hlow_mem_interior
    neckFrontier point neck hpreserved hbound using hcore
  obtain ⟨Λ, hΛ, hΛbound⟩ := exists_one_le_forall_le_of_finite bound hbound_ge_one
  refine ⟨Λ, hΛ, {
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
    neckFrontier := neckFrontier
    boundary_scalar := ?_ }, point, neck, hpreserved⟩
  intro c b z
  exact (hbound c b z).trans
    (mul_le_mul_of_nonneg_right (hΛbound c) (inv_nonneg.mpr (sq_nonneg r)))

theorem exists_initialTerminalRegion_with_spatial_necks (D : OneStepIncoming.{u}) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ δ Λ : ℝ, 0 < δ ∧ δ < ε ∧ 1 ≤ Λ ∧ ∃ (R : InitialTerminalRegion D ε Λ)
      (v : ∀ c : {c // c ∈ R.component}, (R.core c).Boundary → D.slab.terminalRegularOpen)
      (neck : ∀ c b, SpatialNeck D.terminal.metric δ (v c b)),
      ∀ c b, (R.neckFrontier c).chart b = (neck c b).cylindricalChart ∧
        |(R.neckFrontier c).level b| ≤ 3 := by
  have ht : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  let r := D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  have hr : 0 < r :=
    mul_pos (D.parameters.delta_pos _ ht) (D.parameters.neckRadius_pos _ ht)
  obtain ⟨δ, hδ, hδε, hregion⟩ :=
    exists_smoothSphericalRegion_covering_scalar_sublevel_with_spatial_necks D hε
  obtain ⟨Λ, hΛ, R, v, neck, hpreserved⟩ :=
    exists_initialTerminalRegion_of_component_regions D hε hε1 hr rfl
      (hregion ((r ^ 2)⁻¹) (inv_pos.mpr (pow_pos hr 2)))
  exact ⟨δ, Λ, hδ, hδε, hΛ, R, v, neck, hpreserved⟩

theorem exists_initialTerminalRegion (D : OneStepIncoming.{u}) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ Nonempty (InitialTerminalRegion D ε Λ) := by
  obtain ⟨_, Λ, _, _, hΛ, R, _⟩ := exists_initialTerminalRegion_with_spatial_necks D hε hε1
  exact ⟨Λ, hΛ, ⟨R⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
