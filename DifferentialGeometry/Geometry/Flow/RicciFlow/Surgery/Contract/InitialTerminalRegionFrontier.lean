import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialSphericalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExteriorRegion
import DifferentialGeometry.Geometry.Neck.Chart

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure TerminalNeckFrontier (D : OneStepIncoming.{u})
    (W : SmoothSphericalRegion D.stage) (ε : ℝ) where
  chart : W.Boundary → DifferentialGeometry.Geometry.Neck.cylindricalChart
    ThreeModel (M := D.slab.terminalRegularOpen)
  level : W.Boundary → ℝ
  level_mem : ∀ b, level b ∈ Icc (-4 : ℝ) 4
  chart_domain : ∀ b (y : Sphere 2) t, t ∈ Icc (-101 : ℝ) 101 →
    (y, t) ∈ (chart b).domain
  boundary_eq : ∀ b (y : Sphere 2), ∀ hy : (y, level b) ∈ (chart b).domain,
    ((chart b).chart ⟨(y, level b), hy⟩ : D.slab.terminalRegularOpen).1 = (W.sphere b y).1
  metric_close : ∃ η : ℝ, η < ε ∧ ∀ b,
    (chart b).metricCloseOn D.terminal.metric η
      {z : (chart b).domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101}
  collar : ∀ b, DifferentialGeometry.Topology.SmoothTwoSidedCollar
    (𝓡 2) ThreeModel (fun y : Sphere 2 => (W.sphere b y).1)
  collarSign : W.Boundary → ℝ
  collar_sign_unit : ∀ b, collarSign b = 1 ∨ collarSign b = -1
  collar_chart : ∀ b (p : Sphere 2 ×
      DifferentialGeometry.Topology.symmetricOpenInterval (collar b).radius),
    ∃ hp : (p.1, level b + collarSign b * (p.2 : ℝ)) ∈ (chart b).domain,
      (collar b).toFun p =
        ((chart b).chart ⟨(p.1, level b + collarSign b * (p.2 : ℝ)), hp⟩ :
          D.slab.terminalRegularOpen).1
  collar_region : ∀ b (p : Sphere 2 ×
      DifferentialGeometry.Topology.symmetricOpenInterval (collar b).radius),
    (collar b).toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0

structure InitialTerminalRegion (D : OneStepIncoming.{u}) (ε Λ : ℝ) where
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  Lambda_ge_one : 1 ≤ Λ
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_eq : coreRadius = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  component : Set (ConnectedComponents D.slab.terminalRegularOpen)
  component_finite : component.Finite
  component_iff_meets_low : ∀ c : ConnectedComponents D.slab.terminalRegularOpen,
    c ∈ component ↔ ∃ x : D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c ∧ metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹
  core : {c // c ∈ component} → SmoothSphericalRegion D.stage
  core_terminal : ∀ c, (core c).region ⊆ D.slab.terminalRegularRegion
  core_component : ∀ c (x : (core c).region),
    ConnectedComponents.mk (⟨x.1, core_terminal c x.2⟩ : D.slab.terminalRegularOpen) = c.1
  low_mem_interior : ∀ c (x : D.slab.terminalRegularOpen),
    ConnectedComponents.mk x = c.1 → metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹ →
      x.1 ∈ interior (core c).region
  neckFrontier : ∀ c, TerminalNeckFrontier D (core c) ε
  boundary_scalar : ∀ c (b : (core c).Boundary) (y : Sphere 2),
    metricScalarAt D.terminal.metric
      ⟨((core c).sphere b y).1, core_terminal c ((core c).sphere b y).2⟩ ≤
        Λ * (coreRadius ^ 2)⁻¹


namespace TerminalNeckFrontier

variable {D : OneStepIncoming.{u}} {W : SmoothSphericalRegion D.stage} {ε ε' : ℝ}

def monoEpsilon (F : TerminalNeckFrontier D W ε) (hε : ε ≤ ε') :
    TerminalNeckFrontier D W ε' where
  chart := F.chart
  level := F.level
  level_mem := F.level_mem
  chart_domain := F.chart_domain
  boundary_eq := F.boundary_eq
  metric_close := by
    obtain ⟨η, hη, hc⟩ := F.metric_close
    exact ⟨η, hη.trans_le hε, hc⟩
  collar := F.collar
  collarSign := F.collarSign
  collar_sign_unit := F.collar_sign_unit
  collar_chart := F.collar_chart
  collar_region := F.collar_region

end TerminalNeckFrontier

namespace InitialTerminalRegion

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (R : InitialTerminalRegion D ε Λ)

theorem lowComponents_finite :
    {c : ConnectedComponents D.slab.terminalRegularOpen |
      ∃ x : D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹}.Finite :=
  R.component_finite.subset fun _ hc => (R.component_iff_meets_low _).mpr hc

theorem core_pairwise_disjoint : Pairwise (fun c d => Disjoint (R.core c).region (R.core d).region) := by
  intro c d hne
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  have hc := R.core_component c ⟨x, hxc⟩
  have hd := R.core_component d ⟨x, hxd⟩
  exact hne (Subtype.ext (hc.symm.trans hd))

def region : Set D.stage.Carrier := ⋃ c : {c // c ∈ R.component}, (R.core c).region

theorem region_isCompact : IsCompact R.region := by
  let : Finite {c // c ∈ R.component} := R.component_finite.to_subtype
  exact isCompact_iUnion (fun c => (R.core c).compact)

theorem region_terminal : R.region ⊆ D.slab.terminalRegularRegion := by
  rintro x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
  exact R.core_terminal c hc

theorem low_mem_interior_region (x : D.slab.terminalRegularOpen)
    (hx : metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) :
    x.1 ∈ interior R.region := by
  have hc : ConnectedComponents.mk x ∈ R.component :=
    (R.component_iff_meets_low _).mpr ⟨x, rfl, hx⟩
  exact interior_mono (Set.subset_iUnion (fun c : {c // c ∈ R.component} => (R.core c).region)
    ⟨ConnectedComponents.mk x, hc⟩) (R.low_mem_interior _ x rfl hx)

theorem scalar_gt_on_core_frontier (c : {c // c ∈ R.component})
    (x : D.slab.terminalRegularOpen) (hx : x.1 ∈ frontier (R.core c).region) :
    (R.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x := by
  apply lt_of_not_ge
  intro hscalar
  have hxcore : x.1 ∈ (R.core c).region := (R.core c).compact.isClosed.frontier_subset hx
  have hcomp : ConnectedComponents.mk x = c.1 := R.core_component c ⟨x.1, hxcore⟩
  exact hx.2 (R.low_mem_interior c x hcomp hscalar)



theorem low_mem_component {x : D.slab.terminalRegularOpen}
    (hx : metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) :
    ConnectedComponents.mk x ∈ R.component :=
  (R.component_iff_meets_low _).mpr ⟨x, rfl, hx⟩

theorem lowSet_subset_region :
    Subtype.val '' {x : D.slab.terminalRegularOpen |
      metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹} ⊆ R.region := by
  rintro y ⟨x, hx, rfl⟩
  exact interior_subset (R.low_mem_interior_region x hx)

theorem region_nonempty_of_low
    (h : ∃ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) : R.region.Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x.1, R.lowSet_subset_region ⟨x, hx, rfl⟩⟩

theorem component_eq_empty_iff_forall_high :
    R.component = ∅ ↔ ∀ x : D.slab.terminalRegularOpen,
      (R.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x := by
  constructor
  · intro h x
    apply lt_of_not_ge
    intro hx
    have hm := R.low_mem_component hx
    rw [h] at hm
    exact hm
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨x, _, hx⟩ := (R.component_iff_meets_low c).mp hc
    exact (not_lt_of_ge hx) (h x)

def monoLambda {Λ' : ℝ} (hΛ : Λ ≤ Λ') : InitialTerminalRegion D ε Λ' where
  epsilon_pos := R.epsilon_pos
  epsilon_lt_one := R.epsilon_lt_one
  Lambda_ge_one := R.Lambda_ge_one.trans hΛ
  coreRadius := R.coreRadius
  coreRadius_pos := R.coreRadius_pos
  coreRadius_eq := R.coreRadius_eq
  component := R.component
  component_finite := R.component_finite
  component_iff_meets_low := R.component_iff_meets_low
  core := R.core
  core_terminal := R.core_terminal
  core_component := R.core_component
  low_mem_interior := R.low_mem_interior
  neckFrontier := R.neckFrontier
  boundary_scalar := fun c b y => (R.boundary_scalar c b y).trans
    (mul_le_mul_of_nonneg_right hΛ (inv_nonneg.mpr (sq_nonneg _)))

def monoEpsilon {ε' : ℝ} (hε : ε ≤ ε') (hε' : ε' < 1) :
    InitialTerminalRegion D ε' Λ where
  epsilon_pos := R.epsilon_pos.trans_le hε
  epsilon_lt_one := hε'
  Lambda_ge_one := R.Lambda_ge_one
  coreRadius := R.coreRadius
  coreRadius_pos := R.coreRadius_pos
  coreRadius_eq := R.coreRadius_eq
  component := R.component
  component_finite := R.component_finite
  component_iff_meets_low := R.component_iff_meets_low
  core := R.core
  core_terminal := R.core_terminal
  core_component := R.core_component
  low_mem_interior := R.low_mem_interior
  neckFrontier := fun c => (R.neckFrontier c).monoEpsilon hε
  boundary_scalar := R.boundary_scalar

end InitialTerminalRegion
theorem two_le_floor_inv_add_one {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    2 ≤ ⌊ε⁻¹⌋₊ + 1 := by
  have h1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε'.le
  have h2 : (1 : ℕ) ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  omega

theorem inv_sq_pos_of_pos {r : ℝ} (hr : 0 < r) : 0 < (r ^ 2)⁻¹ :=
  inv_pos.mpr (pow_pos hr 2)

theorem inv_sq_le_mul_inv_sq {Λ r : ℝ} (hΛ : 1 ≤ Λ) :
    (r ^ 2)⁻¹ ≤ Λ * (r ^ 2)⁻¹ := by
  have h : (1 : ℝ) * (r ^ 2)⁻¹ ≤ Λ * (r ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hΛ (inv_nonneg.mpr (sq_nonneg r))
  simpa using h


structure HasInitialTerminalRegion (τ : ℝ) where
  tau_pos : 0 < τ
  epsilon : ℝ
  Lambda : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_one : epsilon < 1
  one_le_Lambda : 1 ≤ Lambda
  region : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
    Nonempty (InitialTerminalRegion D epsilon Lambda)

structure TerminalRegionCompletion (ε Λ : ℝ) : Prop where
  complete : ∀ D : OneStepIncoming.{u}, Nonempty (InitialTerminalRegion D ε Λ) →
    Nonempty (TerminalCorePresentation D ε Λ)

def HasInitialTerminalRegion.monoTau {τ τ' : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    (hτ : τ ≤ τ') : HasInitialTerminalRegion.{u} τ' where
  tau_pos := lt_of_lt_of_le h.tau_pos hτ
  epsilon := h.epsilon
  Lambda := h.Lambda
  epsilon_pos := h.epsilon_pos
  epsilon_lt_one := h.epsilon_lt_one
  one_le_Lambda := h.one_le_Lambda
  region := fun D hD => h.region D (le_trans hτ hD)

def HasInitialTerminalRegion.monoLambda {τ : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    {Λ' : ℝ} (hΛ : h.Lambda ≤ Λ') (hΛ' : 1 ≤ Λ') : HasInitialTerminalRegion.{u} τ where
  tau_pos := h.tau_pos
  epsilon := h.epsilon
  Lambda := Λ'
  epsilon_pos := h.epsilon_pos
  epsilon_lt_one := h.epsilon_lt_one
  one_le_Lambda := hΛ'
  region := fun D hD => (h.region D hD).map fun R => R.monoLambda hΛ

def HasInitialTerminalRegion.monoEpsilon {τ : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    {ε' : ℝ} (hε : h.epsilon ≤ ε') (hε' : ε' < 1) : HasInitialTerminalRegion.{u} τ where
  tau_pos := h.tau_pos
  epsilon := ε'
  Lambda := h.Lambda
  epsilon_pos := lt_of_lt_of_le h.epsilon_pos hε
  epsilon_lt_one := hε'
  one_le_Lambda := h.one_le_Lambda
  region := fun D hD => (h.region D hD).map fun R => R.monoEpsilon hε hε'

structure InitialSphericalFrontierReduction where
  tau : ℝ
  tau_pos : 0 < tau
  barrier : HasInitialTerminalRegion.{u} tau
  completion : TerminalRegionCompletion.{u} barrier.epsilon barrier.Lambda

theorem terminalRegionCompletion_of_forall_presentation {ε Λ : ℝ}
    (h : ∀ D : OneStepIncoming.{u}, Nonempty (TerminalCorePresentation D ε Λ)) :
    TerminalRegionCompletion.{u} ε Λ :=
  ⟨fun D _ => h D⟩

def InitialSphericalFrontierReduction.ofRegionAndPresentation {τ : ℝ}
    (h : HasInitialTerminalRegion.{u} τ)
    (hp : ∀ D : OneStepIncoming.{u}, Nonempty (TerminalCorePresentation D h.epsilon h.Lambda)) :
    InitialSphericalFrontierReduction.{u} where
  tau := τ
  tau_pos := h.tau_pos
  barrier := h
  completion := terminalRegionCompletion_of_forall_presentation hp

theorem exists_terminalRegion_of_hasInitialTerminalRegion {τ : ℝ}
    (h : HasInitialTerminalRegion.{u} τ) (D : OneStepIncoming.{u}) (hD : τ ≤ D.endTime) :
    Nonempty (InitialTerminalRegion D h.epsilon h.Lambda) :=
  h.region D hD

theorem hasInitialSphericalFrontier_of_hasInitialTerminalRegion {τ : ℝ}
    (h : HasInitialTerminalRegion.{u} τ)
    (hc : TerminalRegionCompletion.{u} h.epsilon h.Lambda) :
    HasInitialSphericalFrontier.{u} τ :=
  ⟨h.epsilon, h.Lambda, h.epsilon_pos, h.epsilon_lt_one, h.one_le_Lambda,
    fun D hD => hc.complete D (h.region D hD)⟩

theorem exists_hasInitialSphericalFrontier_of_reduction
    (h : InitialSphericalFrontierReduction.{u}) :
    ∃ τ : ℝ, 0 < τ ∧ HasInitialSphericalFrontier.{u} τ :=
  ⟨h.tau, h.tau_pos,
    hasInitialSphericalFrontier_of_hasInitialTerminalRegion h.barrier h.completion⟩

theorem exists_terminalCorePresentationInput_of_reduction
    (h : InitialSphericalFrontierReduction.{u}) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε < 1 ∧
      Nonempty (TerminalCorePresentationInput.{u} τ ε) := by
  obtain ⟨τ, hτ, hS⟩ := exists_hasInitialSphericalFrontier_of_reduction h
  exact hasInitialSphericalFrontier_iff_exists_terminalCorePresentationInput.mp ⟨τ, hτ, hS⟩

theorem exists_one_le_forall_le_of_finite {ι : Type u} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 1 ≤ f i) : ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ i, f i ≤ Λ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, le_rfl, fun i => (hι.false i).elim⟩
  · have : Fintype ι := Fintype.ofFinite ι
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    exact ⟨f j, hf j, fun i => hj i (Finset.mem_univ i)⟩

theorem exists_pos_forall_le_of_finite {ι : Type u} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · have : Fintype ι := Fintype.ofFinite ι
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f j, hf j, fun i => hj i (Finset.mem_univ i)⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
