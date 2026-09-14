import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialSphericalFrontier

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure InitialTerminalRegion (D : OneStepIncoming.{u}) (ε Λ : ℝ) where
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  Lambda_ge_one : 1 ≤ Λ
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_eq : coreRadius =
    D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  component : Set (ConnectedComponents ↥D.slab.terminalRegularOpen)
  component_finite : component.Finite
  component_iff_meets_low : ∀ c : ConnectedComponents ↥D.slab.terminalRegularOpen,
    c ∈ component ↔ ∃ x : ↥D.slab.terminalRegularOpen,
      ConnectedComponents.mk x = c ∧ metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹
  region : Set ↥D.slab.terminalRegularOpen
  region_isOpen : IsOpen region
  region_isCompact : IsCompact region
  region_isPreconnected : IsPreconnected region
  low_mem_region : ∀ x : ↥D.slab.terminalRegularOpen,
    metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹ → x ∈ region
  region_mem_component : ∀ x ∈ region, ConnectedComponents.mk x ∈ component
  boundary_neck : ∀ x ∈ frontier region,
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k
  boundary_scalar : ∀ x ∈ frontier region,
    metricScalarAt D.terminal.metric x ≤ Λ * (coreRadius ^ 2)⁻¹
  high_scalar_outside : ∀ x : ↥D.slab.terminalRegularOpen,
    x ∉ closure region → (coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x

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

theorem InitialTerminalRegion.lowComponents_finite {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) :
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen |
      ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹}.Finite :=
  R.component_finite.subset fun _ hc => (R.component_iff_meets_low _).mpr hc

theorem InitialTerminalRegion.low_mem_component {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) {x : ↥D.slab.terminalRegularOpen}
    (hx : metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) :
    ConnectedComponents.mk x ∈ R.component :=
  (R.component_iff_meets_low _).mpr ⟨x, rfl, hx⟩

theorem InitialTerminalRegion.lowSet_subset_region {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) :
    {x : ↥D.slab.terminalRegularOpen |
      metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹} ⊆ R.region :=
  fun _ hx => R.low_mem_region _ hx

theorem InitialTerminalRegion.region_nonempty_of_low {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ)
    (h : ∃ x : ↥D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) :
    R.region.Nonempty :=
  h.elim fun x hx => ⟨x, R.low_mem_region x hx⟩

theorem InitialTerminalRegion.isConnected_region_of_low {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ)
    (h : ∃ x : ↥D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹) :
    IsConnected R.region :=
  ⟨R.region_nonempty_of_low h, R.region_isPreconnected⟩

theorem InitialTerminalRegion.disjoint_frontier_region {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) : Disjoint (frontier R.region) R.region :=
  disjoint_left.mpr fun x hx hxr => by
    simp only [frontier, Set.mem_sdiff] at hx
    exact hx.2 (by simpa [R.region_isOpen.interior_eq] using hxr)

theorem InitialTerminalRegion.frontier_nonempty_of_nontrivial {D : OneStepIncoming.{u}}
    {ε Λ : ℝ} [PreconnectedSpace ↥D.slab.terminalRegularOpen]
    (R : InitialTerminalRegion D ε Λ) (hne : R.region.Nonempty) (hproper : R.region ≠ univ) :
    (frontier R.region).Nonempty :=
  nonempty_frontier_iff.mpr ⟨hne, hproper⟩

theorem InitialTerminalRegion.exists_boundary_neck_of_mem_frontier {D : OneStepIncoming.{u}}
    {ε Λ : ℝ} (R : InitialTerminalRegion D ε Λ) {x : ↥D.slab.terminalRegularOpen}
    (hx : x ∈ frontier R.region) :
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k :=
  R.boundary_neck x hx

theorem InitialTerminalRegion.component_eq_univ_of_region_eq_univ {D : OneStepIncoming.{u}}
    {ε Λ : ℝ} (R : InitialTerminalRegion D ε Λ) (h : R.region = univ) :
    R.component = univ := by
  refine eq_univ_iff_forall.mpr fun c => ?_
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  rw [← hx]
  exact R.region_mem_component x (by rw [h]; exact mem_univ x)

theorem InitialTerminalRegion.component_eq_empty_iff_forall_high {D : OneStepIncoming.{u}}
    {ε Λ : ℝ} (R : InitialTerminalRegion D ε Λ) :
    R.component = ∅ ↔ ∀ x : ↥D.slab.terminalRegularOpen,
      (R.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric x := by
  constructor
  · intro h x
    by_contra hx
    have hlow : metricScalarAt D.terminal.metric x ≤ (R.coreRadius ^ 2)⁻¹ := le_of_not_gt hx
    have hmem : ConnectedComponents.mk x ∈ R.component := R.low_mem_component hlow
    rw [h] at hmem
    exact hmem
  · intro h
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨x, -, hxl⟩ := (R.component_iff_meets_low c).mp hc
    exact absurd (h x) (not_lt.mpr hxl)

theorem InitialTerminalRegion.two_le_boundary_index {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) {x : ↥D.slab.terminalRegularOpen}
    (hx : x ∈ frontier R.region) :
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ 2 ≤ k := by
  obtain ⟨δ, k, neck, hcenter, hδε, hk⟩ := R.boundary_neck x hx
  exact ⟨δ, k, neck, hcenter, hδε,
    le_trans (two_le_floor_inv_add_one R.epsilon_pos R.epsilon_lt_one) hk⟩

def InitialTerminalRegion.mono_lambda {D : OneStepIncoming.{u}} {ε Λ Λ' : ℝ}
    (R : InitialTerminalRegion D ε Λ) (hΛ : Λ ≤ Λ') (hΛ' : 1 ≤ Λ') :
    InitialTerminalRegion D ε Λ' where
  epsilon_pos := R.epsilon_pos
  epsilon_lt_one := R.epsilon_lt_one
  Lambda_ge_one := hΛ'
  coreRadius := R.coreRadius
  coreRadius_pos := R.coreRadius_pos
  coreRadius_eq := R.coreRadius_eq
  component := R.component
  component_finite := R.component_finite
  component_iff_meets_low := R.component_iff_meets_low
  region := R.region
  region_isOpen := R.region_isOpen
  region_isCompact := R.region_isCompact
  region_isPreconnected := R.region_isPreconnected
  low_mem_region := R.low_mem_region
  region_mem_component := R.region_mem_component
  boundary_neck := R.boundary_neck
  boundary_scalar := fun x hx =>
    (R.boundary_scalar x hx).trans
      (mul_le_mul_of_nonneg_right hΛ (inv_nonneg.mpr (sq_nonneg R.coreRadius)))
  high_scalar_outside := R.high_scalar_outside

def InitialTerminalRegion.mono_epsilon {D : OneStepIncoming.{u}} {ε ε' Λ : ℝ}
    (R : InitialTerminalRegion D ε Λ) (hε : ε ≤ ε') (hε' : ε' < 1) :
    InitialTerminalRegion D ε' Λ where
  epsilon_pos := lt_of_lt_of_le R.epsilon_pos hε
  epsilon_lt_one := hε'
  Lambda_ge_one := R.Lambda_ge_one
  coreRadius := R.coreRadius
  coreRadius_pos := R.coreRadius_pos
  coreRadius_eq := R.coreRadius_eq
  component := R.component
  component_finite := R.component_finite
  component_iff_meets_low := R.component_iff_meets_low
  region := R.region
  region_isOpen := R.region_isOpen
  region_isCompact := R.region_isCompact
  region_isPreconnected := R.region_isPreconnected
  low_mem_region := R.low_mem_region
  region_mem_component := R.region_mem_component
  boundary_neck := fun x hx => by
    obtain ⟨δ, k, neck, hcenter, hδε, hk⟩ := R.boundary_neck x hx
    exact ⟨δ, k, neck, hcenter, hδε.trans hε,
      le_trans (Nat.add_le_add_right (Nat.floor_mono (inv_anti₀ R.epsilon_pos hε)) 1) hk⟩
  boundary_scalar := R.boundary_scalar
  high_scalar_outside := R.high_scalar_outside

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

def HasInitialTerminalRegion.mono_tau {τ τ' : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    (hτ : τ ≤ τ') : HasInitialTerminalRegion.{u} τ' where
  tau_pos := lt_of_lt_of_le h.tau_pos hτ
  epsilon := h.epsilon
  Lambda := h.Lambda
  epsilon_pos := h.epsilon_pos
  epsilon_lt_one := h.epsilon_lt_one
  one_le_Lambda := h.one_le_Lambda
  region := fun D hD => h.region D (le_trans hτ hD)

def HasInitialTerminalRegion.mono_lambda {τ : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    {Λ' : ℝ} (hΛ : h.Lambda ≤ Λ') (hΛ' : 1 ≤ Λ') : HasInitialTerminalRegion.{u} τ where
  tau_pos := h.tau_pos
  epsilon := h.epsilon
  Lambda := Λ'
  epsilon_pos := h.epsilon_pos
  epsilon_lt_one := h.epsilon_lt_one
  one_le_Lambda := hΛ'
  region := fun D hD => (h.region D hD).map fun R => R.mono_lambda hΛ hΛ'

def HasInitialTerminalRegion.mono_epsilon {τ : ℝ} (h : HasInitialTerminalRegion.{u} τ)
    {ε' : ℝ} (hε : h.epsilon ≤ ε') (hε' : ε' < 1) : HasInitialTerminalRegion.{u} τ where
  tau_pos := h.tau_pos
  epsilon := ε'
  Lambda := h.Lambda
  epsilon_pos := lt_of_lt_of_le h.epsilon_pos hε
  epsilon_lt_one := hε'
  one_le_Lambda := h.one_le_Lambda
  region := fun D hD => (h.region D hD).map fun R => R.mono_epsilon hε hε'

structure InitialSphericalFrontierReduction where
  tau : ℝ
  tau_pos : 0 < tau
  barrier : HasInitialTerminalRegion.{u} tau
  completion : TerminalRegionCompletion.{u} barrier.epsilon barrier.Lambda

theorem terminalRegionCompletion_of_forall_presentation {ε Λ : ℝ}
    (h : ∀ D : OneStepIncoming.{u}, Nonempty (TerminalCorePresentation D ε Λ)) :
    TerminalRegionCompletion.{u} ε Λ :=
  ⟨fun D _ => h D⟩

def InitialSphericalFrontierReduction.of_region_and_presentation {τ : ℝ}
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

theorem nonempty_initialTerminalRegion_of_forall_low {D : OneStepIncoming.{u}}
    [CompactSpace ↥D.slab.terminalRegularOpen]
    [PreconnectedSpace ↥D.slab.terminalRegularOpen]
    {ε Λ r : ℝ} (hε : 0 < ε) (hε' : ε < 1) (hΛ : 1 ≤ Λ) (hr : 0 < r)
    (hrEq : r = D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)
    (hlow : ∀ x : ↥D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ (r ^ 2)⁻¹) :
    Nonempty (InitialTerminalRegion D ε Λ) :=
  ⟨{ epsilon_pos := hε
     epsilon_lt_one := hε'
     Lambda_ge_one := hΛ
     coreRadius := r
     coreRadius_pos := hr
     coreRadius_eq := hrEq
     component := univ
     component_finite := Set.finite_univ
     component_iff_meets_low := fun c => ⟨fun _ => by
       obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
       exact ⟨x, hx, hlow x⟩, fun _ => trivial⟩
     region := univ
     region_isOpen := isOpen_univ
     region_isCompact := isCompact_univ
     region_isPreconnected := isPreconnected_univ
     low_mem_region := fun _ _ => trivial
     region_mem_component := fun _ _ => trivial
     boundary_neck := fun x hx => absurd hx (by simp)
     boundary_scalar := fun x hx => absurd hx (by simp)
     high_scalar_outside := fun x hx => absurd hx (by simp) }⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
