import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Curvature.RoundCylinder

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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

def TerminalCorePresentationInput.monoEpsilon {τ ε ε' : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) (hε : ε ≤ ε') (hε' : ε' < 1) :
    TerminalCorePresentationInput.{u} τ ε' where
  tau_pos := P.tau_pos
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  epsilon_lt_one := hε'
  lambda := P.lambda
  one_le_lambda := P.one_le_lambda
  presentation := fun D hτ => (P.presentation D hτ).map (fun Q => Q.monoEpsilon hε)

def TerminalCorePresentationInput.monoLambda {τ ε : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) {Λ' : ℝ}
    (hΛ : P.lambda ≤ Λ') (hΛ' : 1 ≤ Λ') :
    TerminalCorePresentationInput.{u} τ ε where
  tau_pos := P.tau_pos
  epsilon_pos := P.epsilon_pos
  epsilon_lt_one := P.epsilon_lt_one
  lambda := Λ'
  one_le_lambda := hΛ'
  presentation := fun D hτ => (P.presentation D hτ).map (fun Q => Q.monoLambda hΛ)

def TerminalCorePresentationInput.monoParams {τ ε ε' : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) {Λ' : ℝ}
    (hε : ε ≤ ε') (hε' : ε' < 1) (hΛ : P.lambda ≤ Λ') (hΛ' : 1 ≤ Λ') :
    TerminalCorePresentationInput.{u} τ ε' where
  tau_pos := P.tau_pos
  epsilon_pos := lt_of_lt_of_le P.epsilon_pos hε
  epsilon_lt_one := hε'
  lambda := Λ'
  one_le_lambda := hΛ'
  presentation := fun D hτ =>
    (P.presentation D hτ).map (fun Q => (Q.monoEpsilon hε).monoLambda hΛ)

section MetricMonotonicity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricDerivNormSupOn_mono {K : Set M} (hK : IsCompact K) {j k : ℕ} (hjk : j ≤ k)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K j gk gInf gRef ≤
      metricDerivNormSupOn (I := I) K k gk gInf gRef := by
  refine metricDerivNormSupOn_le_of_forall (I := I) K j gk gInf gRef
    (metricDerivNormSupOn (I := I) K k gk gInf gRef)
    (metricDerivNormSupOn_nonneg K k gk gInf gRef) ?_
  intro a ha x hx
  exact derivNorm_le_sup (I := I) hK (ha.trans hjk) gk gInf gRef hx

end MetricMonotonicity

section NeckDatum

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

def NormalizedNeck.lowerOrder {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k j : ℕ}
    (N : NormalizedNeck g δ k) (hjk : j ≤ k) : NormalizedNeck g δ j :=
  { N with
    closeness := lt_of_le_of_lt
      (metricDerivNormSupOn_mono (isCompact_neckClosedTest δ) hjk
        N.normalizedMetric (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)))
      N.closeness }

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.scale_eq_inv_sq_of_scalar {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) {h : ℝ}
    (hcenter : metricScalarAt g N.center = (h ^ 2)⁻¹) :
    N.scale = (h ^ 2)⁻¹ :=
  N.scale_scalar.trans hcenter

end NeckDatum

private theorem metricScalarAt_roundCylinderMetric_eq_one (x : NeckCylinder) :
    metricScalarAt roundCylinderMetric x = 1 := by
  rw [roundCylinderMetric_eq_geometry]
  rw [metricScalarAt_roundCylinder]
  norm_num

theorem exists_center_scalar_inv_sq_roundCylinder :
    ∃ h : ℝ, 0 < h ∧ ∀ x : NeckCylinder, metricScalarAt roundCylinderMetric x = (h ^ 2)⁻¹ :=
  ⟨1, by norm_num, fun x => by rw [metricScalarAt_roundCylinderMetric_eq_one]; norm_num⟩

def AdaptedHistoricalNeck.lowerOrder {d h : ℝ} {k j : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    AdaptedHistoricalNeck D horn d h j where
  d_pos := A.d_pos
  d_lt_quarter := A.d_lt_quarter
  h_pos := A.h_pos
  order_lower := hlow
  depth_ge := A.depth_ge
  chart := A.chart
  chart_agrees_horn := A.chart_agrees_horn
  shift := A.shift
  shift_lower := A.shift_lower
  neck := A.neck.lowerOrder hjk
  chart_eq_neck := A.chart_eq_neck
  scale_eq := A.scale_eq
  pastMetric := A.pastMetric
  pastMetric_inner := A.pastMetric_inner
  past_closeness := fun t ht m hm => A.past_closeness t ht m (le_trans hm hjk)

theorem AdaptedHistoricalNeck.center_scalar_eq {d h : ℝ} {k : ℕ}
    {horn : NeckCylinder → ↥D.slab.terminalRegularOpen}
    (A : AdaptedHistoricalNeck D horn d h k) :
    metricScalarAt D.terminal.metric A.neck.center = (h ^ 2)⁻¹ :=
  A.neck.scale_scalar.symm.trans A.scale_eq

theorem historicalNeckRecognition.mono_order {τ ε d Λ : ℝ} {k j : ℕ}
    (H : historicalNeckRecognition.{u} τ ε d k Λ) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    historicalNeckRecognition.{u} τ ε d j Λ := by
  obtain ⟨hd0, hd1, -, H0, hH0, hrec⟩ := H
  refine ⟨hd0, hd1, hlow, H0, hH0, fun D P c e h hh0 hhH hτ hscale => ?_⟩
  obtain ⟨A⟩ := hrec D P c e h hh0 hhH hτ hscale
  exact ⟨A.lowerOrder hjk hlow⟩

def GlobalStepInputs.monoOrder {p : CutoffParameters} {τ ε d : ℝ} {k j : ℕ}
    {DiscardedCutOpen : Type u → Prop}
    (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) (hjk : j ≤ k)
    (hlow : 2 * ⌊d⁻¹⌋₊ + 4 ≤ j) :
    GlobalStepInputs.{u} p τ ε d j DiscardedCutOpen where
  endInput := G.endInput
  neckInput := G.neckInput.mono_order hjk hlow
  pieceInput := G.pieceInput
  cylinderInput := G.cylinderInput
  protectInput := G.protectInput

theorem exists_precision_order_witness :
    ∃ d : ℝ, ∃ k : ℕ, 0 < d ∧ d < 1 / 4 ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k :=
  ⟨1 / 8, 20, by norm_num, by norm_num, by norm_num⟩

theorem not_order_threshold_nineteen :
    ¬ 2 * ⌊(1 / 8 : ℝ)⁻¹⌋₊ + 4 ≤ 19 := by
  norm_num

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
