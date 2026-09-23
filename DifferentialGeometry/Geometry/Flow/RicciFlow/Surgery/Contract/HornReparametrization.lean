import DifferentialGeometry.Topology.Manifold.HalfCylinderReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCoordinates

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)
  (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
  (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
  (b : ∀ c, P.hornIndex c → ℝ)
  (htail : ∀ c e (q : NeckCylinder), b c e ≤ q.2 → F c e q = q)

include hfix in
private theorem fixes_nonpositive (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (q : NeckCylinder) (hq : q.2 ≤ 0) : F c e q = q :=
  hfix c e q (hq.trans (P.hornCollar c e).radius_pos.le)

include hfix in
private theorem reparametrized_half_range (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) :
    range (fun q : HalfNeckCylinder => P.horn c e (F c e q.val)) =
      range (fun q : HalfNeckCylinder => P.horn c e q.val) :=
  range_comp_halfCylinder (F c e) (fixes_nonpositive P F hfix c e)
    (fun q : HalfNeckCylinder => P.horn c e q.val)

def reparametrizeHorns : TerminalCorePresentation D ε Λ where
  epsilon_pos := P.epsilon_pos
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
  horn := fun c e q => P.horn c e (F c e q)
  horn_smooth := by
    intro c e
    apply (P.horn_smooth c e).comp (F c e).contMDiff.contMDiffOn
    rintro q ⟨_, hq⟩
    exact ⟨mem_univ _, (halfCylinder_image_nonneg_iff (F c e) (fixes_nonpositive P F hfix c e) q).mpr hq⟩
  horn_interior_embedding := by
    intro c e
    change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (P.positiveHornMap c e ∘ positiveCylinderDiffeomorph (F c e) (fixes_nonpositive P F hfix c e))
    have he : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (P.positiveHornMap c e) :=
      P.horn_interior_embedding c e
    exact he.comp_diffeomorph (positiveCylinderDiffeomorph (F c e) (fixes_nonpositive P F hfix c e))
  horn_injOn := by
    intro c e p hp q hq he
    apply (F c e).injective
    exact P.horn_injOn c e
      ⟨mem_univ _, (halfCylinder_image_nonneg_iff (F c e) (fixes_nonpositive P F hfix c e) p).mpr hp.2⟩
      ⟨mem_univ _, (halfCylinder_image_nonneg_iff (F c e) (fixes_nonpositive P F hfix c e) q).mpr hq.2⟩ he
  horn_proper := by
    intro c e
    exact (P.horn_proper c e).comp
      (halfCylinderHomeomorph (F c e) (fixes_nonpositive P F hfix c e)).isProperMap
  horn_range_disjoint := by
    intro c e e' he
    rw [reparametrized_half_range P F hfix, reparametrized_half_range P F hfix]
    exact P.horn_range_disjoint c e e' he
  horn_meets_core := by
    intro c e
    rw [reparametrized_half_range P F hfix, P.horn_meets_core]
    congr 1
    funext y
    rw [hfix c e (y, 0) (P.hornCollar c e).radius_pos.le]
  horn_base_covers_boundary := by
    intro c hc
    rw [P.horn_base_covers_boundary c hc]
    congr 1
    funext e
    congr 1
    funext y
    rw [hfix c e (y, 0) (P.hornCollar c e).radius_pos.le]
  hornCollar := fun c e =>
    { radius := (P.hornCollar c e).radius
      radius_pos := (P.hornCollar c e).radius_pos
      neighborhood := (P.hornCollar c e).neighborhood
      toDiffeomorph := (P.hornCollar c e).toDiffeomorph
      zero_eq := fun y => by
        rw [hfix c e (y, 0) (P.hornCollar c e).radius_pos.le]
        exact (P.hornCollar c e).zero_eq y }
  horn_collar_core_side := P.horn_collar_core_side
  horn_collar_eq := by
    intro c e q hq
    rw [hfix c e (q.1, q.2) q.2.property.2.le]
    exact P.horn_collar_eq c e q hq
  horn_covers_component := by
    intro c hc
    rw [P.horn_covers_component c hc]
    congr 1
    congr 1
    funext e
    exact (reparametrized_half_range P F hfix c e).symm
  horn_scalar_large := by
    intro c e y s hs
    exact P.horn_scalar_large c e (F c e (y, s)).1 (F c e (y, s)).2
      ((halfCylinder_image_nonneg_iff (F c e) (fixes_nonpositive P F hfix c e) (y, s)).mpr hs)
  horn_base_scalar := by
    intro c e y
    rw [hfix c e (y, 0) (P.hornCollar c e).radius_pos.le]
    exact P.horn_base_scalar c e y
  horn_scalar_diverges := by
    intro c e L
    obtain ⟨s, hs⟩ := P.horn_scalar_diverges c e L
    refine ⟨max s (b c e), ?_⟩
    intro y u hu
    rw [htail c e (y, u) ((le_max_right _ _).trans hu)]
    exact hs y u ((le_max_left _ _).trans hu)
  horn_spatial_neck := by
    intro c e x hx
    rw [reparametrized_half_range P F hfix] at hx
    exact P.horn_spatial_neck c e x hx

@[simp]
theorem reparametrizeHorns_core : (P.reparametrizeHorns F hfix b htail).core = P.core := rfl

@[simp]
theorem reparametrizeHorns_horn (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) (q : NeckCylinder) :
    (P.reparametrizeHorns F hfix b htail).horn c e q = P.horn c e (F c e q) := rfl

theorem reparametrizeHorns_range (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) :
    range (fun q : HalfNeckCylinder => (P.reparametrizeHorns F hfix b htail).horn c e q.val) =
      range (fun q : HalfNeckCylinder => P.horn c e q.val) :=
  reparametrized_half_range P F hfix c e

theorem reparametrizeHorns_eq_neck_on_collar
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (Θ : neckCentralOpen δ → positiveHornDomain)
    (hΘ : ∀ q, P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q))
    (a : ℝ) (hF : ∀ q : neckCentralOpen δ, F c e (q.val.1, a - q.val.2) = (Θ q).val) :
    ∀ q : neckCentralOpen δ,
      (P.reparametrizeHorns F hfix b htail).horn c e (q.val.1, a - q.val.2) =
        N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) := by
  intro q
  rw [reparametrizeHorns_horn, hF]
  exact hΘ q


theorem reparametrizeHorns_eq_at_base
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (q : NeckCylinder) (hq : q.2 ≤ (P.hornCollar c e).radius) :
    (P.reparametrizeHorns F hfix b htail).horn c e q = P.horn c e q := by
  rw [reparametrizeHorns_horn, hfix c e q hq]

theorem reparametrizeHorns_eq_at_end
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (q : NeckCylinder) (hq : b c e ≤ q.2) :
    (P.reparametrizeHorns F hfix b htail).horn c e q = P.horn c e q := by
  rw [reparametrizeHorns_horn, htail c e q hq]

theorem reparametrizeHorns_eq_neck_retainedCollar
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (Θ : neckCentralOpen δ → positiveHornDomain)
    (hΘ : ∀ q, P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q))
    (a : ℝ) (hF : ∀ q : neckCentralOpen δ, F c e (q.val.1, a - q.val.2) = (Θ q).val)
    (q : neckRetainedCollar δ) :
    (P.reparametrizeHorns F hfix b htail).horn c e (q.val.1, a - q.val.2) =
      N.chart ⟨q.val, by
        change -δ⁻¹ - 1 < q.val.2 ∧ q.val.2 < δ⁻¹ + 1
        constructor <;> linarith [q.property.1, q.property.2, inv_pos.mpr N.delta_pos]⟩ := by
  have hq : q.val ∈ neckCentralOpen δ :=
    ⟨mem_univ _, by linarith [q.property.1, inv_pos.mpr N.delta_pos], q.property.2⟩
  exact P.reparametrizeHorns_eq_neck_on_collar F hfix b htail c e N Θ hΘ a hF ⟨q.val, hq⟩


def reparametrizeHornsOfCompactSupport
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e)) (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ) :
    TerminalCorePresentation D ε Λ := by
  choose B hB using fun c e => exists_axial_bound_of_compact_support (F c e) (K c e) (hK c e) (hF c e)
  exact P.reparametrizeHorns F hfix B hB

@[simp]
theorem reparametrizeHornsOfCompactSupport_horn
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e)) (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) (q : NeckCylinder) :
    (P.reparametrizeHornsOfCompactSupport F hfix K hK hF).horn c e q = P.horn c e (F c e q) := rfl

@[simp]
theorem reparametrizeHornsOfCompactSupport_core
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e)) (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ) :
    (P.reparametrizeHornsOfCompactSupport F hfix K hK hF).core = P.core := rfl

theorem reparametrizeHornsOfCompactSupport_range
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e)) (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    range (fun q : HalfNeckCylinder => (P.reparametrizeHornsOfCompactSupport F hfix K hK hF).horn c e q.val) =
      range (fun q : HalfNeckCylinder => P.horn c e q.val) :=
  reparametrized_half_range P F hfix c e

theorem reparametrizeHornsOfCompactSupport_eq_neck_retainedCollar
    (K : ∀ c, P.hornIndex c → Set NeckCylinder)
    (hK : ∀ c e, IsCompact (K c e)) (hcompact : ∀ c e, EqOn (F c e) id (K c e)ᶜ)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (Θ : neckCentralOpen δ → positiveHornDomain)
    (hΘ : ∀ q, P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q))
    (a : ℝ) (hF : ∀ q : neckCentralOpen δ, F c e (q.val.1, a - q.val.2) = (Θ q).val)
    (q : neckRetainedCollar δ) :
    (P.reparametrizeHornsOfCompactSupport F hfix K hK hcompact).horn c e (q.val.1, a - q.val.2) =
      N.chart ⟨q.val, by
        change -δ⁻¹ - 1 < q.val.2 ∧ q.val.2 < δ⁻¹ + 1
        constructor <;> linarith [q.property.1, q.property.2, inv_pos.mpr N.delta_pos]⟩ := by
  have hq : q.val ∈ neckCentralOpen δ :=
    ⟨mem_univ _, by linarith [q.property.1, inv_pos.mpr N.delta_pos], q.property.2⟩
  rw [reparametrizeHornsOfCompactSupport_horn, hF ⟨q.val, hq⟩]
  exact hΘ ⟨q.val, hq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
