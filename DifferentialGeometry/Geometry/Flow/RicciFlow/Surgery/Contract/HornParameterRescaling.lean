import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornReparametrization
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarRescaling

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {eps Lambda : ℝ}

private def axialScaling (lambda : ℝ) (h : 0 < lambda) :
    NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder :=
  Diffeomorph.fiberwiseAffine (fun _ => 0) (fun _ => lambda⁻¹)
    contMDiff_const contMDiff_const (fun _ => inv_ne_zero h.ne')

private theorem axialScaling_apply (lambda : ℝ) (h : 0 < lambda) (q : NeckCylinder) :
    axialScaling lambda h q = (q.1, q.2 / lambda) := by
  change (q.1, 0 + lambda⁻¹ * q.2) = _
  rw [zero_add, div_eq_inv_mul]

private def positiveAxialScaling (lambda : ℝ) (h : 0 < lambda) :
    positiveHornDomain ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ positiveHornDomain where
  toEquiv := ((axialScaling lambda h).toHomeomorph.subtype (fun q => by
    change (True ∧ 0 < q.2) ↔ (True ∧ 0 < (axialScaling lambda h q).2)
    rw [axialScaling_apply]
    exact and_congr_right fun _ => (div_pos_iff_of_pos_right h).symm)).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff positiveHornDomain _).mp
    exact (axialScaling lambda h).contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff positiveHornDomain _).mp
    exact (axialScaling lambda h).symm.contMDiff.comp contMDiff_subtype_val

private def halfAxialScaling (lambda : ℝ) (h : 0 < lambda) : HalfNeckCylinder ≃ₜ HalfNeckCylinder :=
  (axialScaling lambda h).toHomeomorph.subtype (fun q => by
    change 0 ≤ q.2 ↔ 0 ≤ (axialScaling lambda h q).2
    rw [axialScaling_apply]
    constructor
    · intro hq; exact div_nonneg hq h.le
    · intro hq
      change 0 ≤ q.2 / lambda at hq
      have hm := mul_nonneg hq h.le
      rwa [div_mul_cancel₀ _ h.ne'] at hm)

private theorem rescaled_half_range (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) :
    range (fun q : HalfNeckCylinder => P.horn c e (q.val.1, q.val.2 / lambda)) =
      range (fun q : HalfNeckCylinder => P.horn c e q.val) := by
  have heq : (fun q : HalfNeckCylinder => P.horn c e (q.val.1, q.val.2 / lambda)) =
      (fun q : HalfNeckCylinder => P.horn c e q.val) ∘ halfAxialScaling lambda hlambda := by
    funext q
    change P.horn c e (q.val.1, q.val.2 / lambda) = P.horn c e (axialScaling lambda hlambda q.val)
    rw [axialScaling_apply]
  rw [heq]
  exact (halfAxialScaling lambda hlambda).surjective.range_comp _

def rescaleHornParameters (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) : TerminalCorePresentation D eps Lambda where
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
  horn := fun c e q => P.horn c e (q.1, q.2 / lambda)
  horn_smooth := by
    intro c e
    exact (P.horn_smooth c e).comp
      (contMDiff_fst.prodMk (contMDiff_snd.div_const lambda)).contMDiffOn
      (fun q hq => ⟨mem_univ _, div_nonneg hq.2 hlambda.le⟩)
  horn_interior_embedding := by
    intro c e
    have he := (P.horn_interior_embedding c e).comp_diffeomorph
      (positiveAxialScaling lambda hlambda)
    have hfun : (fun q : positiveHornDomain => P.horn c e (q.val.1, q.val.2 / lambda)) =
        (fun q : positiveHornDomain => P.horn c e q.val) ∘ positiveAxialScaling lambda hlambda := by
      funext q
      change P.horn c e (q.val.1, q.val.2 / lambda) = P.horn c e (axialScaling lambda hlambda q.val)
      rw [axialScaling_apply]
    change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (fun q : positiveHornDomain => P.horn c e (q.val.1, q.val.2 / lambda))
    rw [hfun]
    exact he
  horn_injOn := by
    intro c e x hx y hy hxy
    have he := P.horn_injOn c e ⟨mem_univ _, div_nonneg hx.2 hlambda.le⟩
      ⟨mem_univ _, div_nonneg hy.2 hlambda.le⟩ hxy
    have hh := Prod.mk.inj he
    exact Prod.ext hh.1 ((div_left_inj' hlambda.ne').mp hh.2)
  horn_proper := by
    intro c e
    have h := (P.horn_proper c e).comp (halfAxialScaling lambda hlambda).isProperMap
    convert h using 1
    funext q
    change P.horn c e (q.val.1, q.val.2 / lambda) = P.horn c e (axialScaling lambda hlambda q.val)
    rw [axialScaling_apply]
  horn_range_disjoint := by
    intro c e e' he
    rw [rescaled_half_range P lambda hlambda, rescaled_half_range P lambda hlambda]
    exact P.horn_range_disjoint c e e' he
  horn_meets_core := by
    intro c e
    rw [rescaled_half_range P lambda hlambda, P.horn_meets_core]
    simp only [zero_div]
  horn_base_covers_boundary := by
    intro c hc
    simpa only [zero_div] using P.horn_base_covers_boundary c hc
  hornCollar := fun c e =>
    { ((P.hornCollar c e).rescaleParameter lambda hlambda) with
      zero_eq := fun z => by simpa only [zero_div] using
        ((P.hornCollar c e).rescaleParameter lambda hlambda).zero_eq z }
  horn_collar_core_side := by
    intro c e q
    change (P.hornCollar c e).toFun (q.1, ⟨q.2.val / lambda, _⟩) ∈ P.core c ↔ q.2.val ≤ 0
    rw [P.horn_collar_core_side]
    constructor
    · intro h
      change q.2.val / lambda ≤ 0 at h
      have hm := mul_nonpos_of_nonpos_of_nonneg h hlambda.le
      rwa [div_mul_cancel₀ _ hlambda.ne'] at hm
    · intro h
      exact div_nonpos_of_nonpos_of_nonneg h hlambda.le
  horn_collar_eq := by
    intro c e q hq
    change (P.hornCollar c e).toFun (q.1, ⟨q.2.val / lambda, _⟩) =
      P.horn c e (q.1, q.2.val / lambda)
    exact P.horn_collar_eq c e _ (div_nonneg hq hlambda.le)
  horn_covers_component := by
    intro c hc
    rw [P.horn_covers_component c hc]
    congr 1
    congr 1
    funext e
    exact (rescaled_half_range P lambda hlambda c e).symm
  horn_scalar_large := by
    intro c e y t ht
    exact P.horn_scalar_large c e y (t / lambda) (div_nonneg ht hlambda.le)
  horn_base_scalar := by
    intro c e y
    simpa only [zero_div] using P.horn_base_scalar c e y
  horn_scalar_diverges := by
    intro c e B
    obtain ⟨r, hr⟩ := P.horn_scalar_diverges c e B
    refine ⟨lambda * r, ?_⟩
    intro y t ht
    exact hr y (t / lambda) ((le_div_iff₀ hlambda).mpr (by simpa only [mul_comm] using ht))
  horn_spatial_neck := by
    intro c e x hx
    rw [rescaled_half_range P lambda hlambda] at hx
    exact P.horn_spatial_neck c e x hx

@[simp] theorem rescaleHornParameters_horn (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) (c) (e : P.hornIndex c) (q : NeckCylinder) :
    (P.rescaleHornParameters lambda hlambda).horn c e q = P.horn c e (q.1, q.2 / lambda) := rfl

theorem rescaleHornParameters_range (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) (c) (e : P.hornIndex c) :
    range (fun q : HalfNeckCylinder => (P.rescaleHornParameters lambda hlambda).horn c e q.val) =
      range (fun q : HalfNeckCylinder => P.horn c e q.val) :=
  rescaled_half_range P lambda hlambda c e

@[simp] theorem rescaleHornParameters_core (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (P.rescaleHornParameters lambda hlambda).core = P.core := rfl

@[simp] theorem rescaleHornParameters_collar_radius (P : TerminalCorePresentation D eps Lambda)
    (lambda : ℝ) (hlambda : 0 < lambda) (c) (e : P.hornIndex c) :
    ((P.rescaleHornParameters lambda hlambda).hornCollar c e).radius =
      lambda * (P.hornCollar c e).radius := rfl

def restrictHornCollars (P : TerminalCorePresentation D eps Lambda)
    (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
    (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius) : TerminalCorePresentation D eps Lambda :=
  { P with
    hornCollar := fun c e => (P.hornCollar c e).restrictRadius (r c e) (hr c e) (hle c e)
    horn_collar_core_side := by
      intro c e q
      exact P.horn_collar_core_side c e _
    horn_collar_eq := by
      intro c e q hq
      exact P.horn_collar_eq c e _ hq }

@[simp] theorem restrictHornCollars_horn (P : TerminalCorePresentation D eps Lambda)
    (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
    (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius) :
    (P.restrictHornCollars r hr hle).horn = P.horn := rfl

@[simp] theorem restrictHornCollars_core (P : TerminalCorePresentation D eps Lambda)
    (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
    (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius) :
    (P.restrictHornCollars r hr hle).core = P.core := rfl

@[simp] theorem restrictHornCollars_radius (P : TerminalCorePresentation D eps Lambda)
    (r : ∀ c, P.hornIndex c → ℝ) (hr : ∀ c e, 0 < r c e)
    (hle : ∀ c e, r c e ≤ (P.hornCollar c e).radius) (c) (e : P.hornIndex c) :
    ((P.restrictHornCollars r hr hle).hornCollar c e).radius = r c e := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
