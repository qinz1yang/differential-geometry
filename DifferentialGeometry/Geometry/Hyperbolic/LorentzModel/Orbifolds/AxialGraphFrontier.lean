import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialGraphRegion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Inward
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionClosure
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.StratumExtrema

noncomputable section

open scoped Topology

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)
open ProjectiveOrthogonalGroup (PO)
open CuspCrossSections (endStabilizer)
open AxisGeometry (axisFoot axisRadialFlow quotientAxisDistance quotientAxisRadialFlow
  axisGraphInward axisGraphClosed axisGraph)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1)) [DiscreteTopology Γ]
  (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)

local notation "hn" => Nat.succ_le_succ (Nat.zero_le m)
local notation "P" => endStabilizer hn Γ (Set.insert ξ (Set.singleton η))

omit [DiscreteTopology Γ] in
private theorem axialStabilizer_pair (γ : P) :
    (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
      (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))) := by
  have he := (ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2
  exact ⟨he ▸ Set.mem_image_of_mem _ (by simp), he ▸ Set.mem_image_of_mem _ (by simp)⟩

local notation "hP" => axialStabilizer_pair m Γ ξ η

local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction hn Γ
local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction hn P
local instance : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
  ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono (show P ≤ Γ from inf_le_left))
local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ⊤ (γ : PO (m + 1) 1)).continuous⟩
local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ⊤ (γ : PO (m + 1) 1)).continuous⟩

local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "R" => quotientAxisDistance m P ξ η hne hP
local notation "S" => {z : QP // R z = Real.arsinh 1}

private def axialStabilizerMap : C(QP, Q) :=
  (ContinuousMap.id (HUpper (m + 1))).orbitQuotientMap
    (Subgroup.inclusion (show P ≤ Γ from inf_le_left)) (by intro γ x; rfl)

local notation "j" => axialStabilizerMap m Γ ξ η

omit [DiscreteTopology Γ] in
private theorem axialStabilizerMap_image (A : Set QP) : j '' A = π '' (πP ⁻¹' A) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective x
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨πP y, hy, rfl⟩

omit [DiscreteTopology Γ] in
private theorem isOpenMap_axialStabilizerMap : IsOpenMap j :=
  IsOpenMap.of_comp (continuous_quotient_mk' : Continuous (πP : HUpper (m + 1) → QP))
    Quotient.mk_surjective
      (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := HUpper (m + 1))).isOpenMap

variable [IsCancelSMul (endStabilizer (Nat.succ_le_succ (Nat.zero_le m)) Γ {ξ, η}) (HUpper (m + 1))]

local notation "U" => axisGraphInward m P ξ η hne hP
local notation "K" => axisGraphClosed m P ξ η hne hP
local notation "G" => axisGraph m P ξ η hne hP

def axialGraphAmbientInward (α : S → ℝ) : Set Q := j '' U α

def axialGraphAmbient (α : S → ℝ) : Set Q := j '' G α

def axialGraphAmbientClosed (α : S → ℝ) : Set Q := j '' K α

def axialGraphAmbientPoint (s : S) (t : ℝ) : Q := j (quotientAxisRadialFlow m P ξ η hne hP t s.val)

theorem axialGraphAmbient_eq_range (α : S → ℝ) :
    axialGraphAmbient m Γ ξ η hne α =
      Set.range (fun s : S => axialGraphAmbientPoint m Γ ξ η hne s (α s)) := by
  rw [axialGraphAmbient, AxisGeometry.axisGraph_eq_range_flow, ← Set.range_comp]
  rfl

omit [DiscreteTopology Γ]
  [IsCancelSMul (endStabilizer (Nat.succ_le_succ (Nat.zero_le m)) Γ {ξ, η}) (HUpper (m + 1))] in
private theorem thinRegion_of_eq_quotient (r : ℝ) {x y : HUpper (m + 1)}
    (hxy : πP x = πP y) (hy : y ∈ thinRegion hn Γ r {ξ, η}) : x ∈ thinRegion hn Γ r {ξ, η} := by
  obtain ⟨γ, hγ⟩ := Quotient.exact hxy
  change (poMulAction hn).smul (γ : PO (m + 1) 1) y = x at hγ
  have hg : (γ : PO (m + 1) 1) ∈ Γ := γ.property.1
  have h := smul_mem_thinRegion hn Γ r hy ⟨γ, hg⟩
  rw [(ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2] at h
  exact hγ ▸ h

private theorem preimage_axisGraphClosed_off_axis_subset_thinRegion
    (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η})
    {y : HUpper (m + 1)} (hyK : πP y ∈ K α) (hy : y ∉ AxisGeometry.axis ξ η) :
    y ∈ thinRegion hn Γ r {ξ, η} := by
  rcases (AxisGeometry.mem_axisGraphClosed_iff m P ξ η hne hP α (πP y)).mp hyK with hyC | ⟨s, t, ht, he⟩
  · have hz := (AxisGeometry.quotientAxisDistance_eq_zero_iff_mem_image_axis m P ξ η hne hP (πP y)).mpr hyC
    have hfoot : y = axisFoot ξ η hne y := dist_eq_zero.mp hz
    exact (hy (hfoot.symm ▸ AxisGeometry.axisFoot_mem ξ η hne y)).elim
  · obtain ⟨z, hz⟩ := Quotient.mk_surjective s.val
    have htop : axisRadialFlow ξ η hne (α s) z ∈ thinRegion hn Γ r {ξ, η} := by
      apply hgraph
      rw [AxisGeometry.axisGraph_eq_range_flow]
      refine ⟨s, ?_⟩
      change quotientAxisRadialFlow m P ξ η hne hP (α s) s.val = _
      rw [← hz]
      rfl
    have hin := axisRadialFlow_mem_thinRegion_of_nonpos hn Γ
      (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)) r ξ η hne htop
      (sub_nonpos.mpr ht) (hgeom _)
    rw [AxisGeometry.axisRadialFlow_add, sub_add_cancel] at hin
    apply thinRegion_of_eq_quotient m Γ ξ η r (y := axisRadialFlow ξ η hne t z) _ hin
    rw [← he, ← hz]
    rfl

private theorem preimage_axisGraphClosed_subset_thinRegion [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    πP ⁻¹' K α ⊆ thinRegion hn Γ r {ξ, η} := by
  intro y hyK
  by_cases hy : y ∉ AxisGeometry.axis ξ η
  · exact preimage_axisGraphClosed_off_axis_subset_thinRegion m Γ ξ η hne r hgeom α hgraph hyK hy
  · have hyaxis : y ∈ AxisGeometry.axis ξ η := Classical.not_not.mp hy
    have hyU : πP y ∈ U α := (AxisGeometry.mem_axisGraphInward_iff m P ξ η hne hP α (πP y)).mpr
      (Or.inl ⟨y, hyaxis, rfl⟩)
    have hU : IsOpen (πP ⁻¹' U α) :=
      (AxisGeometry.isOpen_axisGraphInward m P ξ η hne hP α hα).preimage continuous_quotient_mk'
    have hT : IsClosed (thinRegion hn Γ r {ξ, η}) := isClosed_thinRegion hn Γ
      (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)) r hgeom {ξ, η}
    have hdense : Dense (AxisGeometry.axis ξ η)ᶜ :=
      interior_eq_empty_iff_dense_compl.mp (StratumMaximum.interior_axis_eq_empty (by omega) ξ η)
    by_contra hnot
    obtain ⟨z, hz, hzaxis⟩ := mem_closure_iff_nhds.mp (hdense y) _
      (Filter.inter_mem (hU.mem_nhds hyU) (hT.isOpen_compl.mem_nhds hnot))
    exact hz.2 (preimage_axisGraphClosed_off_axis_subset_thinRegion m Γ ξ η hne r hgeom α hgraph
      (AxisGeometry.axisGraphInward_subset_axisGraphClosed m P ξ η hne hP α hz.1) hzaxis)

omit [IsCancelSMul (endStabilizer (Nat.succ_le_succ (Nat.zero_le m)) Γ {ξ, η}) (HUpper (m + 1))] in
private theorem injOn_axialStabilizerMap_thinRegion (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x)) :
    Set.InjOn j (πP '' thinRegion hn Γ r {ξ, η}) := by
  have hΓ : IsDiscrete (SetLike.coe Γ) := isDiscrete_iff_discreteTopology.mpr inferInstance
  have hinv : ∀ γ : P, ∀ y ∈ thinRegion hn Γ r {ξ, η},
      (poMulAction hn).smul (γ : PO (m + 1) 1) y ∈ thinRegion hn Γ r {ξ, η} := by
    intro γ y hy
    have h := smul_mem_thinRegion hn Γ r hy ⟨γ, γ.property.1⟩
    rwa [(ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2] at h
  have he := isClosedEmbedding_stabilizerQuotientInclusion hn Γ {ξ, η}
    (thinRegion hn Γ r {ξ, η}) hΓ (isClosed_thinRegion hn Γ hΓ r hgeom {ξ, η}) Set.Subset.rfl hinv
  intro x hx y hy hxy
  have h : stabilizerQuotientInclusion hn Γ {ξ, η} (thinRegion hn Γ r {ξ, η}) ⟨x, hx⟩ =
      stabilizerQuotientInclusion hn Γ {ξ, η} (thinRegion hn Γ r {ξ, η}) ⟨y, hy⟩ := hxy
  exact congrArg Subtype.val (he.injective h)

theorem isOpen_axialGraphAmbientInward [CompactSpace S] (α : S → ℝ) (hα : Continuous α) :
    IsOpen (axialGraphAmbientInward m Γ ξ η hne α) :=
  isOpenMap_axialStabilizerMap m Γ ξ η _ (AxisGeometry.isOpen_axisGraphInward m P ξ η hne hP α hα)

theorem isClosed_axialGraphAmbientClosed [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    IsClosed (axialGraphAmbientClosed m Γ ξ η hne α) := by
  rw [axialGraphAmbientClosed, axialStabilizerMap_image]
  apply isClosed_quotient_of_subset_thinRegion hn Γ
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
    ((AxisGeometry.isClosed_axisGraphClosed m P ξ η hne hP α hα).preimage continuous_quotient_mk')
    (preimage_axisGraphClosed_subset_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph)
  intro γ y hy
  change πP ((poMulAction hn).smul (γ : PO (m + 1) 1) y) ∈ K α
  have he : πP ((poMulAction hn).smul (γ : PO (m + 1) 1) y) = πP y := Quotient.sound ⟨γ, rfl⟩
  rw [he]
  exact hy

theorem closure_axialGraphAmbientInward [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    closure (axialGraphAmbientInward m Γ ξ η hne α) = axialGraphAmbientClosed m Γ ξ η hne α := by
  have hsub : axialGraphAmbientInward m Γ ξ η hne α ⊆ axialGraphAmbientClosed m Γ ξ η hne α :=
    Set.image_mono (AxisGeometry.axisGraphInward_subset_axisGraphClosed m P ξ η hne hP α)
  apply Set.Subset.antisymm
  · exact (isClosed_axialGraphAmbientClosed m Γ ξ η hne hm r hgeom α hα hgraph).closure_subset_iff.mpr hsub
  · change j '' K α ⊆ closure (j '' U α)
    rw [← AxisGeometry.closure_axisGraphInward m P ξ η hne hP α hα]
    exact image_closure_subset_closure_image (j).continuous

private theorem axisGraphClosed_subset_image_thinRegion [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    K α ⊆ πP '' thinRegion hn Γ r {ξ, η} := by
  intro z hz
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective z
  exact ⟨y, preimage_axisGraphClosed_subset_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph hz, rfl⟩

theorem axialGraphAmbientClosed_subset_quotient_thinRegion [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    axialGraphAmbientClosed m Γ ξ η hne α ⊆ π '' thinRegion hn Γ r {ξ, η} := by
  rw [axialGraphAmbientClosed, axialStabilizerMap_image]
  exact Set.image_mono
    (preimage_axisGraphClosed_subset_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph)

theorem axialGraphAmbientInward_subset_quotient_thinRegion [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    axialGraphAmbientInward m Γ ξ η hne α ⊆ π '' thinRegion hn Γ r {ξ, η} := by
  apply (Set.image_mono
    (AxisGeometry.axisGraphInward_subset_axisGraphClosed m P ξ η hne hP α)).trans
  exact axialGraphAmbientClosed_subset_quotient_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph

theorem frontier_axialGraphAmbientInward [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η}) :
    frontier (axialGraphAmbientInward m Γ ξ η hne α) = axialGraphAmbient m Γ ξ η hne α := by
  rw [frontier, closure_axialGraphAmbientInward m Γ ξ η hne hm r hgeom α hα hgraph,
    (isOpen_axialGraphAmbientInward m Γ ξ η hne α hα).interior_eq]
  have hinj := injOn_axialStabilizerMap_thinRegion m Γ ξ η r hgeom
  have hthin := axisGraphClosed_subset_image_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph
  have hsub := AxisGeometry.axisGraphInward_subset_axisGraphClosed m P ξ η hne hP α
  change j '' K α \ j '' U α = j '' G α
  rw [← AxisGeometry.axisGraphClosed_diff_axisGraphInward m P ξ η hne hP α]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
    exact ⟨x, ⟨hx, fun hu => hnot ⟨x, hu, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hxK, hxU⟩, rfl⟩
    refine ⟨⟨x, hxK, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hyx : y = x := hinj (hthin (hsub hy)) (hthin hxK) he
    exact hxU (hyx ▸ hy)

theorem axialGraphAmbientPoint_mem_inward_iff [CompactSpace S]
    (hm : 1 ≤ m) (r : ℝ)
    (hgeom : ∀ x : HUpper (m + 1), BoundaryStabilizer.ElementaryGeometry hn
      (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    (α : S → ℝ) (hα : Continuous α) (hgraph : πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η})
    (s : S) (t : ℝ)
    (hchart : quotientAxisRadialFlow m P ξ η hne hP t s.val ∈ πP '' thinRegion hn Γ r {ξ, η}) :
    axialGraphAmbientPoint m Γ ξ η hne s t ∈ axialGraphAmbientInward m Γ ξ η hne α ↔ t < α s := by
  have hinj := injOn_axialStabilizerMap_thinRegion m Γ ξ η r hgeom
  have hthin := axisGraphClosed_subset_image_thinRegion m Γ ξ η hne hm r hgeom α hα hgraph
  have hsub := AxisGeometry.axisGraphInward_subset_axisGraphClosed m P ξ η hne hP α
  rw [← AxisGeometry.mem_axisGraphInward_flow_iff m P ξ η hne hP α s t]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx := hinj (hthin (hsub hy)) hchart he
    exact hyx ▸ hy
  · intro h
    exact ⟨_, h, rfl⟩

omit [DiscreteTopology Γ]
  [IsCancelSMul (endStabilizer (Nat.succ_le_succ (Nat.zero_le m)) Γ {ξ, η}) (HUpper (m + 1))] in
theorem axialGraphAmbientPoint_eq_mk (s : S) (t : ℝ) (y : HUpper (m + 1)) (hy : πP y = s.val) :
    axialGraphAmbientPoint m Γ ξ η hne s t = π (axisRadialFlow ξ η hne t y) := by
  change j (quotientAxisRadialFlow m P ξ η hne hP t s.val) = _
  rw [← hy]
  rfl

theorem graph_preimage_subset_thinRegion_of_mem_quotient_interior
    (r : ℝ) (α : S → ℝ)
    (hgraph : ∀ s : S, quotientAxisRadialFlow m P ξ η hne hP (α s) s.val ∈
      πP '' interior (thinRegion hn Γ r {ξ, η})) :
    πP ⁻¹' G α ⊆ thinRegion hn Γ r {ξ, η} := by
  intro y hy
  rw [Set.mem_preimage, AxisGeometry.axisGraph_eq_range_flow] at hy
  obtain ⟨s, hs⟩ := hy
  obtain ⟨z, hz, he⟩ := hgraph s
  apply thinRegion_of_eq_quotient m Γ ξ η r (y := z) _ (interior_subset hz)
  exact hs.symm.trans he.symm

end DifferentialGeometry.OrbifoldThinRegions
