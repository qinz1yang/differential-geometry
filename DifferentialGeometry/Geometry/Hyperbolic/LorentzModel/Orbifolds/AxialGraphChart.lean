import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialGraphFrontier
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.QuotientInclusion
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenPartialHomeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.OrbifoldThinRegions

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open CuspCrossSections (endStabilizer)
open AxisGeometry (quotientAxisDistance quotientAxisRadialFlow axisProductDiffeomorph axisOffCore)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1)) [DiscreteTopology Γ]
  (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)

local notation "hn" => Nat.succ_le_succ (Nat.zero_le m)
local notation "P" => endStabilizer hn Γ (Set.insert ξ (Set.singleton η))

omit [DiscreteTopology Γ] in
private theorem graphStabilizer_pair (γ : P) :
    (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
      (poBoundaryMulAction hn).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))) := by
  have he := (ElementaryEnds.mem_setStabilizer hn {ξ, η} γ).mp γ.property.2
  exact ⟨he ▸ Set.mem_image_of_mem _ (by simp), he ▸ Set.mem_image_of_mem _ (by simp)⟩

local notation "hP" => graphStabilizer_pair m Γ ξ η

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction hn Γ
private local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction hn P
private local instance : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp
  ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
    (show P ≤ Γ from inf_le_left))
private local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩
private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn Γ
    (isDiscrete_iff_discreteTopology.mpr inferInstance)
private local instance : ProperlyDiscontinuousSMul P (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction hn P
    ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
      (show P ≤ Γ from inf_le_left))

variable [IsCancelSMul Γ (HUpper (m + 1))]

private local instance : IsCancelSMul P (HUpper (m + 1)) :=
  EquivariantMap.isCancelSMul_subAction hn (show P ≤ Γ from inf_le_left)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "QP" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "R" => quotientAxisDistance m P ξ η hne hP
local notation "S" => {z : QP // R z = Real.arsinh 1}
local notation "O" => axisOffCore m P ξ η hne hP
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "J" => ModelWithCorners.prod K 𝓘(ℝ, ℝ)
local notation "j" => EquivariantMap.quotientInclusion («P» := P) (Γ := Γ) hn inf_le_left
local notation "d" => axisProductDiffeomorph m P ξ η hne hP
local notation "a" => Function.uncurry (axialGraphAmbientPoint m Γ ξ η hne)

private local instance : ChartedSpace (Fin m → ℝ) S :=
  AxisGeometry.axisSectionChartedSpace m P ξ η hne hP

private local instance : IsManifold K ∞ S := AxisGeometry.axisSection_isManifold m P ξ η hne hP

theorem isLocalDiffeomorph_axialGraphAmbientPoint : IsLocalDiffeomorph J I ∞ a := by
  have hj := EquivariantMap.isLocalDiffeomorph_quotientInclusion (show P ≤ Γ from inf_le_left) ∞
  have hval : IsLocalDiffeomorph I I ∞ (Subtype.val : O → QP) :=
    DifferentialGeometry.isLocalDiffeomorph_subtype_val O
  have hprod := DifferentialGeometry.isLocalDiffeomorph_comp (f := (d).symm) hval
    (d).symm.isLocalDiffeomorph
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (f := fun z : S × ℝ => ((d).symm z).val) hj hprod
  exact h

omit [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper (m + 1))] in
private theorem offCore_mk (p : HUpper (m + 1)) (hp : p ∉ AxisGeometry.axis ξ η) : πP p ∈ O := by
  intro haxis
  have hz := (AxisGeometry.quotientAxisDistance_eq_zero_iff_mem_image_axis m P ξ η hne hP (πP p)).mpr haxis
  have he : p = AxisGeometry.axisFoot ξ η hne p := dist_eq_zero.mp hz
  exact hp (he.symm ▸ AxisGeometry.axisFoot_mem ξ η hne p)

private theorem product_nonempty (hm : 1 ≤ m) : Nonempty (S × ℝ) := by
  let : Nonempty (HUpper (m + 1)) := ⟨HyperbolicFaithful.basepointH⟩
  have hdense : Dense (AxisGeometry.axis ξ η)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (StratumMaximum.interior_axis_eq_empty (by omega) ξ η)
  obtain ⟨p, hp⟩ := hdense.nonempty
  exact ⟨d ⟨πP p, offCore_mk m Γ ξ η hne p hp⟩⟩

local notation "V" r => (πP '' interior (thinRegion hn Γ r (Set.insert ξ (Set.singleton η))))
private def graphSource (r : ℝ) : Set (S × ℝ) :=
  {z : S × ℝ | quotientAxisRadialFlow m P ξ η hne hP z.2 z.1.val ∈ V r}

local notation "source" r => graphSource m Γ ξ η hne r

private theorem axialGraphAmbientPoint_injOn (r : ℝ) : Set.InjOn a (source r) := by
  intro z hz w hw he
  have hi := (isOpenEmbedding_thinRegionQuotientInclusion hn Γ r {ξ, η}
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))).injective
  have hv : ((d).symm z).val = ((d).symm w).val :=
    congrArg (fun q : V r => (q : QP)) (hi (a₁ := ⟨_, hz⟩) (a₂ := ⟨_, hw⟩) he)
  exact (d).symm.injective (Subtype.ext hv)

def axialGraphChart (hm : 1 ≤ m) (r : ℝ) : OpenPartialHomeomorph (S × ℝ) Q := by
  let := product_nonempty m Γ ξ η hne hm
  have hlocal := isLocalDiffeomorph_axialGraphAmbientPoint m Γ ξ η hne
  have hV : IsOpen (V r) := by
    exact (MulAction.isOpenQuotientMap_quotientMk (Γ := P) (T := HUpper (m + 1))).isOpenMap _ isOpen_interior
  have hsource : IsOpen (source r) :=
    hV.preimage (continuous_subtype_val.comp (d).symm.continuous)
  exact OpenPartialHomeomorph.ofContinuousOpen
    ((axialGraphAmbientPoint_injOn m Γ ξ η hne r).toPartialEquiv a (source r))
    hlocal.contMDiff.continuous.continuousOn hlocal.isOpenMap hsource

@[simp] theorem axialGraphChart_apply (hm : 1 ≤ m) (r : ℝ) (z : S × ℝ) :
    axialGraphChart m Γ ξ η hne hm r z = axialGraphAmbientPoint m Γ ξ η hne z.1 z.2 := rfl

@[simp] theorem axialGraphChart_source (hm : 1 ≤ m) (r : ℝ) :
    (axialGraphChart m Γ ξ η hne hm r).source =
      {z : S × ℝ | quotientAxisRadialFlow m P ξ η hne hP z.2 z.1.val ∈ V r} := rfl

theorem axialGraphChart_target (hm : 1 ≤ m) (r : ℝ) :
    (axialGraphChart m Γ ξ η hne hm r).target =
      π '' ((AxisGeometry.axis ξ η)ᶜ ∩ interior (thinRegion hn Γ r {ξ, η})) := by
  change a '' (source r) = _
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨p, hp, he⟩ := hz
    have hoff : p ∉ AxisGeometry.axis ξ η := by
      intro haxis
      exact ((d).symm z).property ⟨p, haxis, he⟩
    refine ⟨p, ⟨hoff, hp⟩, ?_⟩
    exact congrArg (j : QP → Q) he
  · rintro ⟨p, ⟨hoff, hp⟩, rfl⟩
    let z : O := ⟨πP p, offCore_mk m Γ ξ η hne p hoff⟩
    refine ⟨d z, ?_, ?_⟩
    · change ((d).symm ((d) z)).val ∈ V r
      rw [(d).symm_apply_apply]
      exact ⟨p, hp, rfl⟩
    · change j (((d).symm ((d) z)).val) = π p
      rw [(d).symm_apply_apply]
      rfl

def axialGraphPartialDiffeomorph (hm : 1 ≤ m) (r : ℝ) :
    PartialDiffeomorph J I (S × ℝ) Q ∞ :=
  (axialGraphChart m Γ ξ η hne hm r).toPartialDiffeomorph
    ((isLocalDiffeomorph_axialGraphAmbientPoint m Γ ξ η hne).isLocalDiffeomorphOn (source r))

theorem axialGraphPartialDiffeomorph_toOpenPartialHomeomorph (hm : 1 ≤ m) (r : ℝ) :
    (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).toOpenPartialHomeomorph =
      axialGraphChart m Γ ξ η hne hm r := rfl

@[simp] theorem axialGraphPartialDiffeomorph_source (hm : 1 ≤ m) (r : ℝ) :
    (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).source =
      {z : S × ℝ | quotientAxisRadialFlow m P ξ η hne hP z.2 z.1.val ∈ V r} := rfl

theorem axialGraphPartialDiffeomorph_target (hm : 1 ≤ m) (r : ℝ) :
    (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).target =
      π '' ((AxisGeometry.axis ξ η)ᶜ ∩ interior (thinRegion hn Γ r {ξ, η})) :=
  axialGraphChart_target m Γ ξ η hne hm r

@[simp] theorem axialGraphPartialDiffeomorph_apply (hm : 1 ≤ m) (r : ℝ) (z : S × ℝ) :
    axialGraphPartialDiffeomorph m Γ ξ η hne hm r z =
      axialGraphAmbientPoint m Γ ξ η hne z.1 z.2 := rfl

@[simp] theorem axialGraphPartialDiffeomorph_symm_apply (hm : 1 ≤ m) (r : ℝ) (y : Q) :
    (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).symm y =
      (axialGraphChart m Γ ξ η hne hm r).symm y := rfl

theorem axialGraphPartialDiffeomorph_symm_apply_mk (hm : 1 ≤ m) (r : ℝ)
    (p : HUpper (m + 1)) (hoff : p ∉ AxisGeometry.axis ξ η)
    (hp : p ∈ interior (thinRegion hn Γ r {ξ, η})) :
    (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).symm (π p) =
      d ⟨πP p, offCore_mk m Γ ξ η hne p hoff⟩ := by
  let z : O := ⟨πP p, offCore_mk m Γ ξ η hne p hoff⟩
  have hs : d z ∈ (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).source := by
    change ((d).symm ((d) z)).val ∈ V r
    rw [(d).symm_apply_apply]
    exact ⟨p, hp, rfl⟩
  have he : axialGraphPartialDiffeomorph m Γ ξ η hne hm r (d z) = π p := by
    change j (((d).symm ((d) z)).val) = π p
    rw [(d).symm_apply_apply]
    rfl
  rw [← he]
  exact (axialGraphPartialDiffeomorph m Γ ξ η hne hm r).left_inv hs

end DifferentialGeometry.OrbifoldThinRegions
