import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections
import DifferentialGeometry.Topology.GroupAction.Quotient
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction po_dist_smul)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open ProjectiveOrthogonalGroup (PO)
open CuspCrossSections (endStabilizer interiorHomeomorph)
open OrbifoldStrata (closedSmallSubgroup_le)
open ElementaryEnds (mem_setStabilizer)

variable {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))

local notation "Q" => @MulAction.orbitRel.Quotient Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)
local notation "π" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))

private theorem isOpenMap_quotient_projection : IsOpenMap (π : HUpper n → Q) := by
  let := EquivariantMap.subAction hn Γ
  let : ContinuousConstSMul Γ (HUpper n) :=
    ⟨fun γ => (Isometry.of_dist_eq (po_dist_smul hn (γ : PO n 1))).continuous⟩
  exact (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := HUpper n)).isOpenMap

theorem image_interior_thinRegion (r : ℝ) (S : Set (BoundaryH n)) (γ : Γ) :
    (fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) ''
      interior (thinRegion hn Γ r S) =
        interior (thinRegion hn Γ r
          ((fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S)) := by
  have h := (interiorHomeomorph hn γ).image_interior (thinRegion hn Γ r S)
  change (fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) ''
    interior (thinRegion hn Γ r S) =
      interior ((fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) '' thinRegion hn Γ r S) at h
  rwa [image_thinRegion] at h

theorem precisely_invariant_interior_thinRegion (hΓ : IsDiscrete (SetLike.coe Γ))
    (r : ℝ) (S : Set (BoundaryH n)) (γ : Γ) :
    ((γ : PO n 1) ∈ endStabilizer hn Γ S →
      (fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) ''
        interior (thinRegion hn Γ r S) = interior (thinRegion hn Γ r S)) ∧
    ((γ : PO n 1) ∉ endStabilizer hn Γ S →
      Disjoint ((fun x : HUpper n => (poMulAction hn).smul (γ : PO n 1) x) ''
        interior (thinRegion hn Γ r S)) (interior (thinRegion hn Γ r S))) := by
  constructor
  · intro hγ
    rw [image_interior_thinRegion, (mem_setStabilizer hn S γ).mp hγ.2]
  · intro hγ
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    have hleft := smul_mem_thinRegion hn Γ r (interior_subset hx) γ
    have hright := interior_subset hy
    let _ := hright.1
    have hlabel := hleft.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r _)) hright.2
    exact hγ ⟨γ.property, (mem_setStabilizer hn S γ).mpr hlabel⟩

section Inclusion

variable (r : ℝ) (S : Set (BoundaryH n))

local notation "P" => endStabilizer hn Γ S
local notation "QP" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))

private def stabilizerQuotientMap : C(QP, Q) := by
  let := EquivariantMap.subAction hn Γ
  let := EquivariantMap.subAction hn P
  exact (ContinuousMap.id (HUpper n)).orbitQuotientMap
    (Subgroup.inclusion (show P ≤ Γ from inf_le_left)) (by intro γ x; rfl)

def thinRegionQuotientInclusion : C(πP '' interior (thinRegion hn Γ r S), Q) :=
  (stabilizerQuotientMap hn Γ S).comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem thinRegionQuotientInclusion_mk (x : HUpper n)
    (hx : x ∈ interior (thinRegion hn Γ r S)) :
    thinRegionQuotientInclusion hn Γ r S ⟨πP x, ⟨x, hx, rfl⟩⟩ = π x := rfl

theorem range_thinRegionQuotientInclusion :
    Set.range (thinRegionQuotientInclusion hn Γ r S) = π '' interior (thinRegion hn Γ r S) := by
  ext z
  constructor
  · rintro ⟨⟨q, x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨πP x, ⟨x, hx, rfl⟩⟩, rfl⟩

theorem isOpenEmbedding_thinRegionQuotientInclusion (hΓ : IsDiscrete (SetLike.coe Γ)) :
    _root_.Topology.IsOpenEmbedding (thinRegionQuotientInclusion hn Γ r S) := by
  let := EquivariantMap.subAction hn Γ
  apply _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (thinRegionQuotientInclusion hn Γ r S).continuous
  · rintro ⟨q, x, hx, rfl⟩ ⟨q', y, hy, rfl⟩ h
    change π x = π y at h
    obtain ⟨γ, hγ⟩ := Quotient.exact h
    change (poMulAction hn).smul (γ : PO n 1) y = x at hγ
    have hmem : (γ : PO n 1) ∈ P := by
      by_contra hnot
      exact Set.disjoint_left.mp ((precisely_invariant_interior_thinRegion hn Γ hΓ r S γ).2 hnot)
        ⟨y, hy, hγ⟩ hx
    apply Subtype.ext
    exact Quotient.sound ⟨⟨γ, hmem⟩, hγ⟩
  · let := EquivariantMap.subAction hn P
    let : ContinuousConstSMul P (HUpper n) :=
      ⟨fun γ => (Isometry.of_dist_eq (po_dist_smul hn (γ : PO n 1))).continuous⟩
    have hf : IsOpenMap (stabilizerQuotientMap hn Γ S) :=
      IsOpenMap.of_comp (continuous_quotient_mk' : Continuous (πP : HUpper n → QP))
        Quotient.mk_surjective
        (isOpenMap_quotient_projection hn Γ)
    have hU : IsOpen (πP '' interior (thinRegion hn Γ r S)) :=
      (MulAction.isOpenQuotientMap_quotientMk (Γ := P) (T := HUpper n)).isOpenMap _ isOpen_interior
    exact hf.comp hU.isOpenMap_subtype_val

end Inclusion

theorem isOpen_quotient_interior_thinRegion (r : ℝ) (S : Set (BoundaryH n)) :
    IsOpen (π '' interior (thinRegion hn Γ r S)) :=
  isOpenMap_quotient_projection hn Γ _ isOpen_interior

theorem label_orbit_of_mem_quotient_thinRegion
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) {S T : Set (BoundaryH n)} {z : Q}
    (hzS : z ∈ π '' thinRegion hn Γ r S)
    (hzT : z ∈ π '' thinRegion hn Γ r T) :
    ∃ γ : Γ, (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T := by
  obtain ⟨x, hx, hxq⟩ := hzS
  obtain ⟨y, hy, hyq⟩ := hzT
  obtain ⟨γ, hγ⟩ := Quotient.exact (hyq.trans hxq.symm)
  change (poMulAction hn).smul (γ : PO n 1) x = y at hγ
  have hleft := smul_mem_thinRegion hn Γ r hx γ
  rw [hγ] at hleft
  have hright := hy
  let _ := hright.1
  exact ⟨γ, hleft.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r y)) hright.2⟩

theorem label_orbit_of_mem_quotient_interior_thinRegion
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) {S T : Set (BoundaryH n)} {z : Q}
    (hzS : z ∈ π '' interior (thinRegion hn Γ r S))
    (hzT : z ∈ π '' interior (thinRegion hn Γ r T)) :
    ∃ γ : Γ, (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T :=
  label_orbit_of_mem_quotient_thinRegion hn Γ hΓ r
    (Set.image_mono interior_subset hzS) (Set.image_mono interior_subset hzT)

theorem quotient_interior_thinRegion_eq_of_image_eq (r : ℝ)
    {S T : Set (BoundaryH n)} (γ : Γ)
    (hγ : (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T) :
    π '' interior (thinRegion hn Γ r S) = π '' interior (thinRegion hn Γ r T) := by
  let := EquivariantMap.subAction hn Γ
  have hU := image_interior_thinRegion hn Γ r S γ
  rw [hγ] at hU
  rw [← hU, Set.image_image]
  congr 1
  funext x
  exact (Quotient.sound (show MulAction.orbitRel Γ (HUpper n)
    ((poMulAction hn).smul (γ : PO n 1) x) x from ⟨γ, rfl⟩)).symm

theorem disjoint_quotient_interior_thinRegion (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    {S T : Set (BoundaryH n)}
    (hne : ¬ ∃ γ : Γ, (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T) :
    Disjoint (π '' interior (thinRegion hn Γ r S)) (π '' interior (thinRegion hn Γ r T)) :=
  Set.disjoint_left.mpr fun _ hzS hzT =>
    hne (label_orbit_of_mem_quotient_interior_thinRegion hn Γ hΓ r hzS hzT)

theorem quotient_interior_thinRegion_eq_or_disjoint (hΓ : IsDiscrete (SetLike.coe Γ))
    (r : ℝ) (S T : Set (BoundaryH n)) :
    π '' interior (thinRegion hn Γ r S) = π '' interior (thinRegion hn Γ r T) ∨
      Disjoint (π '' interior (thinRegion hn Γ r S)) (π '' interior (thinRegion hn Γ r T)) := by
  by_cases h : ∃ γ : Γ,
      (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T
  · obtain ⟨γ, hγ⟩ := h
    exact Or.inl (quotient_interior_thinRegion_eq_of_image_eq hn Γ r γ hγ)
  · exact Or.inr (disjoint_quotient_interior_thinRegion hn Γ hΓ r h)

theorem exists_quotient_interior_thinRegion_of_isConnected
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    {C : Set Q} (hC : IsConnected C)
    (hthin : C ⊆ ⋃ S : Set (BoundaryH n), π '' interior (thinRegion hn Γ r S)) :
    ∃ S : Set (BoundaryH n), C ⊆ π '' interior (thinRegion hn Γ r S) := by
  classical
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨S, hxS⟩ := Set.mem_iUnion.mp (hthin hx)
  let A := π '' interior (thinRegion hn Γ r S)
  let B := ⋃ T : {T : Set (BoundaryH n) // π '' interior (thinRegion hn Γ r T) ≠ A},
    π '' interior (thinRegion hn Γ r T.val)
  have hA : IsOpen A := isOpen_quotient_interior_thinRegion hn Γ r S
  have hB : IsOpen B := isOpen_iUnion fun T => isOpen_quotient_interior_thinRegion hn Γ r T.val
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    obtain ⟨T, hyT⟩ := Set.mem_iUnion.mp hyB
    rcases quotient_interior_thinRegion_eq_or_disjoint hn Γ hΓ r S T.val with he | he
    · exact T.property he.symm
    · exact Set.disjoint_left.mp he hyA hyT
  have hcover : C ⊆ A ∪ B := by
    intro y hy
    obtain ⟨T, hyT⟩ := Set.mem_iUnion.mp (hthin hy)
    by_cases hT : π '' interior (thinRegion hn Γ r T) = A
    · exact Or.inl (hT ▸ hyT)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hyT⟩)
  exact ⟨S, hC.isPreconnected.subset_left_of_subset_union hA hB hd hcover ⟨x, hx, hxS⟩⟩

end DifferentialGeometry.OrbifoldThinRegions
