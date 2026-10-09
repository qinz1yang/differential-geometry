import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections
import DifferentialGeometry.Topology.GroupAction.Quotient

noncomputable section

namespace DifferentialGeometry.OrbifoldThinRegions

open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open ProjectiveOrthogonalGroup (PO)
open CuspCrossSections (endStabilizer interiorHomeomorph)
open ElementaryEnds (mem_setStabilizer)

variable {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))

local notation "Q" => @MulAction.orbitRel.Quotient Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)
local notation "π" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))

section Saturation

variable (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ} {S : Set (BoundaryH n)}
  {A : Set (HUpper n)}

local notation "P" => endStabilizer hn Γ S

include hΓ in
theorem isClosed_saturation_of_subset_thinRegion (hA : IsClosed A)
    (hsub : A ⊆ thinRegion hn Γ r S)
    (hinv : ∀ γ : P, ∀ p ∈ A, (poMulAction hn).smul (γ : PO n 1) p ∈ A) :
    IsClosed (⋃ γ : Γ, (fun p => (poMulAction hn).smul (γ : PO n 1) p) '' A) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  let F (T : Set (BoundaryH n)) : Set (HUpper n) :=
    ⋃ γ : Γ, ⋃ (_ : (fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S = T),
      (fun p => (γ : PO n 1) • p) '' A
  have hFsub (T : Set (BoundaryH n)) : F T ⊆ thinRegion hn Γ r T := by
    rintro p hp
    obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hγT, q, hq, rfl⟩ := Set.mem_iUnion.mp hγ
    have h := smul_mem_thinRegion hn Γ r (hsub hq) γ
    change (γ : PO n 1) • q ∈ thinRegion hn Γ r
      ((fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S) at h
    exact hγT ▸ h
  have hFclosed (T : Set (BoundaryH n)) : IsClosed (F T) := by
    by_cases hex : ∃ γ : Γ, (fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S = T
    · obtain ⟨γ, hγ⟩ := hex
      have he : F T = (fun p => (γ : PO n 1) • p) '' A := by
        apply Set.Subset.antisymm
        · rintro p hp
          obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hp
          obtain ⟨hδT, q, hq, rfl⟩ := Set.mem_iUnion.mp hδ
          have hfix : (fun ξ : BoundaryH n => ((γ⁻¹ * δ : Γ) : PO n 1) • ξ) '' S = S := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
            rw [← Set.image_image, hδT, ← hγ, Set.image_image]
            simp only [inv_smul_smul, Set.image_id']
          let a : P := ⟨γ⁻¹ * δ, (γ⁻¹ * δ).property,
            (mem_setStabilizer hn S _).mpr hfix⟩
          refine ⟨(a : PO n 1) • q, hinv a q hq, ?_⟩
          change (γ : PO n 1) • (((γ : PO n 1)⁻¹ * (δ : PO n 1)) • q) = _
          rw [mul_smul, smul_inv_smul]
        · intro p hp
          exact Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨hγ, hp⟩⟩
      rw [he]
      exact (interiorHomeomorph hn γ).isClosedMap _ hA
    · have he : F T = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hp
        obtain ⟨hγT, _⟩ := Set.mem_iUnion.mp hγ
        exact hex ⟨γ, hγT⟩
      rw [he]
      exact isClosed_empty
  have hfinite : LocallyFinite F := (locallyFinite_thinRegion hn Γ hΓ r).subset hFsub
  have he : (⋃ γ : Γ, (fun p => (γ : PO n 1) • p) '' A) = ⋃ T, F T := by
    ext p
    constructor
    · intro hp
      obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion.mpr ⟨(fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S,
        Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨rfl, hγ⟩⟩⟩
    · intro hp
      obtain ⟨T, hpT⟩ := Set.mem_iUnion.mp hp
      obtain ⟨γ, hγT⟩ := Set.mem_iUnion.mp hpT
      obtain ⟨_, hγ⟩ := Set.mem_iUnion.mp hγT
      exact Set.mem_iUnion.mpr ⟨γ, hγ⟩
  change IsClosed (⋃ γ : Γ, (fun p : HUpper n => (γ : PO n 1) • p) '' A)
  rw [he]
  exact hfinite.isClosed_iUnion hFclosed

include hΓ in
theorem isClosed_quotient_of_subset_thinRegion (hA : IsClosed A)
    (hsub : A ⊆ thinRegion hn Γ r S)
    (hinv : ∀ γ : P, ∀ p ∈ A, (poMulAction hn).smul (γ : PO n 1) p ∈ A) :
    IsClosed (π '' A) := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  change IsClosed (π ⁻¹' (π '' A))
  have he : π ⁻¹' (π '' A) =
      ⋃ γ : Γ, (fun p => (poMulAction hn).smul (γ : PO n 1) p) '' A := by
    ext p
    constructor
    · rintro ⟨q, hq, he⟩
      obtain ⟨γ, hγ⟩ := Quotient.exact he.symm
      exact Set.mem_iUnion.mpr ⟨γ, q, hq, hγ⟩
    · intro hp
      obtain ⟨γ, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
      refine ⟨q, hq, ?_⟩
      exact (show π ((poMulAction hn).smul (γ : PO n 1) q) = π q from
        Quotient.sound ⟨γ, rfl⟩).symm
  rw [he]
  exact isClosed_saturation_of_subset_thinRegion hn Γ hΓ hA hsub hinv

end Saturation

section Inclusion

variable (S : Set (BoundaryH n)) (A : Set (HUpper n))

local notation "P" => endStabilizer hn Γ S
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))

def stabilizerQuotientInclusion : C(πP '' A, Q) := by
  let := EquivariantMap.subAction hn Γ
  let := EquivariantMap.subAction hn P
  let f := (ContinuousMap.id (HUpper n)).orbitQuotientMap
    (Subgroup.inclusion (show P ≤ Γ from inf_le_left)) (by intro γ x; rfl)
  exact f.comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem stabilizerQuotientInclusion_mk (p : HUpper n) (hp : p ∈ A) :
    stabilizerQuotientInclusion hn Γ S A ⟨πP p, ⟨p, hp, rfl⟩⟩ = π p := rfl

theorem range_stabilizerQuotientInclusion :
    Set.range (stabilizerQuotientInclusion hn Γ S A) = π '' A := by
  ext z
  constructor
  · rintro ⟨⟨q, p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨πP p, ⟨p, hp, rfl⟩⟩, rfl⟩

theorem isClosedEmbedding_stabilizerQuotientInclusion (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hA : IsClosed A) (hsub : A ⊆ thinRegion hn Γ r S)
    (hinv : ∀ γ : P, ∀ p ∈ A, (poMulAction hn).smul (γ : PO n 1) p ∈ A) :
    _root_.Topology.IsClosedEmbedding (stabilizerQuotientInclusion hn Γ S A) := by
  apply _root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (stabilizerQuotientInclusion hn Γ S A).continuous
  · rintro ⟨q, p, hp, rfl⟩ ⟨q', p', hp', rfl⟩ h
    change π p = π p' at h
    obtain ⟨γ, hγ⟩ := Quotient.exact h
    have hleft := smul_mem_thinRegion hn Γ r (hsub hp') γ
    change (poMulAction hn).smul (γ : PO n 1) p' = p at hγ
    rw [hγ] at hleft
    have hright := hsub hp
    let _ := hright.1
    have hlabel := hleft.2.unique
      (hΓ.mono (OrbifoldStrata.closedSmallSubgroup_le hn Γ r p)) hright.2
    apply Subtype.ext
    exact Quotient.sound ⟨⟨γ, γ.property, (mem_setStabilizer hn S γ).mpr hlabel⟩, hγ⟩
  · intro C hC
    have hpre : πP ⁻¹' (πP '' A) = A := by
      apply Set.Subset.antisymm
      · rintro p ⟨q, hq, he⟩
        obtain ⟨γ, hγ⟩ := Quotient.exact he.symm
        exact hγ ▸ hinv γ q hq
      · exact Set.subset_preimage_image _ _
    have hPA : IsClosed (πP '' A) := by
      apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
      change IsClosed (πP ⁻¹' (πP '' A))
      rwa [hpre]
    let B : Set (HUpper n) := πP ⁻¹' (Subtype.val '' C)
    have hB : IsClosed B :=
      (hPA.isClosedMap_subtype_val C hC).preimage continuous_quotient_mk'
    have hBsub : B ⊆ A := by
      intro p hp
      rw [← hpre]
      obtain ⟨q, _, he⟩ := hp
      change πP p ∈ πP '' A
      rw [← he]
      exact q.property
    have hBinv (γ : P) (p : HUpper n) (hp : p ∈ B) :
        (poMulAction hn).smul (γ : PO n 1) p ∈ B := by
      change πP ((poMulAction hn).smul (γ : PO n 1) p) ∈ Subtype.val '' C
      have he : πP ((poMulAction hn).smul (γ : PO n 1) p) = πP p :=
        Quotient.sound ⟨γ, rfl⟩
      rw [he]
      exact hp
    have he : (stabilizerQuotientInclusion hn Γ S A) '' C = π '' B := by
      ext z
      constructor
      · rintro ⟨⟨q, p, hp, rfl⟩, hCp, rfl⟩
        exact ⟨p, ⟨⟨πP p, ⟨p, hp, rfl⟩⟩, hCp, rfl⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨q, hCq, he⟩ := hp
        refine ⟨q, hCq, ?_⟩
        have hq : q = ⟨πP p, ⟨p, hBsub ⟨q, hCq, he⟩, rfl⟩⟩ := Subtype.ext he
        rw [hq]
        rfl
    rw [he]
    exact isClosed_quotient_of_subset_thinRegion hn Γ hΓ hB (hBsub.trans hsub) hBinv

end Inclusion

end DifferentialGeometry.OrbifoldThinRegions
