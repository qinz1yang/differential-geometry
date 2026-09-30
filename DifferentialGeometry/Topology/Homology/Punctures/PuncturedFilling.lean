import DifferentialGeometry.Topology.Homology.Punctures.DiskExcision
import DifferentialGeometry.Topology.Homology.Punctures.PuncturedAcyclic

open CategoryTheory Limits Set

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {e : Disk n → M} {B : Set M}

theorem isChartDisk.isHomotopyEquivInclusion_sdiff_halfDisk (he : isChartDisk e)
    (hD : range e ⊆ B) :
    isHomotopyEquivInclusion (B \ e '' diskInterior n) (B \ e '' halfDisk n) := by
  have h := he.isHomotopyEquivInclusion_annulus (ρ := 1 / 2) (by norm_num)
    (B := B \ e '' halfDisk n) ?_ ?_
  · convert h using 1
    ext x
    constructor
    · rintro ⟨hxB, hxU⟩
      refine ⟨⟨hxB, fun hK => hxU (image_halfDisk_subset_image_diskInterior e hK)⟩, ?_⟩
      rintro ⟨v, hv, rfl⟩
      exact hxU ⟨v, mem_diskInterior.2 hv.2, rfl⟩
    · rintro ⟨⟨hxB, hxK⟩, hxAnn⟩
      refine ⟨hxB, ?_⟩
      rintro ⟨v, hv, rfl⟩
      rw [mem_diskInterior] at hv
      by_cases h : ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2
      · exact hxK ⟨v, h, rfl⟩
      · exact hxAnn ⟨v, ⟨not_le.1 h, hv⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨hD (mem_range_self v), ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_halfDisk] at h
    exact absurd hv (not_lt.2 h)
  · exact disjoint_sdiff_left

namespace SingularPair

variable (R : ModuleCat.{u} ℤ)

def relativeHomologyPuncturedFillingIso (he : isChartDisk e) (hD : range e ⊆ B) (k : ℕ) :
    relativeHomology R (TopCat.of (B \ e '' diskInterior n : Set M)) (Subtype.val ⁻¹' (e '' diskSphere n)) k ≅
      relativeHomology R (TopCat.of B) (Subtype.val ⁻¹' (range e)) k := by
  have hS : e '' diskSphere n ⊆ B \ e '' diskInterior n := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨hD (mem_range_self v), ?_⟩
    intro h
    rw [he.injective.mem_set_image] at h
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv h
  have hcollar : range e \ e '' halfDisk n ⊆ B \ e '' halfDisk n := by
    rintro x ⟨hxD, hxK⟩
    exact ⟨hD hxD, hxK⟩
  have hsub : B \ e '' diskInterior n ⊆ B \ e '' halfDisk n :=
    sdiff_subset_sdiff_right (image_halfDisk_subset_image_diskInterior e)
  have hpair : (Subtype.val ⁻¹' (range e \ e '' halfDisk n) :
      Set (B \ e '' halfDisk n : Set M)) = Subtype.val ⁻¹' (range e) := by
    ext ⟨x, hx⟩
    exact and_iff_left hx.2
  have hset : (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B) =
      (Subtype.val ⁻¹' (e '' halfDisk n))ᶜ := by
    ext ⟨x, hx⟩
    exact and_iff_right hx
  have hexc : closure (Subtype.val ⁻¹' (e '' halfDisk n) : Set B) ⊆
      interior (Subtype.val ⁻¹' (range e)) := by
    rw [(he.isClosed_image_halfDisk.preimage continuous_subtype_val).closure_eq]
    exact (preimage_mono (image_halfDisk_subset_image_diskInterior e)).trans
      (interior_maximal (preimage_mono (image_subset_range _ _))
        (he.isOpen_image_diskInterior.preimage continuous_subtype_val))
  let φ₁ :
      relativeHomology R (TopCat.of (B \ e '' diskInterior n : Set M))
          (Subtype.val ⁻¹' (e '' diskSphere n)) k ≅
        relativeHomology R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e \ e '' halfDisk n)) k :=
    relativeHomologyIsoOfHomotopyEquivInclusion R hS hcollar hsub
      (image_diskSphere_subset_range_sdiff_halfDisk he)
      (he.isHomotopyEquivInclusion_sdiff_halfDisk hD)
      he.isHomotopyEquivInclusion_image_diskSphere k
  let φ₂ :
      relativeHomology R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e \ e '' halfDisk n)) k ≅
        relativeHomology R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e)) k :=
    relativeHomologyIsoOfEq R _ hpair k
  let φ₃ :
      relativeHomology R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e)) k ≅
        relativeHomology R (TopCat.of (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k :=
    (relativeHomologyIsoOfSubtypeSubtype R (show B \ e '' halfDisk n ⊆ B from sdiff_subset)
      (range e) k).symm
  let φ₄ :
      relativeHomology R (TopCat.of (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k ≅
        relativeHomology R (TopCat.of ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k :=
    relativeHomologyIsoOfHomeomorphMemIff R
      (Homeomorph.setCongr
        (s := (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
        (t := ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B)) hset)
      (A := Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e)))
      (B := Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e)))
      (fun _ => by exact Iff.rfl) k
  let φ₅ :
      relativeHomology R (TopCat.of ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k ≅
        relativeHomology R (TopCat.of B) (Subtype.val ⁻¹' (range e)) k :=
    excisionClosedIso R (X := TopCat.of B) (Subtype.val ⁻¹' (e '' halfDisk n))
      (Subtype.val ⁻¹' (range e)) hexc k
  exact φ₁ ≪≫ φ₂ ≪≫ φ₃ ≪≫ φ₄ ≪≫ φ₅

theorem isZero_relativeHomology_puncturedFilling (he : isChartDisk e) (hD : range e ⊆ B)
    (hB : acyclic R (TopCat.of B)) (k : ℕ) :
    IsZero (relativeHomology R (TopCat.of (B \ e '' diskInterior n : Set M))
      (Subtype.val ⁻¹' (e '' diskSphere n)) k) := by
  have : ContractibleSpace (Subtype.val ⁻¹' (range e) : Set B) := by
    have := he.contractibleSpace_range
    exact (homeomorphPreimageVal hD).contractibleSpace
  exact (isZero_relativeHomology_of_contractible_of_acyclic' R hB k).of_iso
    (relativeHomologyPuncturedFillingIso R he hD k)

theorem relHomologyVanishes_puncturedFilling (he : isChartDisk e) (hD : range e ⊆ B)
    (hB : acyclic integerCoefficients.{u} (TopCat.of B)) :
    relHomologyVanishes (B \ e '' diskInterior n : Set M) (Subtype.val ⁻¹' (e '' diskSphere n)) :=
  isZero_relativeHomology_puncturedFilling integerCoefficients he hD hB

end SingularPair

end DifferentialGeometry.Topology

end
