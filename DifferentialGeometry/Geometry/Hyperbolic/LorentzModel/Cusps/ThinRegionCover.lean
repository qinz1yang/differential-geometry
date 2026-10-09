import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Core
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionQuotient

open Set

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))

local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

include hΓ in
theorem exists_label_of_isCompact_compl_iUnion_thin_regions
    {ι : Type*} (S : ι → Set (BoundaryH n)) (U : ι → Set QΓ)
    (hU : ∀ i, U i ⊆ πΓ '' OrbifoldThinRegions.thinRegion hn Γ r (S i))
    (hcompact : IsCompact (⋃ i, U i)ᶜ) (ξ : D.centers) :
    ∃ (i : ι) (γ : Γ),
      (fun η : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) η) ''
        {ξ.val} = S i := by
  let e := D.horoballCylinderMap hΓ ξ
  have he : _root_.Topology.IsClosedEmbedding e := D.horoballCylinderMap_isClosedEmbedding hΓ ξ
  have hc := he.isCompact_preimage hcompact
  obtain ⟨B, hB⟩ := (hc.image (continuous_subtype_val.comp continuous_snd)).bddAbove
  obtain ⟨c, hc⟩ := (D.isConnected_quotient_horosphere ξ).nonempty
  let t : Ici (0 : ℝ) := ⟨max B 0 + 1, by
    change 0 ≤ max B 0 + 1
    linarith [le_max_right B 0]⟩
  have hout : e (⟨c, hc⟩, t) ∉ (⋃ i, U i)ᶜ := by
    intro hin
    have hb := hB ⟨(⟨c, hc⟩, t), hin, rfl⟩
    change max B 0 + 1 ≤ B at hb
    linarith [le_max_left B 0]
  obtain ⟨i, hi⟩ := mem_iUnion.mp (not_not.mp hout)
  have hethin : e (⟨c, hc⟩, t) ∈ πΓ '' OrbifoldThinRegions.thinRegion hn Γ r {ξ.val} := by
    have hrange : e (⟨c, hc⟩, t) ∈ range (D.horoballCylinderMap hΓ ξ) :=
      ⟨(⟨c, hc⟩, t), rfl⟩
    rw [D.range_horoballCylinderMap hΓ ξ] at hrange
    exact Set.image_mono ((D.horoball_inside ξ).trans interior_subset) hrange
  obtain ⟨γ, hγ⟩ := OrbifoldThinRegions.label_orbit_of_mem_quotient_thinRegion
    hn Γ hΓ r hethin (hU i hi)
  exact ⟨i, γ, hγ⟩

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
