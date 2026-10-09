import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Core
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.MatchedTruncations

noncomputable section

open Set

namespace DifferentialGeometry.CuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open HyperbolicAction (poMulAction)
open Busemann (busemann horoball horosphere)

theorem image_truncatedSet {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) :
    let π := Quotient.mk
      (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
    π '' truncatedSet hn Γ A c = (⋃ ξ : A, π '' {p | busemann ξ.val p < c ξ})ᶜ := by
  dsimp only
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩ hq
    obtain ⟨ξ, s, hs, hsq⟩ := mem_iUnion.mp hq
    obtain ⟨γ, hγ⟩ := Quotient.exact (hpq.trans hsq.symm)
    exact hp (mem_iUnion.mpr ⟨ξ, mem_iUnion.mpr ⟨γ, s, hs, hγ⟩⟩)
  · intro hq
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    refine ⟨p, ?_, rfl⟩
    intro hp
    obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hp
    obtain ⟨γ, s, hs, hsp⟩ := mem_iUnion.mp hξ
    apply hq
    have hps : Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _
        (EquivariantMap.subAction hn Γ)) p = Quotient.mk
        (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ)) s :=
      Quotient.sound ⟨γ, hsp⟩
    exact mem_iUnion.mpr ⟨ξ, s, hs, hps.symm⟩

theorem truncatedSet_antitone {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) : Antitone (truncatedSet hn Γ A) := by
  intro c d hcd p hp hc
  obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hc
  obtain ⟨γ, x, hx, hxp⟩ := mem_iUnion.mp hξ
  exact hp (mem_iUnion.mpr ⟨ξ, mem_iUnion.mpr ⟨γ, x, lt_of_lt_of_le hx (hcd ξ), hxp⟩⟩)

namespace FiniteCuspTruncation

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))

local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))

theorem horoballCylinderMap_image_gt (ξ : D.centers) (R : ℝ) (hR : 0 ≤ R) :
    D.horoballCylinderMap hΓ ξ '' {z | R < z.2.val} =
      πΓ '' {p | busemann ξ.val p < D.level ξ - R} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨q, p, hp, rfl⟩, t⟩, ht, rfl⟩
    refine ⟨AsymptoticRays.rayTo p ξ.val t.val, ?_, rfl⟩
    change busemann ξ.val (AsymptoticRays.rayTo p ξ.val t.val) < D.level ξ - R
    rw [HorosphereProjection.busemann_rayTo,
      show busemann ξ.val p = D.level ξ from hp]
    exact sub_lt_sub_left ht _
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : busemann ξ.val p < D.level ξ - R := hp
    let P := CuspCrossSections.endStabilizer hn Γ {ξ.val}
    let πP := Quotient.mk
      (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
    let q : πP '' horoball ξ.val (D.level ξ) := ⟨πP p, ⟨p, by
      change busemann ξ.val p ≤ D.level ξ
      linarith, rfl⟩⟩
    refine ⟨D.horoballQuotientHomeomorph hΓ ξ q, ?_, ?_⟩
    · change R < D.level ξ - busemann ξ.val p
      linarith
    · change D.horoballQuotientInclusion ξ
        ((D.horoballQuotientHomeomorph hΓ ξ).symm
          (D.horoballQuotientHomeomorph hΓ ξ q)) = πΓ p
      rw [Homeomorph.symm_apply_apply]
      rfl

theorem cylindricalCore_eq_image_truncatedSet (R : D.centers → ℝ)
    (hR : ∀ ξ, 0 ≤ R ξ) :
    Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R =
      πΓ '' truncatedSet hn Γ D.centers (fun ξ => D.level ξ - R ξ) := by
  unfold Topology.cylindricalCore
  rw [image_truncatedSet]
  congr 1
  apply iUnion_congr
  intro ξ
  exact D.horoballCylinderMap_image_gt hΓ ξ (R ξ) (hR ξ)

variable (hdim : 2 ≤ n) [MeasureTheory.HasFundamentalDomain Γ (PO n 1)]
  (hcov : MeasureTheory.covolume Γ (PO n 1) ≠ ⊤)
  {ε : ℝ} (hr : 0 < r) (hre : r < ε)
  (hgeom : ∀ p : HUpper n,
    BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε p))

def retruncate (c : D.centers → ℝ) (hc : ∀ ξ, c ξ ≤ D.level ξ) :
    FiniteCuspTruncation hn Γ r := by
  classical
  have hex := MatchedCusps.exists_compact_retruncated_core hn hdim Γ hΓ hcov hr hre hgeom
    D D.centers c (fun ξ => ⟨1, by
      change HyperbolicBoundary.poBoundaryPermHom hn (1 : PO n 1) ξ.val ∈ D.centers
      rw [map_one]
      exact ξ.property⟩)
  let K := Classical.choose hex
  have hK := Classical.choose_spec hex
  refine
    { centers := D.centers
      finite_centers := D.finite_centers
      level := c
      region_nonempty := D.region_nonempty
      horoball_inside := fun ξ p hp => D.horoball_inside ξ (le_trans hp (hc ξ))
      distinct_orbits := D.distinct_orbits
      covers_centers := D.covers_centers
      core := D.core ∪ K
      compact_core := D.compact_core.union hK.1
      core_subset := union_subset
        (D.core_subset.trans (truncatedSet_antitone hn Γ D.centers hc)) hK.2.1
      covers_truncated := ?_ }
  intro p hp
  obtain ⟨γ, hγ⟩ := hK.2.2 p hp
  exact ⟨γ, Or.inr hγ⟩

theorem core_subset_retruncate_core (c : D.centers → ℝ) (hc : ∀ ξ, c ξ ≤ D.level ξ) :
    D.core ⊆ (D.retruncate hΓ hdim hcov hr hre hgeom c hc).core :=
  subset_union_left

end FiniteCuspTruncation
end DifferentialGeometry.CuspTruncation
