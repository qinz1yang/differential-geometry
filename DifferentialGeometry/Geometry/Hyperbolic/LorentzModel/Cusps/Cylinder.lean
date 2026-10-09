import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Truncation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Quotient
import DifferentialGeometry.Topology.GroupAction.Quotient

noncomputable section

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (poBoundaryMulAction)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere horoball)
open AsymptoticRays (rayTo)
open HorosphereProjection (retract retract_mem_horosphere)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer hn Γ (Set.singleton ξ.val)
local notation "πP" => Quotient.mk
  (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))
local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

def horoballQuotientHomeomorph :
    (πP '' horoball ξ.val (D.level ξ)) ≃ₜ
      (πP '' horosphere ξ.val (D.level ξ)) × Set.Ici (0 : ℝ) :=
  HorosphereProjection.quotientHoroballHomeomorph hn P ξ.val
    (CuspCrossSections.horospherical_endStabilizer hn Γ hΓ (D.region_nonempty ξ)) (D.level ξ)

@[simp] theorem horoballQuotientHomeomorph_apply_mk (p : HUpper n)
    (hp : p ∈ horoball ξ.val (D.level ξ)) :
    D.horoballQuotientHomeomorph hΓ ξ ⟨πP p, ⟨p, hp, rfl⟩⟩ =
      (⟨πP (retract ξ.val (D.level ξ) p),
        ⟨retract ξ.val (D.level ξ) p, retract_mem_horosphere ξ.val (D.level ξ) p, rfl⟩⟩,
        ⟨D.level ξ - busemann ξ.val p, by
          change 0 ≤ D.level ξ - busemann ξ.val p
          exact sub_nonneg.mpr hp⟩) := rfl

@[simp] theorem horoballQuotientHomeomorph_symm_apply_mk (p : HUpper n)
    (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : Set.Ici (0 : ℝ)) :
    ((D.horoballQuotientHomeomorph hΓ ξ).symm (⟨πP p, ⟨p, hp, rfl⟩⟩, t)).val =
      πP (rayTo p ξ.val t.val) := rfl

include hΓ in
theorem isCompact_quotient_horosphere (hdim : 2 ≤ n)
    [MeasureTheory.HasFundamentalDomain Γ (PO n 1)]
    (hcov : MeasureTheory.covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ p : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε p)) :
    IsCompact (πP '' horosphere ξ.val (D.level ξ)) :=
  CuspCrossSections.isCompact_quotient_horosphere hn hdim Γ hΓ hcov hr hre hgeom
    (D.region_nonempty ξ) (D.level ξ)

theorem isConnected_quotient_horosphere :
    IsConnected (πP '' horosphere ξ.val (D.level ξ)) :=
  HorosphereProjection.isConnected_image_quotient_horosphere hn P ξ.val (D.level ξ)

def horoballQuotientInclusion : C(πP '' horoball ξ.val (D.level ξ), QΓ) := by
  letI := EquivariantMap.subAction hn P
  letI := EquivariantMap.subAction hn Γ
  let f := (ContinuousMap.id (HUpper n)).orbitQuotientMap
    (Subgroup.inclusion (show P ≤ Γ from inf_le_left)) (by intro γ p; rfl)
  exact f.comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem horoballQuotientInclusion_apply_mk (p : HUpper n)
    (hp : p ∈ horoball ξ.val (D.level ξ)) :
    D.horoballQuotientInclusion ξ ⟨πP p, ⟨p, hp, rfl⟩⟩ = πΓ p := rfl

include hΓ in
theorem horoballQuotientInclusion_injective :
    Function.Injective (D.horoballQuotientInclusion ξ) := by
  rintro ⟨q, p, hp, rfl⟩ ⟨q', p', hp', rfl⟩ h
  change πΓ p = πΓ p' at h
  obtain ⟨γ, hγ⟩ := Quotient.exact h
  have hfix : (poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val = ξ.val := by
    by_contra hne
    have hdisjoint := (D.precisely_invariant hΓ ξ γ).2 hne
    exact Set.disjoint_left.mp hdisjoint ⟨p', hp', hγ⟩ hp
  apply Subtype.ext
  exact Quotient.sound ⟨⟨γ, (CuspCrossSections.mem_endStabilizer_singleton hn Γ ξ.val γ).mpr
    ⟨γ.property, hfix⟩⟩, hγ⟩

@[simp] theorem horoballQuotientInclusion_homeomorph_symm_apply_mk (p : HUpper n)
    (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : Set.Ici (0 : ℝ)) :
    D.horoballQuotientInclusion ξ
      ((D.horoballQuotientHomeomorph hΓ ξ).symm (⟨πP p, ⟨p, hp, rfl⟩⟩, t)) =
        πΓ (rayTo p ξ.val t.val) := rfl

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
