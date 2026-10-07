import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothCylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Cylinder

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Busemann (busemann horosphere)
open HorosphereProjection (retract retract_mem_horosphere)

variable {m : ℕ}

private local instance (P : Subgroup (PO (m + 1) 1)) : MulAction P (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) P

private local instance (P : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

variable {Γ : Subgroup (PO (m + 1) 1)} {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 m) Γ r)
  (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

local notation "P" => endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val)
local notation "Q" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))
local notation "hhor" => CuspCrossSections.horospherical_endStabilizer
  (Nat.le_add_left 1 m) Γ hΓ (D.region_nonempty ξ)
local notation "S" => (π '' horosphere ξ.val (D.level ξ))
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "K" => 𝓘(ℝ, Fin m → ℝ)
local notation "T" => (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi)

def openHoroballQuotient : TopologicalSpace.Opens Q :=
  HorosphereProjection.quotientOpenHoroball (Nat.le_add_left 1 m) P ξ.val hhor (D.level ξ)

@[simp] theorem openHoroballQuotient_coe :
    (D.openHoroballQuotient hΓ ξ : Set Q) =
      π '' {p : HUpper (m + 1) | busemann ξ.val p < D.level ξ} := rfl

variable [IsCancelSMul (endStabilizer (Nat.le_add_left 1 m) Γ (Set.singleton ξ.val))
  (HUpper (m + 1))]

@[instance_reducible] def horosphereQuotientChartedSpace : ChartedSpace (Fin m → ℝ) S := by
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
  exact HorosphereProjection.quotientHorosphereChartedSpace P ξ.val hhor (D.level ξ)

theorem isManifold_quotient_horosphere :
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    IsManifold K ∞ S := by
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
  exact HorosphereProjection.isManifold_quotient_horosphere P ξ.val hhor (D.level ξ)

def openHoroballQuotientDiffeomorph :
    let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
      (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    D.openHoroballQuotient hΓ ξ ≃ₘ⟮I, (K).prod 𝓘(ℝ, ℝ)⟯ S × T := by
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
    (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
  let _ := D.horosphereQuotientChartedSpace hΓ ξ
  exact HorosphereProjection.quotientOpenHoroballDiffeomorph P ξ.val hhor (D.level ξ)

@[simp] theorem openHoroballQuotientDiffeomorph_apply_mk (p : HUpper (m + 1))
    (hp : busemann ξ.val p < D.level ξ) :
    let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
      (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    D.openHoroballQuotientDiffeomorph hΓ ξ ⟨π p, ⟨p, hp, rfl⟩⟩ =
      (⟨π (retract ξ.val (D.level ξ) p),
        ⟨retract ξ.val (D.level ξ) p, retract_mem_horosphere ξ.val (D.level ξ) p, rfl⟩⟩,
        ⟨D.level ξ - busemann ξ.val p, sub_pos.mpr hp⟩) := rfl

theorem openHoroballQuotientDiffeomorph_symm_apply_mk (p : HUpper (m + 1))
    (hp : p ∈ horosphere ξ.val (D.level ξ)) (t : T) :
    let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
      (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    ((D.openHoroballQuotientDiffeomorph hΓ ξ).symm
      (⟨π p, ⟨p, hp, rfl⟩⟩, t)).val = π (AsymptoticRays.rayTo p ξ.val t.val) := rfl

theorem openHoroballQuotientDiffeomorph_symm_eq_horoballQuotientHomeomorph_symm (z : S × T) :
    let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
      (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    ((D.openHoroballQuotientDiffeomorph hΓ ξ).symm z).val =
      ((D.horoballQuotientHomeomorph hΓ ξ).symm
        (z.1, ⟨z.2.val, (show 0 < z.2.val from z.2.property).le⟩)).val := rfl

@[simp] theorem openHoroballQuotientDiffeomorph_depth (q : D.openHoroballQuotient hΓ ξ) :
    let _ := OrbifoldCompactness.properlyDiscontinuous_subAction
      (Nat.le_add_left 1 m) P (hΓ.mono inf_le_left)
    let _ := D.horosphereQuotientChartedSpace hΓ ξ
    (D.openHoroballQuotientDiffeomorph hΓ ξ q).2.val = D.level ξ -
      HorosphereProjection.quotientBusemann (Nat.le_add_left 1 m) P ξ.val hhor q.val := rfl

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
