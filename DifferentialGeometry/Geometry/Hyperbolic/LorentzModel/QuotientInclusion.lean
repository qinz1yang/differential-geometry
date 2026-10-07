import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence
import DifferentialGeometry.Topology.Manifold.QuotientMap

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.EquivariantMap

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {n : ℕ} (hn : 1 ≤ n) {P Γ : Subgroup (PO n 1)} (hP : P ≤ Γ)

local notation "QP" => @MulAction.orbitRel.Quotient P (HUpper n) _ (subAction hn P)
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _ (subAction hn Γ)
local notation "πP" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (subAction hn P))
local notation "πΓ" => Quotient.mk (@MulAction.orbitRel Γ (HUpper n) _ (subAction hn Γ))

def quotientInclusion : C(QP, QΓ) := by
  let _ := subAction hn P
  let _ := subAction hn Γ
  exact (ContinuousMap.id (HUpper n)).orbitQuotientMap (Subgroup.inclusion hP) (fun _ _ => rfl)

@[simp] theorem quotientInclusion_apply_mk (p : HUpper n) :
    quotientInclusion hn hP (πP p) = πΓ p := rfl

theorem quotientInclusion_image (A : Set (HUpper n)) :
    quotientInclusion hn hP '' (πP '' A) = πΓ '' A := by
  rw [Set.image_image]
  rfl

include hP in
theorem isCancelSMul_subAction
    [hfree : @IsCancelSMul Γ (HUpper n) (subAction hn Γ).toSMul] :
    @IsCancelSMul P (HUpper n) (subAction hn P).toSMul := by
  let _ := subAction hn P
  let _ := subAction hn Γ
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro γ p hp
  have he : (Subgroup.inclusion hP γ : Γ) = 1 := IsCancelSMul.eq_one_of_smul hp
  exact Subtype.ext (congrArg (fun δ : Γ => (δ : PO n 1)) he)

end DifferentialGeometry.EquivariantMap

namespace DifferentialGeometry.EquivariantMap

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {m : ℕ} {P Γ : Subgroup (PO (m + 1) 1)} (hP : P ≤ Γ)

private local instance (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  subAction (Nat.le_add_left 1 m) Δ

private local instance (Δ : Subgroup (PO (m + 1) 1)) : ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

private local instance (Δ : Subgroup (PO (m + 1) 1)) (r : ℕ∞ω) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) r Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m r (γ : PO (m + 1) 1)⟩

variable [ProperlyDiscontinuousSMul P (HUpper (m + 1))]
  [ProperlyDiscontinuousSMul Γ (HUpper (m + 1))]
  [IsCancelSMul Γ (HUpper (m + 1))]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))

theorem isLocalDiffeomorph_quotientInclusion (r : ℕ∞ω) :
    let _ := isCancelSMul_subAction (Nat.le_add_left 1 m) hP
    IsLocalDiffeomorph I I r (quotientInclusion (Nat.le_add_left 1 m) hP) := by
  let _ := isCancelSMul_subAction (Nat.le_add_left 1 m) hP
  exact ContinuousMap.isLocalDiffeomorph_orbitQuotientMap
    (ContinuousMap.id (HUpper (m + 1))) (Subgroup.inclusion hP) (fun _ _ => rfl)
    (Diffeomorph.refl I (HUpper (m + 1)) r).isLocalDiffeomorph

end DifferentialGeometry.EquivariantMap
