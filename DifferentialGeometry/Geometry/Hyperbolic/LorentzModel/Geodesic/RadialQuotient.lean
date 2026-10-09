import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.RadialFlow
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ShortDisplacementCompactness
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1))

local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction (by omega) Γ

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "q" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))

variable (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)
  (hpair : ∀ γ : Γ,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))))

def quotientAxisRadialFlow (hpair : ∀ γ : Γ,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1)))) (t : ℝ) : Q → Q :=
  Quotient.map (axisRadialFlow ξ η hne t) fun x y hxy => by
    obtain ⟨γ, hγ⟩ := hxy
    change (poMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) y = x at hγ
    refine ⟨γ, ?_⟩
    change (poMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1)
      (axisRadialFlow ξ η hne t y) = axisRadialFlow ξ η hne t x
    rw [← axisRadialFlow_smul (by omega) γ ξ η hne (hpair γ), hγ]

@[simp] theorem quotientAxisRadialFlow_mk (t : ℝ) (y : HUpper (m + 1)) :
    quotientAxisRadialFlow m Γ ξ η hne hpair t (q y) = q (axisRadialFlow ξ η hne t y) := rfl

theorem quotientAxisRadialFlow_zero (y : Q) : quotientAxisRadialFlow m Γ ξ η hne hpair 0 y = y := by
  induction y using Quotient.inductionOn with
  | _ y => rw [quotientAxisRadialFlow_mk, axisRadialFlow_zero]

theorem quotientAxisRadialFlow_add (s t : ℝ) (y : Q) :
    quotientAxisRadialFlow m Γ ξ η hne hpair s (quotientAxisRadialFlow m Γ ξ η hne hpair t y) =
      quotientAxisRadialFlow m Γ ξ η hne hpair (s + t) y := by
  induction y using Quotient.inductionOn with
  | _ y => simp only [quotientAxisRadialFlow_mk, axisRadialFlow_add]

private def axisDistanceFun (y : HUpper (m + 1)) : ℝ := dist y (axisFoot ξ η hne y)

include hpair in
private theorem axisDistanceFun_eq_of_orbitRel (x y : HUpper (m + 1))
    (hxy : MulAction.orbitRel Γ (HUpper (m + 1)) x y) :
    axisDistanceFun m ξ η hne x = axisDistanceFun m ξ η hne y := by
  obtain ⟨γ, hγ⟩ := hxy
  change (poMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) y = x at hγ
  have h := dist_axisFoot_smul (n := m + 1) (by omega) (γ : PO (m + 1) 1) ξ η hne (hpair γ) y
  change axisDistanceFun m ξ η hne ((poMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) y) =
    axisDistanceFun m ξ η hne y at h
  rw [hγ] at h
  exact h

def quotientAxisDistance (hpair : ∀ γ : Γ,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1)))) : Q → ℝ :=
  Quotient.lift (axisDistanceFun m ξ η hne)
    (axisDistanceFun_eq_of_orbitRel m Γ ξ η hne hpair)

@[simp] theorem quotientAxisDistance_mk (y : HUpper (m + 1)) :
    quotientAxisDistance m Γ ξ η hne hpair (q y) = dist y (axisFoot ξ η hne y) := rfl

theorem sinh_quotientAxisDistance_quotientAxisRadialFlow (t : ℝ) (y : Q) :
    Real.sinh (quotientAxisDistance m Γ ξ η hne hpair
      (quotientAxisRadialFlow m Γ ξ η hne hpair t y)) =
        Real.exp t * Real.sinh (quotientAxisDistance m Γ ξ η hne hpair y) := by
  induction y using Quotient.inductionOn with
  | _ y => exact sinh_dist_axisFoot_axisRadialFlow ξ η hne t y

theorem quotientAxisDistance_eq_zero_iff_mem_image_axis (z : Q) :
    quotientAxisDistance m Γ ξ η hne hpair z = 0 ↔ z ∈ q '' axis ξ η := by
  constructor
  · induction z using Quotient.inductionOn with
    | _ y =>
        intro hy
        have heq : y = axisFoot ξ η hne y := dist_eq_zero.mp hy
        exact ⟨y, heq.symm ▸ axisFoot_mem ξ η hne y, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [quotientAxisDistance_mk, axisFoot_eq_self ξ η hne hy, dist_self]

theorem quotientAxisRadialFlow_mem_image_axis_iff (t : ℝ) (z : Q) :
    quotientAxisRadialFlow m Γ ξ η hne hpair t z ∈ q '' axis ξ η ↔ z ∈ q '' axis ξ η := by
  rw [← quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair,
    ← quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair]
  induction z using Quotient.inductionOn with
  | _ y =>
      simp only [quotientAxisRadialFlow_mk, quotientAxisDistance_mk, dist_eq_zero]
      constructor
      · intro heq
        have hym := (axisRadialFlow_mem_axis_iff ξ η hne t y).mp
          (heq.symm ▸ axisFoot_mem ξ η hne (axisRadialFlow ξ η hne t y))
        exact (axisFoot_eq_self ξ η hne hym).symm
      · intro heq
        have hym : y ∈ axis ξ η := heq.symm ▸ axisFoot_mem ξ η hne y
        exact (axisFoot_eq_self ξ η hne ((axisRadialFlow_mem_axis_iff ξ η hne t y).mpr hym)).symm

theorem log_sinh_quotientAxisDistance_quotientAxisRadialFlow (t : ℝ) {z : Q}
    (hz : z ∉ q '' axis ξ η) :
    Real.log (Real.sinh (quotientAxisDistance m Γ ξ η hne hpair
      (quotientAxisRadialFlow m Γ ξ η hne hpair t z))) =
        Real.log (Real.sinh (quotientAxisDistance m Γ ξ η hne hpair z)) + t := by
  induction z using Quotient.inductionOn with
  | _ y =>
      exact log_sinh_dist_axisFoot_axisRadialFlow ξ η hne t
        (fun hy => hz ⟨y, hy, rfl⟩)

section Smooth

variable (hΓ : IsDiscrete (SetLike.coe Γ)) [IsCancelSMul Γ (HUpper (m + 1))]

local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

local instance : ContMDiffConstSMul I ∞ Γ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

theorem contMDiff_quotientAxisRadialFlow :
    letI : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
      OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) Γ hΓ
    ContMDiff ((I).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : Q × ℝ => quotientAxisRadialFlow m Γ ξ η hne hpair z.2 z.1) := by
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) Γ hΓ
  have hq : IsLocalDiffeomorph I I ∞ (q : HUpper (m + 1) → Q) :=
    MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I
  have hqp := PDE.RicciFlow.Perelman.KappaSolutions.isLocalDiffeomorph_prod_real q hq
  apply hqp.contMDiff_of_comp_of_surjective
    (show Function.Surjective (fun z : HUpper (m + 1) × ℝ => (q z.1, z.2)) from by
      rintro ⟨y, t⟩
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
      exact ⟨(x, t), rfl⟩)
  have hswap : ContMDiff ((I).prod 𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun z : HUpper (m + 1) × ℝ => (z.2, z.1)) := contMDiff_snd.prodMk contMDiff_fst
  exact hq.contMDiff.comp ((contMDiff_axisRadialFlow ξ η hne ∞).comp hswap)

theorem contMDiffOn_quotientAxisDistance :
    letI : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
      OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) Γ hΓ
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (quotientAxisDistance m Γ ξ η hne hpair)
      {z : Q | quotientAxisDistance m Γ ξ η hne hpair z ≠ 0} := by
  let _ := OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) Γ hΓ
  have hq : IsLocalDiffeomorph I I ∞ (q : HUpper (m + 1) → Q) :=
    MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I
  intro z hz
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective z
  have hy : y ∉ axis ξ η := by
    intro hy
    apply hz
    rw [quotientAxisDistance_mk, axisFoot_eq_self ξ η hne hy, dist_self]
  have hc := (contMDiffOn_dist_axisFoot ξ η hne ∞ y hy).contMDiffAt
    ((isClosed_axis ξ η).isOpen_compl.mem_nhds hy)
  apply ContMDiffAt.contMDiffWithinAt
  apply (hq y).contMDiffAt_of_comp
  exact hc

end Smooth

end DifferentialGeometry.AxisGeometry
