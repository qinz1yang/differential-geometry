import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothProjection
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Quotient
import DifferentialGeometry.Topology.Manifold.Quotient

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.HorosphereProjection

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open BusemannCocycle (poConfFactor)
open AsymptoticRays (rayTo rayTo_zero)

section

variable {n : ℕ} (hn : 1 ≤ n) (P : Subgroup (PO n 1)) (ξ : BoundaryH n)

local notation "Q" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)

theorem quotientRay_zero
    (hfix : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) (q : Q) :
    quotientRay hn P ξ hfix 0 q = q := by
  induction q using Quotient.inductionOn with
  | _ p => simp only [quotientRay_mk, rayTo_zero]

theorem quotientRay_add
    (hfix : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (s t : ℝ) (q : Q) :
    quotientRay hn P ξ hfix t (quotientRay hn P ξ hfix s q) =
      quotientRay hn P ξ hfix (s + t) q := by
  induction q using Quotient.inductionOn with
  | _ p => simp only [quotientRay_mk, rayTo_add]

theorem quotientBusemann_quotientRay
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (t : ℝ) (q : Q) :
    quotientBusemann hn P ξ hhor (quotientRay hn P ξ (fun γ => (hhor γ).1) t q) =
      quotientBusemann hn P ξ hhor q - t := by
  induction q using Quotient.inductionOn with
  | _ p => exact busemann_rayTo p ξ t

end

variable {m : ℕ} (P : Subgroup (PO (m + 1) 1))

local instance : MulAction P (HUpper (m + 1)) := EquivariantMap.subAction (by omega) P

local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

local instance (r : ℕ∞ω) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) r P (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m r (γ : PO (m + 1) 1)⟩

variable [ProperlyDiscontinuousSMul P (HUpper (m + 1))]
  [IsCancelSMul P (HUpper (m + 1))]
  (ξ : BoundaryH (m + 1))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))

theorem contMDiff_quotientBusemann
    (hhor : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ ∧
      poConfFactor (by omega) (γ : PO (m + 1) 1) ξ = 1) (r : ℕ∞ω) :
    ContMDiff I 𝓘(ℝ, ℝ) r (quotientBusemann (by omega) P ξ hhor) := by
  apply (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := r) I).contMDiff_of_comp_of_surjective Quotient.mk_surjective
  exact Busemann.contMDiff_busemann ξ r

theorem contMDiff_quotientRay
    (hfix : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ)
    (r : ℕ∞ω) :
    ContMDiff ((I).prod 𝓘(ℝ, ℝ)) I r
      (fun z : Q × ℝ => quotientRay (by omega) P ξ hfix z.2 z.1) := by
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := r) I
  rintro ⟨q, t⟩
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
  let L := (hπ p).localInverse
  have hl : ContMDiffAt ((I).prod 𝓘(ℝ, ℝ)) I r
      (fun z : Q × ℝ => L z.1) (π p, t) :=
    (hπ p).contMDiffAt_localInverse.comp (π p, t) contMDiffAt_fst
  have hs := hπ.contMDiff.contMDiffAt.comp (π p, t)
    ((contMDiff_rayTo ξ r).contMDiffAt.comp (π p, t) (hl.prodMk contMDiffAt_snd))
  apply hs.congr_of_eventuallyEq
  have he := (hπ p).localInverse_eventuallyEq_right
  have ht : Filter.Tendsto (Prod.fst : Q × ℝ → Q) (𝓝 (π p, t)) (𝓝 (π p)) :=
    continuous_fst.continuousAt
  filter_upwards [ht he] with z hz
  change quotientRay (by omega) P ξ hfix z.2 z.1 = π (rayTo (L z.1) ξ z.2)
  change π (L z.1) = z.1 at hz
  exact congrArg (quotientRay (by omega) P ξ hfix z.2) hz.symm

def quotientRayDiffeomorph
    (hfix : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ)
    (t : ℝ) (r : ℕ∞ω := ∞) : Q ≃ₘ^r⟮I, I⟯ Q where
  toFun := quotientRay (by omega) P ξ hfix t
  invFun := quotientRay (by omega) P ξ hfix (-t)
  left_inv q := by rw [quotientRay_add, add_neg_cancel, quotientRay_zero]
  right_inv q := by rw [quotientRay_add, neg_add_cancel, quotientRay_zero]
  contMDiff_toFun := (contMDiff_quotientRay P ξ hfix r).comp
    (contMDiff_id.prodMk contMDiff_const)
  contMDiff_invFun := (contMDiff_quotientRay P ξ hfix r).comp
    (contMDiff_id.prodMk contMDiff_const)

@[simp] theorem quotientRayDiffeomorph_apply_mk
    (hfix : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ)
    (t : ℝ) (r : ℕ∞ω) (p : HUpper (m + 1)) :
    quotientRayDiffeomorph P ξ hfix t r (π p) = π (rayTo p ξ t) := rfl

@[simp] theorem quotientRayDiffeomorph_symm_apply_mk
    (hfix : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ)
    (t : ℝ) (r : ℕ∞ω) (p : HUpper (m + 1)) :
    (quotientRayDiffeomorph P ξ hfix t r).symm (π p) = π (rayTo p ξ (-t)) := rfl

theorem contMDiff_quotient_retract
    (hhor : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ ∧
      poConfFactor (by omega) (γ : PO (m + 1) 1) ξ = 1) (c : ℝ) (r : ℕ∞ω) :
    ContMDiff I I r (fun q : Q => quotientRay (by omega) P ξ (fun γ => (hhor γ).1)
      (quotientBusemann (by omega) P ξ hhor q - c) q) := by
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := r) I
  apply hπ.contMDiff_of_comp_of_surjective Quotient.mk_surjective
  exact hπ.contMDiff.comp (contMDiff_retract ξ c r)

theorem mfderiv_quotientBusemann_ne_zero
    (hhor : ∀ γ : P, (poBoundaryMulAction (by omega)).smul (γ : PO (m + 1) 1) ξ = ξ ∧
      poConfFactor (by omega) (γ : PO (m + 1) 1) ξ = 1) (q : Q) :
    mfderiv I 𝓘(ℝ, ℝ) (quotientBusemann (by omega) P ξ hhor) q ≠ 0 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (G := P) (M := HUpper (m + 1)) (n := ∞) I
    have hd := mfderiv_comp («I» := I) (I' := I) (I'' := 𝓘(ℝ, ℝ)) p
      ((contMDiff_quotientBusemann P ξ hhor ∞).mdifferentiable (by simp) (π p))
      (hπ.contMDiff.mdifferentiable (by simp) p)
    intro hz
    apply Busemann.mfderiv_busemann_ne_zero ξ p
    change mfderiv I 𝓘(ℝ, ℝ) (quotientBusemann (by omega) P ξ hhor ∘ π) p = 0
    rw [hd, hz, ContinuousLinearMap.zero_comp]

end DifferentialGeometry.HorosphereProjection
