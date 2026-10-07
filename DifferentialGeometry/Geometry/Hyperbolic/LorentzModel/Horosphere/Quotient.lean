import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.ContinuousAction
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

namespace DifferentialGeometry.HorosphereProjection

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open BusemannCocycle (poConfFactor)
open AsymptoticRays (rayTo rayTo_zero)
open Busemann (busemann horosphere horoball)

variable {n : ℕ} (hn : 1 ≤ n)

variable (P : Subgroup (PO n 1)) (ξ : BoundaryH n)

local notation "Q" => @MulAction.orbitRel.Quotient P (HUpper n) _ (EquivariantMap.subAction hn P)
local notation "π" => Quotient.mk (@MulAction.orbitRel P (HUpper n) _ (EquivariantMap.subAction hn P))

def quotientRay (hfix : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (t : ℝ) : Q → Q :=
  Quotient.map (fun p => rayTo p ξ t) fun p q hpq => by
    obtain ⟨γ, hγ⟩ := hpq
    refine ⟨γ, ?_⟩
    change (poMulAction hn).smul (γ : PO n 1) (rayTo q ξ t) = rayTo p ξ t
    have he := BoundaryExtension.po_smul_rayTo hn (γ : PO n 1) q ξ t
    change (poMulAction hn).smul (γ : PO n 1) (rayTo q ξ t) =
      rayTo ((poMulAction hn).smul (γ : PO n 1) q)
        ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ) t at he
    rw [hfix γ] at he
    exact he.trans (congrArg (fun z => rayTo z ξ t) hγ)

@[simp] theorem quotientRay_mk
    (hfix : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (t : ℝ) (p : HUpper n) :
    quotientRay hn P ξ hfix t (π p) =
      π (rayTo p ξ t) := rfl

theorem continuous_quotientRay
    (hfix : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) :
    Continuous (fun z : ℝ × Q =>
      quotientRay hn P ξ hfix z.1 z.2) := by
  let := EquivariantMap.subAction hn P
  let : ContinuousConstSMul P (HUpper n) :=
    ⟨fun γ => (ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id)⟩
  have hq := MulAction.isOpenQuotientMap_quotientMk (Γ := P) (T := HUpper n)
  have hp := (IsOpenQuotientMap.id (X := ℝ)).prodMap hq
  rw [← hp.continuous_comp_iff]
  exact continuous_quotient_mk'.comp
    ((continuous_rayTo ξ).comp (continuous_snd.prodMk continuous_fst))

private theorem busemann_smul
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (γ : P) (p : HUpper n) :
    busemann ξ ((poMulAction hn).smul (γ : PO n 1) p) = busemann ξ p := by
  have h := BusemannCocycle.po_busemann_smul hn (γ : PO n 1) ξ p
  simpa only [(hhor γ).1, (hhor γ).2, Real.log_one, sub_zero] using h

def quotientBusemann
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) :
    Q → ℝ :=
  Quotient.lift (busemann ξ) fun p q hpq => by
    obtain ⟨γ, hγ⟩ := hpq
    rw [← hγ]
    exact busemann_smul hn P ξ hhor γ q

@[simp] theorem quotientBusemann_mk
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (p : HUpper n) :
    quotientBusemann hn P ξ hhor (π p) =
      busemann ξ p := rfl

theorem continuous_quotientBusemann
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) :
    Continuous (quotientBusemann hn P ξ hhor) :=
  continuous_quot_lift _ (continuous_busemann ξ)

theorem mem_image_horoball_iff_quotientBusemann_le
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ)
    (q : Q) :
    q ∈ π '' horoball ξ c ↔
      quotientBusemann hn P ξ hhor q ≤ c := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · induction q using Quotient.inductionOn with
    | _ p => exact fun hp => ⟨p, hp, rfl⟩

def quotientHorosphereHomeomorph
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ) :
    Q ≃ₜ
      (π '' horosphere ξ c) × ℝ := by
  let hfix := fun γ : P => (hhor γ).1
  let R := fun q : Q =>
    quotientRay hn P ξ hfix (quotientBusemann hn P ξ hhor q - c) q
  have hR (q : Q) :
      R q ∈ π '' horosphere ξ c := by
    induction q using Quotient.inductionOn with
    | _ p => exact ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩
  refine
    { toFun := fun q => (⟨R q, hR q⟩, c - quotientBusemann hn P ξ hhor q)
      invFun := fun z => quotientRay hn P ξ hfix z.2 z.1.val
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      change Quotient.mk _ (rayTo (retract ξ c p) ξ (c - busemann ξ p)) = Quotient.mk _ p
      rw [retract, rayTo_add, sub_add_sub_cancel, sub_self, rayTo_zero]
  · rintro ⟨⟨q, p, hp, rfl⟩, t⟩
    apply Prod.ext
    · apply Subtype.ext
      change Quotient.mk _ (retract ξ c (rayTo p ξ t)) = Quotient.mk _ p
      rw [retract_rayTo, retract_eq_self ξ c hp]
    · change c - busemann ξ (rayTo p ξ t) = t
      rw [busemann_rayTo, show busemann ξ p = c from hp]
      ring
  · exact ((continuous_quotientRay hn P ξ hfix).comp
      (((continuous_quotientBusemann hn P ξ hhor).sub continuous_const).prodMk
        continuous_id)).subtype_mk hR |>.prodMk
          (continuous_const.sub (continuous_quotientBusemann hn P ξ hhor))
  · exact (continuous_quotientRay hn P ξ hfix).comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))

@[simp] theorem quotientHorosphereHomeomorph_apply_mk
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ) (p : HUpper n) :
    quotientHorosphereHomeomorph hn P ξ hhor c (π p) =
      (⟨π (retract ξ c p),
        ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩⟩, c - busemann ξ p) := rfl

@[simp] theorem quotientHorosphereHomeomorph_symm_apply_mk
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ) (p : HUpper n)
    (hp : p ∈ horosphere ξ c) (t : ℝ) :
    (quotientHorosphereHomeomorph hn P ξ hhor c).symm
      (⟨π p, ⟨p, hp, rfl⟩⟩, t) =
        π (rayTo p ξ t) := rfl

def quotientHoroballHomeomorph
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ) :
    (π '' horoball ξ c) ≃ₜ (π '' horosphere ξ c) × Set.Ici (0 : ℝ) := by
  let e := quotientHorosphereHomeomorph hn P ξ hhor c
  refine
    { toFun := fun q => ((e q.val).1, ⟨(e q.val).2, ?_⟩)
      invFun := fun z => ⟨e.symm (z.1, z.2.val), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change 0 ≤ c - quotientBusemann hn P ξ hhor q.val
    exact sub_nonneg.mpr
      ((mem_image_horoball_iff_quotientBusemann_le hn P ξ hhor c q.val).mp q.property)
  · apply (mem_image_horoball_iff_quotientBusemann_le hn P ξ hhor c _).mpr
    have h := congrArg Prod.snd (e.apply_symm_apply (z.1, z.2.val))
    change c - quotientBusemann hn P ξ hhor (e.symm (z.1, z.2.val)) = z.2.val at h
    have ht : 0 ≤ z.2.val := z.2.property
    linarith
  · intro q
    apply Subtype.ext
    exact e.symm_apply_apply q.val
  · intro z
    apply Prod.ext
    · change (e (e.symm (z.1, z.2.val))).1 = z.1
      exact congrArg Prod.fst (e.apply_symm_apply (z.1, z.2.val))
    · apply Subtype.ext
      change (e (e.symm (z.1, z.2.val))).2 = z.2.val
      exact congrArg Prod.snd (e.apply_symm_apply (z.1, z.2.val))
  · exact (e.continuous.comp continuous_subtype_val).fst.prodMk
      ((e.continuous.comp continuous_subtype_val).snd.subtype_mk _)
  · exact (e.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem quotientHoroballHomeomorph_apply_mk
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ)
    (p : HUpper n) (hp : p ∈ horoball ξ c) :
    quotientHoroballHomeomorph hn P ξ hhor c ⟨π p, ⟨p, hp, rfl⟩⟩ =
      (⟨π (retract ξ c p), ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩⟩,
        ⟨c - busemann ξ p, by change 0 ≤ c - busemann ξ p; exact sub_nonneg.mpr hp⟩) := rfl

@[simp] theorem quotientHoroballHomeomorph_symm_apply_mk
    (hhor : ∀ γ : P, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1) (c : ℝ)
    (p : HUpper n) (hp : p ∈ horosphere ξ c) (t : Set.Ici (0 : ℝ)) :
    ((quotientHoroballHomeomorph hn P ξ hhor c).symm
      (⟨π p, ⟨p, hp, rfl⟩⟩, t)).val = π (rayTo p ξ t.val) := rfl

theorem isConnected_image_quotient_horosphere (c : ℝ) :
    IsConnected (π '' horosphere ξ c) := by
  let : PathConnectedSpace (HUpper n) := HyperbolicGeodesic.pathConnectedSpace hn
  have heq : π '' horosphere ξ c =
      Set.range (fun p => π (retract ξ c p)) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, congrArg (Quotient.mk _) (retract_eq_self ξ c hp)⟩
    · rintro ⟨p, rfl⟩
      exact ⟨retract ξ c p, retract_mem_horosphere ξ c p, rfl⟩
  rw [heq]
  exact isConnected_range (continuous_quotient_mk'.comp (continuous_retract ξ c))

end DifferentialGeometry.HorosphereProjection
