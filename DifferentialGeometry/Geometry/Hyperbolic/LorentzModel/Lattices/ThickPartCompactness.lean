/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence
import Mathlib.Order.CompletePartialOrder
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.ThickPartCompactness

noncomputable section

open Set Filter Function MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Pointwise Topology ENNReal

namespace DifferentialGeometry.LatticeCompactness

section Hyperbolic

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicTransitive

variable {n : ℕ}

theorem exists_compact_cover_thick_frames (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [hfd : HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) {U : Set (PO n 1)} (hU : U ∈ 𝓝 1) :
    ∃ C : Set (PO n 1), IsCompact C ∧
      ∀ g ∈ thickSet Γ U, ∃ γ : Γ, (γ : PO n 1) * g ∈ C := by
  let : Countable Γ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Γ disc
  let : T2Space (PO n 1) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t2Space_PO hn
  let : InnerRegularCompactLTTop (volume : Measure (PO n 1)) := by
    change InnerRegularCompactLTTop (Measure.haar : Measure (PO n 1))
    infer_instance
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  exact exists_compact_cover_thickSet hF
    (by rwa [← hF.covolume_eq_volume volume]) hU

def thickPart (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (HUpper n) :=
  {x | ∀ γ : Γ, γ ≠ 1 →
    ε ≤ dist x ((poMulAction hn).smul (γ : PO n 1) x)}

def shortDisplacement (hn : 1 ≤ n) (ε : ℝ) : Set (PO n 1) :=
  {g | dist basepointH ((poMulAction hn).smul g basepointH) < ε}

theorem continuous_displacement (hn : 1 ≤ n) (a : PO n 1) :
    Continuous (fun x : HUpper n => dist x ((poMulAction hn).smul a x)) :=
  continuous_id.dist ((ContinuousAction.continuous_po_smul hn).comp
    (continuous_const.prodMk continuous_id))

theorem isOpen_shortDisplacement (hn : 1 ≤ n) (ε : ℝ) :
    IsOpen (shortDisplacement hn ε) :=
  isOpen_lt (continuous_const.dist ((ContinuousAction.continuous_po_smul hn).comp
    (continuous_id.prodMk continuous_const))) continuous_const

theorem shortDisplacement_mem_nhds (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    shortDisplacement hn ε ∈ 𝓝 (1 : PO n 1) := by
  apply (isOpen_shortDisplacement hn ε).mem_nhds
  change dist basepointH ((poMulAction hn).smul 1 basepointH) < ε
  have h1 : (poMulAction hn).smul (1 : PO n 1) (basepointH : HUpper n) = basepointH :=
    (poMulAction hn).one_smul _
  rw [h1, dist_self]
  exact hε

theorem isClosed_thickPart (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) :
    IsClosed (thickPart hn Γ ε) := by
  have hset : thickPart hn Γ ε = ⋂ γ : Γ, ⋂ (_ : γ ≠ 1),
      {x : HUpper n | ε ≤ dist x ((poMulAction hn).smul (γ : PO n 1) x)} := by
    ext x
    simp only [thickPart, mem_ofPred_eq, mem_iInter]
  rw [hset]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_displacement hn γ)

theorem displacement_conj (hn : 1 ≤ n) (g a : PO n 1) (x : HUpper n) :
    dist ((poMulAction hn).smul g x)
        ((poMulAction hn).smul a ((poMulAction hn).smul g x))
      = dist x ((poMulAction hn).smul (g⁻¹ * a * g) x) := by
  let := poMulAction hn
  change dist (g • x) (a • (g • x)) = dist x ((g⁻¹ * a * g) • x)
  have h := po_dist_smul hn g x ((g⁻¹ * a * g) • x)
  simpa only [smul_smul, mul_assoc, mul_inv_cancel_left] using h

theorem smul_mem_thickPart (hn : 1 ≤ n) {Γ : Subgroup (PO n 1)} {ε : ℝ}
    {x : HUpper n} (hx : x ∈ thickPart hn Γ ε) (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) x ∈ thickPart hn Γ ε := by
  intro γ hγ
  rw [displacement_conj]
  apply hx (δ⁻¹ * γ * δ)
  intro h
  apply hγ
  have h' := congrArg (fun a : Γ => δ * a * δ⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel_left, mul_one,
    mul_inv_cancel_left] using h'

theorem mem_thickSet_shortDisplacement_iff (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (g : PO n 1) :
    g ∈ thickSet Γ (shortDisplacement hn ε) ↔
      (poMulAction hn).smul g basepointH ∈ thickPart hn Γ ε := by
  constructor
  · intro hg γ hγ
    rw [displacement_conj]
    exact le_of_not_gt (fun h => hγ (hg γ h))
  · intro hx γ hγ
    by_contra hne
    have h := hx γ hne
    rw [displacement_conj] at h
    exact (not_lt_of_ge h) hγ

theorem exists_compact_thickPart_core (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ thickPart hn Γ ε ∧
      ∀ x ∈ thickPart hn Γ ε, ∃ γ : Γ,
        (poMulAction hn).smul (γ : PO n 1) x ∈ K := by
  let := poMulAction hn
  obtain ⟨C, hC, hcover⟩ :=
    exists_compact_cover_thick_frames hn Γ disc hcov (shortDisplacement_mem_nhds hn hε)
  let p : PO n 1 → HUpper n := fun g => g • basepointH
  have hp : Continuous p :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_id.prodMk continuous_const)
  refine ⟨p '' C ∩ thickPart hn Γ ε, (hC.image hp).inter_right
    (isClosed_thickPart hn Γ ε), inter_subset_right, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := exists_po_smul_basepoint hn x
  have hg' : g • (basepointH : HUpper n) = x := hg
  have hgt : g ∈ thickSet Γ (shortDisplacement hn ε) :=
    (mem_thickSet_shortDisplacement_iff hn Γ ε g).mpr (hg ▸ hx)
  obtain ⟨γ, hγ⟩ := hcover g hgt
  refine ⟨γ, ⟨?_, smul_mem_thickPart hn hx γ⟩⟩
  refine ⟨(γ : PO n 1) * g, hγ, ?_⟩
  change ((γ : PO n 1) * g) • basepointH = (γ : PO n 1) • x
  rw [mul_smul, hg']

theorem isCompact_quotient_thickPart (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' thickPart hn Γ ε) := by
  let := EquivariantMap.subAction hn Γ
  obtain ⟨K, hK, hKt, hcover⟩ := exists_compact_thickPart_core hn Γ disc hcov hε
  have himage : (Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' K
      = (Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' thickPart hn Γ ε := by
    apply Subset.antisymm (image_mono hKt)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hcover x hx
    refine ⟨(poMulAction hn).smul (γ : PO n 1) x, hγ, ?_⟩
    exact Quotient.sound ⟨γ, rfl⟩
  rw [← himage]
  exact hK.image continuous_quotient_mk'

end Hyperbolic

end DifferentialGeometry.LatticeCompactness
