/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Lattices.Basic

noncomputable section

open Set Function MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Pointwise ENNReal

namespace DifferentialGeometry.FiniteIndexCovolume

section Action

variable {G X : Type*} [Group G] [Countable G] [MulAction G X] [MeasurableSpace X]
variable {μ : Measure X} [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

def transversalDomain (R : Set G) (F : Set X) : Set X :=
  ⋃ r : R, (r : G) • F

theorem isFundamentalDomain_transversal {H : Subgroup G} {R : Set G}
    (hR : Subgroup.IsComplement (H : Set G) R) {F : Set X}
    (hF : IsFundamentalDomain G F μ) :
    IsFundamentalDomain H (transversalDomain R F) μ where
  nullMeasurableSet := .iUnion fun r => hF.nullMeasurableSet.smul (r : G)
  ae_covers := hF.ae_covers.mono fun x hx => by
    obtain ⟨g, hg⟩ := hx
    obtain ⟨⟨h, r⟩, hhr⟩ := hR.2 g⁻¹
    change (h : G) * (r : G) = g⁻¹ at hhr
    have hrg : (r : G) * g = (h : G)⁻¹ := by
      calc
        (r : G) * g = (h : G)⁻¹ * ((h : G) * (r : G)) * g := by group
        _ = (h : G)⁻¹ * g⁻¹ * g := by rw [hhr]
        _ = (h : G)⁻¹ := by group
    refine ⟨h⁻¹, mem_iUnion.mpr ⟨r, g • x, hg, ?_⟩⟩
    change (r : G) • (g • x) = (h : G)⁻¹ • x
    rw [smul_smul, hrg]
  aedisjoint := by
    intro h k hne
    change AEDisjoint μ ((h : G) • transversalDomain R F)
      ((k : G) • transversalDomain R F)
    simp only [transversalDomain, smul_set_iUnion, AEDisjoint.iUnion_left_iff,
      AEDisjoint.iUnion_right_iff, smul_smul]
    intro r s
    apply hF.aedisjoint
    intro heq
    have hp : (h, s) = (k, r) := hR.1 heq
    exact hne (congrArg Prod.fst hp)

theorem hasFundamentalDomain_subgroup (H : Subgroup G) [hfd : HasFundamentalDomain G X μ] :
    HasFundamentalDomain H X μ := by
  obtain ⟨R, hR, _⟩ := H.exists_isComplement_right 1
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  exact (isFundamentalDomain_transversal hR hF).hasFundamentalDomain μ

theorem measure_transversalDomain {H : Subgroup G} [H.FiniteIndex] {R : Set G}
    (hR : Subgroup.IsComplement (H : Set G) R) {F : Set X}
    (hF : IsFundamentalDomain G F μ) :
    μ (transversalDomain R F) = (H.index : ℝ≥0∞) * μ F := by
  let : Fintype R := hR.finite_right.fintype
  have hdisj : Pairwise (AEDisjoint μ on fun r : R => (r : G) • F) := by
    intro r s hrs
    exact hF.aedisjoint (fun h => hrs (Subtype.ext h))
  rw [transversalDomain, measure_iUnion₀ hdisj (fun r => hF.nullMeasurableSet.smul (r : G))]
  simp only [measure_smul, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hR.card_right]

theorem covolume_subgroup (H : Subgroup G) [H.FiniteIndex]
    [hfd : HasFundamentalDomain G X μ] :
    covolume H X μ = (H.index : ℝ≥0∞) * covolume G X μ := by
  obtain ⟨R, hR, _⟩ := H.exists_isComplement_right 1
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  rw [(isFundamentalDomain_transversal hR hF).covolume_eq_volume μ,
    hF.covolume_eq_volume μ, measure_transversalDomain hR hF]

end Action

section AmbientSubgroup

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} [Measure.IsMulLeftInvariant μ]
variable {H Γ : Subgroup G} [Countable Γ]

omit [MeasurableMul G] [Measure.IsMulLeftInvariant μ] [Countable Γ] in
theorem isFundamentalDomain_of_subgroupOf (hHΓ : H ≤ Γ) {F : Set G}
    (hF : IsFundamentalDomain (H.subgroupOf Γ) F μ) :
    IsFundamentalDomain H F μ := by
  let e := Subgroup.subgroupOfEquivOfLe hHΓ
  have h := hF.preimage_of_equiv (Measure.QuasiMeasurePreserving.id μ)
    e.bijective (fun _ _ => rfl)
  simpa only [Set.preimage_id] using h

theorem hasFundamentalDomain_of_le (hHΓ : H ≤ Γ) [HasFundamentalDomain Γ G μ] :
    HasFundamentalDomain H G μ := by
  have hfd := hasFundamentalDomain_subgroup (μ := μ) (X := G) (H.subgroupOf Γ)
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  exact (isFundamentalDomain_of_subgroupOf hHΓ hF).hasFundamentalDomain μ

theorem covolume_of_le (hHΓ : H ≤ Γ) [(H.subgroupOf Γ).FiniteIndex]
    [HasFundamentalDomain Γ G μ] :
    covolume H G μ = (H.relIndex Γ : ℝ≥0∞) * covolume Γ G μ := by
  let e := Subgroup.subgroupOfEquivOfLe hHΓ
  let : Countable H := Countable.of_equiv (H.subgroupOf Γ) e.toEquiv
  have hfd := hasFundamentalDomain_subgroup (μ := μ) (X := G) (H.subgroupOf Γ)
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  rw [(isFundamentalDomain_of_subgroupOf hHΓ hF).covolume_eq_volume μ,
    ← hF.covolume_eq_volume μ]
  exact covolume_subgroup (H.subgroupOf Γ)

theorem covolume_ne_top_of_le (hHΓ : H ≤ Γ) [(H.subgroupOf Γ).FiniteIndex]
    [HasFundamentalDomain Γ G μ] (hcov : covolume Γ G μ ≠ ⊤) :
    covolume H G μ ≠ ⊤ := by
  rw [covolume_of_le hHΓ]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hcov

end AmbientSubgroup

section PO

variable {n : ℕ} {H Γ : Subgroup (PO n 1)}

theorem finiteIndex_lattice_data (hHΓ : H ≤ Γ) [(H.subgroupOf Γ).FiniteIndex]
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    IsDiscrete (SetLike.coe H) ∧ HasFundamentalDomain H (PO n 1) ∧
      covolume H (PO n 1) ≠ 0 ∧ covolume H (PO n 1) ≠ ⊤ ∧
      covolume H (PO n 1) = (H.relIndex Γ : ℝ≥0∞) * covolume Γ (PO n 1) := by
  let : Countable Γ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Γ disc
  have hdisc : IsDiscrete (SetLike.coe H) := disc.mono hHΓ
  let : HasFundamentalDomain H (PO n 1) := hasFundamentalDomain_of_le hHΓ
  exact ⟨hdisc, inferInstance, DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.covolume_ne_zero H hdisc,
    covolume_ne_top_of_le hHΓ hcov, covolume_of_le hHΓ⟩

end PO

end DifferentialGeometry.FiniteIndexCovolume
