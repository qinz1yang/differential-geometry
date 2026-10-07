/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.FixedLocus

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.StratumIncidence

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicConvexity
open OrbifoldStrata FixedLocusGeometry

variable {n : ℕ}

theorem val_mem_of_interior_section_nonempty (V : Submodule ℝ (LorVec n))
    (hV : (interior {x : HUpper n | x.val ∈ V}).Nonempty) :
    ∀ y : HUpper n, y.val ∈ V := by
  obtain ⟨p, hp⟩ := hV
  have hpV : p.val ∈ V :=
    (interior_subset (s := {x : HUpper n | x.val ∈ V})) hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  intro y
  by_cases hpy : p = y
  · simpa only [← hpy] using hpV
  let t : ℝ := r / 2
  have ht : 0 < t := half_pos hr
  have hq : geodFromTo p y hpy t ∈ Metric.ball p r := by
    have hd : dist (geodFromTo p y hpy t) p = |t| := by
      simpa only [geodFromTo_zero, sub_zero] using dist_geodFromTo hpy t 0
    rw [Metric.mem_ball, hd, abs_of_pos ht]
    dsimp [t]
    linarith
  have hqV : (geodFromTo p y hpy t).val ∈ V := hball hq
  have hsV : Real.sinh t • dirVec p y ∈ V := by
    have h := V.sub_mem hqV (V.smul_mem (Real.cosh t) hpV)
    change Real.cosh t • p.val + Real.sinh t • dirVec p y -
      Real.cosh t • p.val ∈ V at h
    simpa only [add_sub_cancel_left] using h
  have hdir : dirVec p y ∈ V := by
    have h := V.smul_mem (Real.sinh t)⁻¹ hsV
    rwa [smul_smul, inv_mul_cancel₀ (Real.sinh_pos_iff.mpr ht).ne', one_smul] at h
  have hy := V.add_mem (V.smul_mem (Real.cosh (dist p y)) hpV)
    (V.smul_mem (Real.sinh (dist p y)) hdir)
  change (geodFromTo p y hpy (dist p y)).val ∈ V at hy
  rwa [geodFromTo_dist] at hy

theorem fixedLocus_eq_univ_of_interior_nonempty (hn : 1 ≤ n)
    (D : Subgroup (PO n 1)) (hD : (interior (fixedLocus hn D)).Nonempty) :
    fixedLocus hn D = univ := by
  have hne : (fixedLocus hn D).Nonempty := hD.mono interior_subset
  have he := fixedLocus_eq_preimage_span hn D hne
  have hV : (interior {x : HUpper n | x.val ∈ locusSpan (fixedLocus hn D)}).Nonempty := by
    rwa [← he]
  apply eq_univ_of_forall
  intro y
  exact mem_fixedLocus_of_val_mem_span hn D hne
    (val_mem_of_interior_section_nonempty _ hV y)

theorem interior_fixedLocus_eq_empty (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hproper : fixedLocus hn D ≠ univ) : interior (fixedLocus hn D) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  exact fun h => hproper (fixedLocus_eq_univ_of_interior_nonempty hn D h)

theorem fixedLocus_eq_univ_iff (hn : 1 ≤ n) (D : Subgroup (PO n 1)) :
    fixedLocus hn D = univ ↔ D = ⊥ := by
  let := poMulAction hn
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro g hg
    change g = 1
    apply po_smul_eq_one hn
    intro x
    have hx : x ∈ fixedLocus hn D := h.symm ▸ mem_univ x
    exact hx ⟨g, hg⟩
  · rintro rfl
    apply eq_univ_of_forall
    intro x γ
    have hγ : (γ : PO n 1) = 1 := γ.property
    change (γ : PO n 1) • x = x
    rw [hγ, one_smul]

theorem not_isOpen_of_subset_fixedLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) {σ : Set (HUpper n)} (hF : (fixedStratum hn Γ ε σ).Nonempty)
    (hproper : σ ≠ univ) (hsub : fixedStratum hn Γ ε σ ⊆ σ) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  obtain ⟨x, hx⟩ := hF
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ := hx
  have hempty : interior σ = ∅ := by
    rw [← he]
    exact interior_fixedLocus_eq_empty hn _ (he ▸ hproper)
  intro hopen
  have hxint := (hopen.subset_interior_iff.mpr hsub) hx
  rw [hempty] at hxint
  exact hxint

theorem exists_outgoing_of_not_isOpen (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) {σ : Set (HUpper n)}
    (hopen : ¬IsOpen (fixedStratum hn Γ ε σ)) :
    ∃ τ : Set (HUpper n), σ ⊂ τ ∧
      ∃ x ∈ fixedStratum hn Γ ε σ, x ∈ closure (fixedStratum hn Γ ε τ) := by
  classical
  have hex : ∃ x ∈ fixedStratum hn Γ ε σ,
      x ∉ interior (fixedStratum hn Γ ε σ) := by
    by_contra h
    apply hopen
    apply subset_interior_iff_isOpen.mp
    intro x hx
    by_contra hnot
    exact h ⟨x, hx, hnot⟩
  obtain ⟨x, hx, hxint⟩ := hex
  let I := {τ : Set (HUpper n) // τ ≠ σ}
  have hpart : (fixedStratum hn Γ ε σ)ᶜ =
      ⋃ τ : I, fixedStratum hn Γ ε τ.val := by
    ext y
    constructor
    · intro hy
      have hne : fixedLocus hn (closedSmallSubgroup hn Γ ε y) ≠ σ := hy
      exact mem_iUnion.mpr ⟨⟨_, hne⟩, rfl⟩
    · intro hy hys
      obtain ⟨τ, hτ⟩ := mem_iUnion.mp hy
      exact τ.property (hτ.symm.trans hys)
  have hl : LocallyFinite (fun τ : I => fixedStratum hn Γ ε τ.val) :=
    (locallyFinite_fixedStratum hn Γ hΓ ε).comp_injective Subtype.val_injective
  have hc : x ∈ closure ((fixedStratum hn Γ ε σ)ᶜ) := by
    rwa [closure_compl, mem_compl_iff]
  rw [hpart, hl.closure_iUnion] at hc
  obtain ⟨τ, hτ⟩ := mem_iUnion.mp hc
  exact ⟨τ, fixedLocus_ssubset_of_incident hn Γ hΓ ε τ.property.symm hx hτ, x, hx, hτ⟩

theorem exists_higher_rank_incident_of_not_isOpen (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hopen : ¬IsOpen (fixedStratum hn Γ ε σ)) :
    ∃ τ : Set (HUpper n), τ.Nonempty ∧ locusRank σ < locusRank τ ∧
      ∃ x ∈ fixedStratum hn Γ ε σ, x ∈ closure (fixedStratum hn Γ ε τ) := by
  obtain ⟨τ, hsub, x, hx, hτ⟩ := exists_outgoing_of_not_isOpen hn Γ hΓ ε hopen
  exact ⟨τ, hσ.mono hsub.subset,
    locusRank_lt_of_incident hn Γ hΓ ε hσ hsub.ne hx hτ, x, hx, hτ⟩

end DifferentialGeometry.StratumIncidence
