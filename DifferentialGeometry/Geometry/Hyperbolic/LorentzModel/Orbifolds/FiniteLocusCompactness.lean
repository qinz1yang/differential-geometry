/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.StratumExtrema

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FiniteLocusCompactness

open Hyperbolic HyperbolicAction HyperbolicFaithful
open OrbifoldStrata FixedLocusGeometry StratumMaximum

variable {n : ℕ}

theorem label_eq_univ_of_rank (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) (hF : (fixedStratum hn Γ ε σ).Nonempty)
    (hrank : n + 1 ≤ locusRank σ) : σ = univ := by
  obtain ⟨x, hx⟩ := hF
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ := hx
  have hsection : σ = {p : HUpper n | p.val ∈ locusSpan σ} := by
    simpa only [he] using fixedLocus_eq_preimage_span hn
      (closedSmallSubgroup hn Γ ε x) (he.symm ▸ hσ)
  have htop : locusSpan σ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := le_antisymm (locusRank_le σ) hrank
    simpa only [locusRank, LorVec, Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] using h
  rw [hsection, htop]
  apply eq_univ_of_forall
  intro p
  change p.val ∈ (⊤ : Submodule ℝ (LorVec n))
  exact Submodule.mem_top

theorem exists_finite_representatives_of_rank_bound (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x))
    (k : ℕ) :
    ∃ S : Set (Set (HUpper n)), S.Finite ∧ (∀ τ ∈ S, τ.Nonempty) ∧
      ∀ σ : Set (HUpper n), σ.Nonempty → (fixedStratum hn Γ ε σ).Nonempty →
        n + 1 ≤ locusRank σ + k →
          ∃ γ : Γ, (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' σ ∈ S := by
  classical
  let := poMulAction hn
  induction k with
  | zero =>
    refine ⟨{univ}, finite_singleton _, ?_, ?_⟩
    · intro τ hτ
      rw [mem_singleton_iff.mp hτ]
      exact ⟨basepointH, mem_univ _⟩
    · intro σ hσ hF hrank
      have he : σ = univ := label_eq_univ_of_rank hn Γ ε hσ hF (by simpa only [add_zero] using hrank)
      refine ⟨1, ?_⟩
      change (fun p : HUpper n => (1 : PO n 1) • p) '' σ ∈ ({univ} : Set (Set (HUpper n)))
      simpa only [one_smul, image_id', mem_singleton_iff] using he
  | succ k ih =>
    obtain ⟨S, hS, hSne, hcover⟩ := ih
    let : Finite S := hS
    choose N hNfinite hNcover using
      (fun τ : S => exists_finite_incident_representatives hn Γ hΓ hcov hε (hSne τ τ.property))
    let T : Set (Set (HUpper n)) := S ∪ ⋃ τ : S, N τ ∩ {σ | σ.Nonempty}
    have hT : T.Finite :=
      hS.union (Set.finite_iUnion (fun τ => (hNfinite τ).inter_of_left _))
    refine ⟨T, hT, ?_, ?_⟩
    · intro τ hτ
      rcases hτ with hτ | hτ
      · exact hSne τ hτ
      · obtain ⟨ρ, hρ⟩ := mem_iUnion.mp hτ
        exact hρ.2
    · intro σ hσ hF hrank
      by_cases hproper : σ = univ
      · obtain ⟨γ, hγ⟩ := hcover σ hσ hF (by
          have htop := submodule_eq_top_of_all_val (locusSpan σ)
            (fun p => val_mem_locusSpan (hproper.symm ▸ mem_univ p))
          have he : locusRank σ = n + 1 := by
            change Module.finrank ℝ (locusSpan σ) = n + 1
            rw [htop, finrank_top]
            simp only [LorVec, Module.finrank_pi,
              Fintype.card_sum, Fintype.card_fin]
          omega)
        exact ⟨γ, Or.inl hγ⟩
      obtain ⟨τ, hτ, hrankτ, x, hxσ, hxτ⟩ :=
        StratumIncidence.exists_higher_rank_incident_of_not_isOpen hn Γ hΓ ε hσ
          (not_isOpen_fixedStratum hn hdim Γ hΓ hcov hε hgeometry hσ hF hproper)
      have hFτ : (fixedStratum hn Γ ε τ).Nonempty :=
        (show (closure (fixedStratum hn Γ ε τ)).Nonempty from ⟨x, hxτ⟩).of_closure
      obtain ⟨γ, hγ⟩ := hcover τ hτ hFτ (by omega)
      let ρ : S := ⟨(fun p : HUpper n => (γ : PO n 1) • p) '' τ, hγ⟩
      have hinc : (closure (fixedStratum hn Γ ε ρ.val) ∩
          closure (fixedStratum hn Γ ε ((fun p : HUpper n => (γ : PO n 1) • p) '' σ))).Nonempty :=
        ⟨(γ : PO n 1) • x, smul_mem_closure_fixedStratum hn Γ ε hxτ γ,
          smul_mem_closure_fixedStratum hn Γ ε (subset_closure hxσ) γ⟩
      obtain ⟨δ, hδ⟩ := hNcover ρ _ hinc
      refine ⟨δ * γ, Or.inr (mem_iUnion.mpr ⟨ρ, ?_, ?_⟩)⟩
      · change (fun p : HUpper n => ((δ : PO n 1) * (γ : PO n 1)) • p) '' σ ∈ N ρ
        change (fun p : HUpper n => (δ : PO n 1) • p) ''
          ((fun p : HUpper n => (γ : PO n 1) • p) '' σ) ∈ N ρ at hδ
        simpa only [image_image, mul_smul] using hδ
      · exact hσ.image _

theorem exists_finite_stratum_representatives (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x)) :
    ∃ S : Set (Set (HUpper n)), S.Finite ∧ (∀ τ ∈ S, τ.Nonempty) ∧
      ∀ σ : Set (HUpper n), σ.Nonempty → (fixedStratum hn Γ ε σ).Nonempty →
        ∃ γ : Γ, (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' σ ∈ S := by
  obtain ⟨S, hS, hSne, hcover⟩ :=
    exists_finite_representatives_of_rank_bound hn hdim Γ hΓ hcov hε hgeometry n
  refine ⟨S, hS, hSne, fun σ hσ hF => hcover σ hσ hF ?_⟩
  have h := locusRank_pos hσ
  omega

theorem smul_mem_closure_finiteLocus (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {x : HUpper n} (hx : x ∈ closure (finiteLocus hn Γ ε)) (γ : Γ) :
    (poMulAction hn).smul (γ : PO n 1) x ∈ closure (finiteLocus hn Γ ε) := by
  rw [closure_finiteLocus_eq_iUnion hn Γ hΓ ε] at hx
  obtain ⟨σ, hxσ⟩ := mem_iUnion.mp hx
  have h := smul_mem_closure_fixedStratum hn Γ ε hxσ γ
  exact (closure_mono (fixedStratum_subset_finiteLocus hn Γ hΓ ε (σ.property.image _))) h

theorem exists_compact_finiteLocus_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x)) :
    ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ closure (finiteLocus hn Γ ε) ∧
      ∀ x ∈ closure (finiteLocus hn Γ ε), ∃ γ : Γ,
        (poMulAction hn).smul (γ : PO n 1) x ∈ K := by
  classical
  let := poMulAction hn
  obtain ⟨S, hS, hSne, hcover⟩ :=
    exists_finite_stratum_representatives hn hdim Γ hΓ hcov hε hgeometry
  let : Finite S := hS
  choose C hCcompact hCcover using
    (fun τ : S => exists_compact_cover_closure_fixedStratum hn Γ hΓ hcov hε (hSne τ τ.property))
  refine ⟨(⋃ τ : S, C τ) ∩ closure (finiteLocus hn Γ ε),
    (isCompact_iUnion hCcompact).inter_right isClosed_closure, inter_subset_right, ?_⟩
  intro x hx
  have hx' := hx
  rw [closure_finiteLocus_eq_iUnion hn Γ hΓ ε] at hx'
  obtain ⟨σ, hxσ⟩ := mem_iUnion.mp hx'
  have hF : (fixedStratum hn Γ ε σ.val).Nonempty :=
    (show (closure (fixedStratum hn Γ ε σ.val)).Nonempty from ⟨x, hxσ⟩).of_closure
  obtain ⟨γ, hγ⟩ := hcover σ σ.property hF
  let τ : S := ⟨(fun p : HUpper n => (γ : PO n 1) • p) '' σ.val, hγ⟩
  obtain ⟨δ, hδ⟩ := hCcover τ ((γ : PO n 1) • x)
    (smul_mem_closure_fixedStratum hn Γ ε hxσ γ)
  refine ⟨δ * γ, mem_iUnion.mpr ⟨τ, ?_⟩, smul_mem_closure_finiteLocus hn Γ hΓ ε hx (δ * γ)⟩
  change ((δ : PO n 1) * (γ : PO n 1)) • x ∈ C τ
  rwa [mul_smul]

theorem isCompact_quotient_closure_finiteLocus (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x)) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) '' closure (finiteLocus hn Γ ε)) := by
  let := EquivariantMap.subAction hn Γ
  obtain ⟨K, hK, hKsub, hcover⟩ := exists_compact_finiteLocus_core hn hdim Γ hΓ hcov hε hgeometry
  let q := Quotient.mk (MulAction.orbitRel Γ (HUpper n))
  have he : q '' K = q '' closure (finiteLocus hn Γ ε) := by
    apply Subset.antisymm (image_mono hKsub)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hcover x hx
    exact ⟨(poMulAction hn).smul (γ : PO n 1) x, hγ, Quotient.sound ⟨γ, rfl⟩⟩
  rw [← he]
  exact hK.image continuous_quotient_mk'

theorem exists_finite_parabolic_neighbors (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x)) :
    ∃ S : Set (HyperbolicBoundary.BoundaryH n), S.Finite ∧
      ∀ ξ : HyperbolicBoundary.BoundaryH n,
        (closure (finiteLocus hn Γ ε) ∩
          closure (ParabolicRegions.region hn Γ ε ξ)).Nonempty →
          ∃ δ : Γ, (HyperbolicBoundary.poBoundaryMulAction hn).smul (δ : PO n 1) ξ ∈ S := by
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_finiteLocus_core hn hdim Γ hΓ hcov hε hgeometry
  refine ⟨{ξ | (ParabolicRegions.closedRegion hn Γ ε ξ ∩ K).Nonempty},
    ParabolicRegions.finite_centers_meeting_compact hn Γ hΓ ε hK, ?_⟩
  rintro ξ ⟨x, hxfinite, hxξ⟩
  obtain ⟨δ, hδ⟩ := hcover x hxfinite
  have hc : Continuous (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_const.prodMk continuous_id)
  have h := (image_closure_subset_closure_image (s := ParabolicRegions.region hn Γ ε ξ) hc)
    ⟨x, hxξ, rfl⟩
  rw [ParabolicRegions.image_region] at h
  exact ⟨δ, (poMulAction hn).smul (δ : PO n 1) x,
    ParabolicRegions.closure_region_subset_closedRegion hn Γ hΓ ε _ h, hδ⟩

end DifferentialGeometry.FiniteLocusCompactness
