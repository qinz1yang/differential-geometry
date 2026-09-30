/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceRuns
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCircleCapSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactFaceDiskFamily.exists_arcs_of_holes
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {B₁ B₂ : Set E3} (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, section34CompactVertexBallImage src f₁ w) {H : Fin 4 → Set E3}
    (hHE : ∀ k, ∃ e : Section34CompactEdgeIndex K K', H k = section34CompactSplitDiskImage src f₁ e)
    (h12 : B₁ ∩ B₂ = ⋃ k, H k) (s : Section34CompactSimplexIndex K 3)
    (hcov : ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 →
      section34CompactVertexBallImage src f₁ w ⊆ B₁ ∪ B₂)
    {i j : Fin 4} {p q : E3} (hHi : tgtD s ∩ H i = {p}) (hHj : tgtD s ∩ H j = {q})
    (hHij : Disjoint (H i) (H j)) (hHo : ∀ k, k ≠ i → k ≠ j → tgtD s ∩ H k = ∅)
    {w₁ w₂ : Section34CompactVertexIndex K K'} (hw₁ : Section34Incident w₁.1 s.1)
    (hw₂ : Section34Incident w₂.1 s.1) (hV₁ : section34CompactVertexBallImage src f₁ w₁ ⊆ B₁)
    (hV₂ : section34CompactVertexBallImage src f₁ w₂ ⊆ B₂) :
    p ≠ q ∧ tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧ tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} ∧
      (∃ γ₁ : ℝ → E3, IsPLHomeomorphOn γ₁ (Icc 0 1) (tgtD s ∩ B₁) ∧ γ₁ 0 = p ∧ γ₁ 1 = q) ∧
      ∃ γ₂ : ℝ → E3, IsPLHomeomorphOn γ₂ (Icc 0 1) (tgtD s ∩ B₂) ∧ γ₂ 0 = p ∧ γ₂ 1 = q := by
  have hpH : p ∈ H i := (hHi.symm.subset (mem_singleton p)).2
  have hqH : q ∈ H j := (hHj.symm.subset (mem_singleton q)).2
  have hpD : p ∈ tgtD s := (hHi.symm.subset (mem_singleton p)).1
  have hqD : q ∈ tgtD s := (hHj.symm.subset (mem_singleton q)).1
  have hpq : p ≠ q := fun h => Set.disjoint_left.mp hHij hpH (by rw [h]; exact hqH)
  have hinter : tgtD s ∩ B₁ ∩ B₂ = {p, q} := by
    apply Subset.antisymm
    · rintro z ⟨⟨hzD, hz1⟩, hz2⟩
      have hz12 : z ∈ B₁ ∩ B₂ := ⟨hz1, hz2⟩
      rw [h12] at hz12
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz12
      by_cases hki : k = i
      · subst hki
        exact Or.inl (hHi.subset ⟨hzD, hk⟩)
      · by_cases hkj : k = j
        · subst hkj
          exact Or.inr (hHj.subset ⟨hzD, hk⟩)
        · have h0 : z ∈ tgtD s ∩ H k := ⟨hzD, hk⟩
          rw [hHo k hki hkj] at h0
          exact h0.elim
    · have hHB : ∀ k, H k ⊆ B₁ ∩ B₂ := fun k => by
        rw [h12]
        exact subset_iUnion H k
      rintro z (rfl | rfl)
      · exact ⟨⟨hpD, (hHB i hpH).1⟩, (hHB i hpH).2⟩
      · exact ⟨⟨hqD, (hHB j hqH).1⟩, (hHB j hqH).2⟩
  have hcover : tgtDBd s ⊆ B₁ ∪ B₂ := by
    obtain ⟨-, -, hD3, -, -, -, -, hD8, -⟩ := hdisk
    intro z hz
    rw [← hD3 s] at hz
    obtain ⟨w, hzw⟩ := mem_iUnion.mp hz.2
    refine hcov w ?_ hzw
    by_contra hns
    have h0 : z ∈ tgtD s ∩ section34CompactVertexBallImage src f₁ w := ⟨hz.1, hzw⟩
    rw [hD8 s w hns] at h0
    exact h0
  have hne : ∀ {B : Set E3} {w : Section34CompactVertexIndex K K'},
      Section34Incident w.1 s.1 → section34CompactVertexBallImage src f₁ w ⊆ B →
      ((tgtD s ∩ B) \ {p, q}).Nonempty := by
    intro B w hw hVB
    obtain ⟨z, hzA, hzE⟩ := hdisk.exists_mem_faceArc_notMem_splitDiskImage ⟨(s, w), hw⟩
    have hzDV := (hdisk.faceDisk_inter_vertexBallImage_eq ⟨(s, w), hw⟩).symm.subset hzA
    refine ⟨z, ⟨hzDV.1, hVB hzDV.2⟩, ?_⟩
    rintro (rfl | rfl)
    · obtain ⟨e, he⟩ := hHE i
      exact hzE e (by rw [← he]; exact hpH)
    · obtain ⟨e, he⟩ := hHE j
      exact hzE e (by rw [← he]; exact hqH)
  obtain ⟨hDb, hγ₁, hγ₂⟩ := hdisk.exists_arcs_of_inter_eq_pair s hB₁ hB₂ hcover hsub hpq hinter
    (hne hw₁ hV₁) (hne hw₂ hV₂)
  refine ⟨hpq, hDb, ?_, hγ₁, hγ₂⟩
  rw [← hinter]
  ext z
  simp only [mem_inter_iff]
  tauto

theorem exists_split_of_four_runs {B₁ : Set E3} (hB₁ : IsPLBall 3 B₁) {H r : Fin 4 → Set E3}
    {rH : Fin 4 → (Fin 3 → ℝ) → E3} {ρ : Fin 4 → ℝ → E3}
    (hrH : ∀ k, IsPLHomeomorphOn (rH k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H k))
    (hHB : ∀ k, H k ⊆ frontier B₁) (hHdisj : Pairwise fun k l => Disjoint (H k) (H l))
    (hρ : ∀ k, IsPLHomeomorphOn (ρ k) (Icc 0 1) (r k)) (hrB : ∀ k, r k ⊆ frontier B₁)
    (hrr : Pairwise fun k l => Disjoint (r k) (r l))
    (hout : ∀ k, r k ∩ H k = {ρ k 1}) (hin : ∀ k, r (k + 1) ∩ H k = {ρ (k + 1) 0})
    (hfar : ∀ k l, l ≠ k → l + 1 ≠ k → r k ∩ H l = ∅)
    (hbout : ∀ k, ρ k 1 ∈ rH k '' stdSimplexBoundary 2)
    (hbin : ∀ k, ρ (k + 1) 0 ∈ rH k '' stdSimplexBoundary 2) :
    ∃ (X Y : Set E3) (qX qY : (Fin 3 → ℝ) → E3) (β : Fin 4 → Set E3) (σ : Fin 4 → ℝ → E3),
      IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X ∧
      IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y ∧
      X ∪ Y ∪ (⋃ k, H k) = frontier B₁ ∧ X ∩ Y = ⋃ k, r k ∧
      (∀ k, IsPLHomeomorphOn (σ k) (Icc 0 1) (β k)) ∧
      (∀ k, β k ⊆ rH k '' stdSimplexBoundary 2) ∧
      (∀ k, (X ∩ H k = β k ∧ Y ∩ H k = closure (rH k '' stdSimplexBoundary 2 \ β k)) ∨
        (X ∩ H k = closure (rH k '' stdSimplexBoundary 2 \ β k) ∧ Y ∩ H k = β k)) ∧
      qX '' stdSimplexBoundary 2 = (⋃ k, r k) ∪ ⋃ k, (X ∩ H k) ∧
      qY '' stdSimplexBoundary 2 = (⋃ k, r k) ∪ ⋃ k, (Y ∩ H k) := by
  have hbH : ∀ k, rH k '' stdSimplexBoundary 2 ⊆ H k := fun k => by
    rw [← (hrH k).image_eq]
    exact image_mono fun x hx => hx.1
  have hne : ∀ k, ρ k 1 ≠ ρ (k + 1) 0 := by
    intro k h
    have h1 : ρ k 1 ∈ r k := (hρ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
    have h2 : ρ (k + 1) 0 ∈ r (k + 1) := (hρ (k + 1)).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    have hk : k ≠ k + 1 := by
      fin_cases k <;> decide
    exact Set.disjoint_left.mp (hrr hk) h1 (h ▸ h2)
  have harc : ∀ k, ∃ (β : Set E3) (σ : ℝ → E3), IsPLHomeomorphOn σ (Icc 0 1) β ∧
      σ 0 = ρ k 1 ∧ σ 1 = ρ (k + 1) 0 ∧ β ⊆ rH k '' stdSimplexBoundary 2 := by
    intro k
    obtain ⟨A, B', γ, δ', h⟩ := exists_arc_decomposition_of_isPLSphere_one
      ((hrH k).isPLSphere_image_stdSimplexBoundary (n := 1)) (hbout k) (hbin k) (hne k)
    obtain ⟨hγ, -, hγ0, hγ1, -, -, hAB, -⟩ := h
    refine ⟨A, γ, hγ, hγ0, hγ1, ?_⟩
    rw [← hAB]
    exact subset_union_left
  choose β σ hσ hσ0 hσ1 hβb using harc
  have hβH : ∀ k, β k ⊆ H k := fun k => (hβb k).trans (hbH k)
  have hρ0 : ∀ k, ρ k 0 ∈ r k := fun k => (hρ k).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hρ1 : ∀ k, ρ k 1 ∈ r k := fun k => (hρ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hσ0m : ∀ k, σ k 0 ∈ β k := fun k => (hσ k).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hσ1m : ∀ k, σ k 1 ∈ β k := fun k => (hσ k).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hrβ : ∀ k, r k ∩ β k = {ρ k 1} := by
    intro k
    apply Subset.antisymm
    · rw [← hout k]
      exact inter_subset_inter_right _ (hβH k)
    · rintro z rfl
      exact ⟨hρ1 k, hσ0 k ▸ hσ0m k⟩
  have hβr : ∀ k, β k ∩ r (k + 1) = {σ k 1} := by
    intro k
    rw [hσ1 k]
    apply Subset.antisymm
    · rw [← hin k, inter_comm (β k)]
      exact inter_subset_inter_right _ (hβH k)
    · rintro z rfl
      exact ⟨hσ1 k ▸ hσ1m k, hρ0 (k + 1)⟩
  have hJ := isPLSphere_one_iUnion_union_iUnion_of_fin_four hρ hσ hσ0 hσ1 hrβ hβr
    (fun k l hkl => hrr hkl) (fun k l hkl => (hHdisj hkl).mono (hβH k) (hβH l))
    (fun k l h1 h2 => by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact subset_eq_empty (inter_subset_inter_right _ (hβH l)) (hfar k l h1 h2))
  set J := (⋃ k, r k) ∪ ⋃ k, β k
  have hJS : J ⊆ frontier B₁ :=
    union_subset (iUnion_subset hrB) (iUnion_subset fun k => (hβH k).trans (hHB k))
  have hends : ∀ k, ({σ k 0, σ k 1} : Set E3) ⊆ ⋃ l, r l := by
    intro k z hz
    rcases hz with rfl | hz
    · exact mem_iUnion.mpr ⟨k, hσ0 k ▸ hρ1 k⟩
    · rw [mem_singleton_iff.mp hz, hσ1 k]
      exact mem_iUnion.mpr ⟨k + 1, hρ0 (k + 1)⟩
  have hrHl : ∀ k l, r k ∩ H l ⊆ {σ l 0, σ l 1} := by
    intro k l z hz
    by_cases hlk : l = k
    · subst hlk
      rw [hout l] at hz
      rw [mem_singleton_iff.mp hz, ← hσ0 l]
      exact mem_insert _ _
    · by_cases hlk' : l + 1 = k
      · subst hlk'
        rw [hin l] at hz
        rw [mem_singleton_iff.mp hz, ← hσ1 l]
        exact mem_insert_of_mem _ (mem_singleton _)
      · rw [hfar k l hlk hlk'] at hz
        exact hz.elim
  have hHJ : ∀ k, H k ∩ J = β k := by
    intro k
    apply Subset.antisymm
    · rintro z ⟨hzH, hz | hz⟩
      · obtain ⟨l, hl⟩ := mem_iUnion.mp hz
        rcases hrHl l k ⟨hl, hzH⟩ with h | h
        · rw [h]
          exact hσ0m k
        · rw [mem_singleton_iff.mp h]
          exact hσ1m k
      · obtain ⟨l, hl⟩ := mem_iUnion.mp hz
        by_cases hlk : l = k
        · rw [← hlk]
          exact hl
        · exact absurd hzH (Set.disjoint_left.mp (hHdisj hlk) (hβH l hl))
    · intro z hz
      exact ⟨hβH k hz, Or.inr (mem_iUnion.mpr ⟨k, hz⟩)⟩
  obtain ⟨X, Y, qX, qY, hqX, hqY, hXY, hXYi, hXH, hqXb, hqYb⟩ :=
    hB₁.isPLSphere_frontier.exists_split_of_circle_caps hJ hJS hrH hHB hHdisj hσ hβb hHJ
  have hJβ : J \ ⋃ k, (β k \ {σ k 0, σ k 1}) = ⋃ k, r k := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hzn⟩
      · exact hz
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
        by_contra hzr
        exact hzn (mem_iUnion.mpr ⟨k, hk, fun h => hzr (hends k h)⟩)
    · intro z hz
      refine ⟨Or.inl hz, fun h => ?_⟩
      obtain ⟨l, hl, hln⟩ := mem_iUnion.mp h
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact hln (hrHl k l ⟨hk, hβH l hl⟩)
  rw [hJβ] at hXYi hqXb hqYb
  exact ⟨X, Y, qX, qY, β, σ, hqX, hqY, hXY, hXYi, hσ, hβb, hXH, hqXb, hqYb⟩

end DifferentialGeometry.Topology.PiecewiseLinear
