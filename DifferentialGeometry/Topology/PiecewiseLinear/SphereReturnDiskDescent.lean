/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubinterval
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskContainment

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLSphere.exists_clean_return_subdisk
    {S : Set E} (hS : IsPLSphere 2 S) {ι : Type*} (F : ι → Set E) (i₀ : ι)
    {B₀ R₀ D₀ : Set E} {q₀ : (Fin 3 → ℝ) → E} {β₀ δ₀ : ℝ → E}
    (hβ₀ : IsPLHomeomorphOn β₀ (Icc 0 1) B₀) (hBF₀ : B₀ ⊆ F i₀)
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) R₀)
    (hδ₀0 : δ₀ 0 = β₀ 0) (hδ₀1 : δ₀ 1 = β₀ 1)
    (hB₀R₀ : B₀ ∩ R₀ = {β₀ 0, β₀ 1})
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₀B : q₀ '' stdSimplexBoundary 2 = B₀ ∪ R₀) (hD₀S : D₀ ⊆ S)
    (hfinite : (R₀ ∩ ⋃ i, F i).Finite)
    (hcross : ∀ (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E),
      IsPLHomeomorphOn β (Icc 0 1) B → B ⊆ F i →
      IsPLHomeomorphOn δ (Icc 0 1) R → δ 0 = β 0 → δ 1 = β 1 →
      R ⊆ R₀ → B ∩ R = {β 0, β 1} →
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      q '' stdSimplexBoundary 2 = B ∪ R → D ⊆ D₀ → D ∩ R₀ = R →
      ((D \ (B ∪ R)) ∩ ⋃ j, F j).Nonempty →
      ∃ (j : ι) (A : Set E) (α : ℝ → E), IsPLHomeomorphOn α (Icc 0 1) A ∧
        A ⊆ F j ∧ A ⊆ D ∧ A ∩ (B ∪ R) = {α 0, α 1} ∧
        ({α 0, α 1} : Set E) ⊆ R \ {β 0, β 1}) :
    ∃ (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E),
      IsPLHomeomorphOn β (Icc 0 1) B ∧ B ⊆ F i ∧
      IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = β 0 ∧ δ 1 = β 1 ∧
      R ⊆ R₀ ∧ B ∩ R = {β 0, β 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      q '' stdSimplexBoundary 2 = B ∪ R ∧ D ⊆ D₀ ∧ D ∩ R₀ = R ∧
      ∀ j, Disjoint (D \ (B ∪ R)) (F j) := by
  classical
  let P := fun (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E) =>
    IsPLHomeomorphOn β (Icc 0 1) B ∧ B ⊆ F i ∧
    IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = β 0 ∧ δ 1 = β 1 ∧
    R ⊆ R₀ ∧ B ∩ R = {β 0, β 1} ∧
    IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
    q '' stdSimplexBoundary 2 = B ∪ R ∧ D ⊆ D₀ ∧ D ∩ R₀ = R
  have hR₀D₀ : R₀ ⊆ D₀ := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hq₀B.symm.subset (Or.inr hx)
    exact hzx ▸ hq₀.bijOn.mapsTo hz.1
  have hinit : P i₀ B₀ R₀ D₀ q₀ β₀ δ₀ :=
    ⟨hβ₀, hBF₀, hδ₀, hδ₀0, hδ₀1, Subset.rfl, hB₀R₀, hq₀, hq₀B,
      Subset.rfl, inter_eq_right.mpr hR₀D₀⟩
  have hex : ∃ n, ∃ (i : ι) (B R D : Set E) (q : (Fin 3 → ℝ) → E) (β δ : ℝ → E),
      P i B R D q β δ ∧ (R ∩ ⋃ j, F j).ncard = n :=
    ⟨_, i₀, B₀, R₀, D₀, q₀, β₀, δ₀, hinit, rfl⟩
  obtain ⟨i, B, R, D, q, β, δ, hdata, hn⟩ := Nat.find_spec hex
  obtain ⟨hβ, hBF, hδ, hδ0, hδ1, hRR₀, hBR, hq, hqB, hDD₀, hDR₀⟩ := hdata
  refine ⟨i, B, R, D, q, β, δ, hβ, hBF, hδ, hδ0, hδ1, hRR₀, hBR,
    hq, hqB, hDD₀, hDR₀, ?_⟩
  intro j
  apply disjoint_left.mpr
  intro x hxD hxF
  obtain ⟨a, A, α, hα, hAF, hAD, hAL, hαends⟩ :=
    hcross i B R D q β δ hβ hBF hδ hδ0 hδ1 hRR₀ hBR hq hqB hDD₀ hDR₀
      ⟨x, hxD, mem_iUnion.mpr ⟨j, hxF⟩⟩
  have hαne : α 0 ≠ α 1 := fun heq => zero_ne_one
    (hα.bijOn.injOn (by norm_num) (by norm_num) heq)
  have hαR : ({α 0, α 1} : Set E) ⊆ R \ {δ 0, δ 1} := by
    simpa only [hδ0, hδ1] using hαends
  obtain ⟨R', δ', hδ', hδ'0, hδ'1, hR'⟩ :=
    exists_subarc_between_interior_points hδ (hαR (by simp)) (hαR (by simp)) hαne
  rw [hδ0, hδ1] at hR'
  have hR'R : R' ⊆ R := hR'.trans sdiff_subset
  have hendsR' : ({α 0, α 1} : Set E) ⊆ R' := by
    rw [← hδ'0, ← hδ'1]
    exact pair_subset (hδ'.bijOn.mapsTo (by norm_num)) (hδ'.bijOn.mapsTo (by norm_num))
  obtain ⟨D', q', hq', hD'D, hq'A, hD'J⟩ :=
    hS.exists_disk_between_proper_arc_and_boundary_arc hq (hDD₀.trans hD₀S)
      hα hδ' hδ'0 hδ'1 hAD
      (hR'R.trans (subset_union_right.trans hqB.symm.subset)) (by rw [hqB]; exact hAL)
  rw [hqB] at hD'J
  have hD'R : D' ∩ R = R' := Subset.antisymm
    (fun y hy => hD'J.subset ⟨hy.1, Or.inr hy.2⟩)
    (fun y hy => ⟨(hD'J.symm.subset hy).1, hR'R hy⟩)
  have hD'R₀ : D' ∩ R₀ = R' := Subset.antisymm
    (fun y hy => hD'R.subset ⟨hy.1, hDR₀.subset ⟨hD'D hy.1, hy.2⟩⟩)
    (fun y hy => ⟨(hD'R.symm.subset hy).1, hRR₀ (hR'R hy)⟩)
  have hAR' : A ∩ R' = {α 0, α 1} := Subset.antisymm
    (fun y hy => hAL.subset ⟨hy.1, Or.inr (hR'R hy.2)⟩)
    (fun y hy => ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
      (hα.bijOn.mapsTo (by norm_num))) hy, hendsR' hy⟩)
  have hnew : P a A R' D' q' α δ' :=
    ⟨hα, hAF, hδ', hδ'0, hδ'1, hR'R.trans hRR₀, hAR', hq', hq'A,
      hD'D.trans hDD₀, hD'R₀⟩
  have hfin : (R ∩ ⋃ j, F j).Finite :=
    hfinite.subset fun y hy => ⟨hRR₀ hy.1, hy.2⟩
  have hcorners : ({β 0, β 1} : Set E) ⊆ R ∩ ⋃ j, F j := by
    intro y hy
    exact ⟨(hBR.symm.subset hy).2, mem_iUnion.mpr ⟨i, hBF ((pair_subset
      (hβ.bijOn.mapsTo (by norm_num)) (hβ.bijOn.mapsTo (by norm_num))) hy)⟩⟩
  have hβne : β 0 ≠ β 1 := fun heq => zero_ne_one
    (hβ.bijOn.injOn (by norm_num) (by norm_num) heq)
  have hdrop := Set.ncard_sdiff_add_ncard_of_subset hcorners hfin
  rw [Set.ncard_pair hβne] at hdrop
  have hcount : (R' ∩ ⋃ j, F j).ncard ≤ ((R ∩ ⋃ j, F j) \ {β 0, β 1}).ncard :=
    Set.ncard_le_ncard (fun y hy => ⟨⟨hR'R hy.1, hy.2⟩, (hR' hy.1).2⟩) hfin.sdiff
  have hmin := Nat.find_min' hex ⟨a, A, R', D', q', α, δ', hnew, rfl⟩
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
