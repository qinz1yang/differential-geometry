/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcCycle
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPatch
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  {c : OpenPartialHomeomorph M E3}

omit [T2Space M] in
theorem IsPLCellOn.exists_interval_in_chart {A : Set M} {p q : M}
    (hA : IsPLCellOn 1 A {p, q}) (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hAc : A ⊆ c.source) :
    ∃ γ : ℝ → E3, IsPLHomeomorphOn γ (Icc 0 1) (c '' A) ∧ γ 0 = c p ∧ γ 1 = c q := by
  obtain ⟨r, hr, hrb⟩ := hA.exists_isPLHomeomorphOn_image_chart hc hAc
  have hi : IsPLCellOn 1 (c '' A) (c '' {p, q}) := by
    rw [hrb]
    exact isPLCellOn_id_of_isPLBall hr
  obtain ⟨γ, hγ, hγb⟩ := hi.exists_isPLHomeomorphOn_Icc
  rw [image_pair] at hγb
  rcases Set.pair_eq_pair_iff.mp hγb with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨γ, hγ, h0.symm, h1.symm⟩
  · refine ⟨fun t => γ (1 - t), isPLHomeomorphOn_comp_one_sub hγ, ?_, ?_⟩
    · simpa only [sub_zero] using h0.symm
    · simpa only [sub_self] using h1.symm

theorem IsPLCellOn.exists_split_of_runs_in_chart {m : ℕ} {B Bb : Set M}
    (hB : IsPLCellOn 3 B Bb) {H Hb r : Fin (m + 2) → Set M} {p q : Fin (m + 2) → M}
    (hH : ∀ k, IsPLCellOn 2 (H k) (Hb k))
    (hHB : ∀ k, H k ⊆ frontier B) (hHdisj : Pairwise fun k l => Disjoint (H k) (H l))
    (hr : ∀ k, IsPLCellOn 1 (r k) {p k, q k}) (hrB : ∀ k, r k ⊆ frontier B)
    (hrr : Pairwise fun k l => Disjoint (r k) (r l))
    (hout : ∀ k, r k ∩ H k = {q k}) (hin : ∀ k, r (k + 1) ∩ H k = {p (k + 1)})
    (hfar : ∀ k l, l ≠ k → l + 1 ≠ k → r k ∩ H l = ∅)
    (hbout : ∀ k, q k ∈ Hb k) (hbin : ∀ k, p (k + 1) ∈ Hb k)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hBc : B ⊆ c.source) :
    ∃ X Xb Y Yb : Set M, IsPLCellOn 2 X Xb ∧ IsPLCellOn 2 Y Yb ∧
      X ∪ Y ∪ (⋃ k, H k) = frontier B ∧ X ∩ Y = ⋃ k, r k ∧
      (∀ k, X ∩ H k ∪ Y ∩ H k = Hb k) ∧
      Xb = (⋃ k, r k) ∪ ⋃ k, X ∩ H k ∧
      Yb = (⋃ k, r k) ∪ ⋃ k, Y ∩ H k ∧
      ∀ k, IsPLCellOn 1 (X ∩ H k) {q k, p (k + 1)} ∧
        IsPLCellOn 1 (Y ∩ H k) {q k, p (k + 1)} := by
  have hBcl := hB.isCompact.isClosed
  have hHc : ∀ k, H k ⊆ c.source := fun k => (hHB k).trans (hBcl.frontier_subset.trans hBc)
  have hrc : ∀ k, r k ⊆ c.source := fun k => (hrB k).trans (hBcl.frontier_subset.trans hBc)
  have hpc : ∀ k, p k ∈ c.source := fun k =>
    hrc k ((hr k).boundary_subset (mem_insert _ _))
  have hqc : ∀ k, q k ∈ c.source := fun k =>
    hrc k ((hr k).boundary_subset (mem_insert_of_mem _ (mem_singleton _)))
  have hHbc : ∀ k, Hb k ⊆ c.source := fun k => (hH k).boundary_subset.trans (hHc k)
  obtain ⟨hBi, hBb⟩ := hB.isPLBall_image_chart hc hBc
  have hBfr : c '' frontier B = frontier (c '' B) := by
    rw [← hB.boundary_eq_frontier]
    exact hBb
  choose rH hrH hrHb using fun k => (hH k).exists_isPLHomeomorphOn_image_chart hc (hHc k)
  choose ρ hρ hρ0 hρ1 using fun k => (hr k).exists_interval_in_chart hc (hrc k)
  have hfrc : frontier (c '' B) ⊆ c.target := by
    rw [← hBfr]
    exact image_subset_iff.mpr fun z hz => c.map_source (hBc (hBcl.frontier_subset hz))
  have hdis : ∀ A D : Set M, A ⊆ c.source → D ⊆ c.source → Disjoint A D →
      Disjoint (c '' A) (c '' D) := by
    intro A D hAc hDc hAD
    rw [Set.disjoint_iff_inter_eq_empty, ← c.injOn.image_inter hAc hDc,
      Set.disjoint_iff_inter_eq_empty.mp hAD, image_empty]
  have houti : ∀ k, c '' r k ∩ c '' H k = {ρ k 1} := fun k => by
    rw [← c.injOn.image_inter (hrc k) (hHc k), hout k, image_singleton, hρ1 k]
  have hini : ∀ k, c '' r (k + 1) ∩ c '' H k = {ρ (k + 1) 0} := fun k => by
    rw [← c.injOn.image_inter (hrc (k + 1)) (hHc k), hin k, image_singleton, hρ0 (k + 1)]
  obtain ⟨X, Y, qX, qY, β, σ, τ, hX, hY, hXY, hXYi, hσ, hτ, hβb, hXH, hXb, hYb⟩ :=
    exists_split_of_runs hBi hrH
      (fun k => hBfr ▸ image_mono (hHB k))
      (fun k l hkl => hdis _ _ (hHc k) (hHc l) (hHdisj hkl)) hρ
      (fun k => hBfr ▸ image_mono (hrB k))
      (fun k l hkl => hdis _ _ (hrc k) (hrc l) (hrr hkl)) houti hini
      (fun k l h1 h2 => by
        rw [← c.injOn.image_inter (hrc k) (hHc l), hfar k l h1 h2, image_empty])
      (fun k => by rw [← hrHb k, hρ1 k]; exact mem_image_of_mem c (hbout k))
      (fun k => by rw [← hrHb k, hρ0 (k + 1)]; exact mem_image_of_mem c (hbin k))
  have hXt : X ⊆ c.target := fun z hz => hfrc (hXY.subset (Or.inl (Or.inl hz)))
  have hYt : Y ⊆ c.target := fun z hz => hfrc (hXY.subset (Or.inl (Or.inr hz)))
  have hHt : ∀ k, c '' H k ⊆ c.target := fun k =>
    image_subset_iff.mpr fun z hz => c.map_source (hHc k hz)
  have hpull : ∀ A : Set M, A ⊆ c.source → c.symm '' (c '' A) = A :=
    fun A hAc => c.symm_image_image_of_subset_source hAc
  have hinter : ∀ Z : Set E3, Z ⊆ c.target → ∀ k,
      c.symm '' (Z ∩ c '' H k) = c.symm '' Z ∩ H k := by
    intro Z hZ k
    rw [c.symm.injOn.image_inter hZ (hHt k), hpull _ (hHc k)]
  have hHX : ∀ k, X ∩ c '' H k ∪ Y ∩ c '' H k = c '' Hb k := by
    intro k
    have hcl : IsClosed (rH k '' stdSimplexBoundary 2) :=
      ((hrH k).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron.isClosed
    rw [hrHb k]
    rcases hXH k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact union_closure_sdiff_eq_of_subset hcl (hβb k)
    · rw [h1, h2, union_comm]
      exact union_closure_sdiff_eq_of_subset hcl (hβb k)
  have hXcell := (isPLCellOn_id_of_isPLBall hX).image_chart_symm hc hXt
  have hYcell := (isPLCellOn_id_of_isPLBall hY).image_chart_symm hc hYt
  refine ⟨c.symm '' X, c.symm '' (qX '' stdSimplexBoundary 2),
    c.symm '' Y, c.symm '' (qY '' stdSimplexBoundary 2), hXcell, hYcell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hi := congrArg (fun Z => c.symm '' Z) hXY
    simpa only [image_union, image_iUnion, hpull _ (hHc _), ← hBfr,
      hpull _ (hBcl.frontier_subset.trans hBc)] using hi
  · have hi := congrArg (fun Z => c.symm '' Z) hXYi
    simpa only [c.symm.injOn.image_inter hXt hYt, image_iUnion, hpull _ (hrc _)] using hi
  · intro k
    have hi := congrArg (fun Z => c.symm '' Z) (hHX k)
    simpa only [image_union, hinter X hXt k, hinter Y hYt k, hpull _ (hHbc k)] using hi
  · rw [hXb, image_union, image_iUnion, image_iUnion]
    simp only [hpull _ (hrc _), hinter X hXt]
  · rw [hYb, image_union, image_iUnion, image_iUnion]
    simp only [hpull _ (hrc _), hinter Y hYt]
  · intro k
    have harc : ∀ Z : Set E3, Z ⊆ c.target →
        (∃ γ : ℝ → E3, IsPLHomeomorphOn γ (Icc 0 1) Z ∧
          γ 0 = ρ k 1 ∧ γ 1 = ρ (k + 1) 0) →
        IsPLCellOn 1 (c.symm '' Z) {q k, p (k + 1)} := by
      rintro Z hZ ⟨γ, hγ, h0, h1⟩
      have hi := (isPLCellOn_one_of_isPLHomeomorphOn_Icc hγ).image_chart_symm hc hZ
      simpa only [image_pair, h0, h1, hρ1 k, hρ0 (k + 1),
        c.left_inv (hqc k), c.left_inv (hpc (k + 1))] using hi
    rw [← hinter X hXt k, ← hinter Y hYt k]
    constructor
    · apply harc _ (inter_subset_left.trans hXt)
      rcases hXH k with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        exact ⟨σ k, hσ k⟩
      · rw [h1]
        exact ⟨τ k, hτ k⟩
    · apply harc _ (inter_subset_left.trans hYt)
      rcases hXH k with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [h2]
        exact ⟨τ k, hτ k⟩
      · rw [h2]
        exact ⟨σ k, hσ k⟩

end DifferentialGeometry.Topology.PiecewiseLinear
