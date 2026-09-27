/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Adapted from exists_face_of_notMem_arc in Schoenflies/ArcComplement.lean,
commit 05a43d29cde026618777db3d4e4316204ccca237.
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import DifferentialGeometry.External.Schoenflies.SquareCycle

open Set Topology

namespace Schoenflies

open scoped Graph

theorem exists_square_chain {α : ℝ → Plane}
    (hα : ContinuousOn α unitInterval) (hinj : InjOn α unitInterval) {d : ℝ} (hd : 0 < d) :
    ∃ (n m : ℕ) (c : ℕ → Plane) (r : ℝ), 0 < m ∧ 0 < r ∧
      Graph.IsPlaneChain (familyChain c ((n + 1) * m) m r) segmentDrawing
        (familyOverlay c ((n + 1) * m) r) n ∧
      (∀ j ≤ (n + 1) * m, c j ∈ α '' unitInterval) ∧
      (∀ x ∈ α '' unitInterval, ∃ j ≤ (n + 1) * m, x ∈ Plane.openSquare (c j) r) ∧
      (∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
        Plane.supDist (c j) (c (p * m)) + r ≤ 3 * d) := by
  obtain ⟨m₁, hm₁, hmesh₁⟩ := exists_mesh hα hd 3 (by norm_num)
  obtain ⟨n, hK⟩ : ∃ n, 3 * m₁ = n + 1 := ⟨3 * m₁ - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [hK] at hmesh₁
  obtain ⟨ρ, hρ, hsep⟩ := exists_pos_dist_nonadjacent hα hinj (n := n + 1)
  let δ := min d ρ
  have hδ : 0 < δ := lt_min hd hρ
  have hδd : δ ≤ d := min_le_left _ _
  have hδρ : δ ≤ ρ := min_le_right _ _
  obtain ⟨m, hm, hmesh₂⟩ := exists_mesh hα (by linarith : (0 : ℝ) < δ / 4)
    (n + 1) (by omega)
  let c (j : ℕ) := α (sample ((n + 1) * m) j)
  let r := δ / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hstep : ∀ j < (n + 1) * m, Plane.supDist (c j) (c (j + 1)) < r := by
    intro j hj
    have hmem : sample ((n + 1) * m) (j + 1) ∈
        Icc (sample ((n + 1) * m) j) (sample ((n + 1) * m) (j + 1)) :=
      ⟨sample_mono (Nat.le_succ j), le_rfl⟩
    exact (Plane.supDist_comm _ _).trans_lt
      ((Plane.supDist_eq_dist_le _ _).trans_lt (hmesh₂ j hj _ hmem))
  have hcell : ∀ p j, p * m ≤ j → j ≤ p * m + m → c j ∈ subarcCell α (n + 1) p := by
    intro p j hj hj'
    exact ⟨sample ((n + 1) * m) j, sample_mem_Icc_of_block hm hj (by nlinarith), rfl⟩
  have hfar : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ k, q * m ≤ k → k ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c k) := by
    intro p q hp hq hpq j hj hj' k hk hk'
    have hdist := hsep p (by omega) q (by omega) (by omega)
      _ (hcell p j hj hj') _ (hcell q k hk hk')
    have hlt := lt_supDist_of_le_dist hρ hdist
    dsimp [r]
    linarith
  have hchain := isPlaneChain_familyChain (c := c) (N := (n + 1) * m)
    (m := m) (r := r) (n := n) squaresTwoConnected hr hn (le_of_eq (by ring)) hstep hfar
  have hcpm : ∀ p, c (p * m) = α (sample (n + 1) p) := by
    intro p
    dsimp [c]
    rw [sample_mul (k := n + 1) hm]
  have hbase : ∀ q, q < n + 1 → ∀ j, q * m ≤ j → j ≤ q * m + m →
      Plane.supDist (c j) (α (sample (n + 1) q)) < d := by
    intro q hq j hj hj'
    have hmem : sample ((n + 1) * m) j ∈ Icc (sample (n + 1) q) (sample (n + 1) (q + 1)) :=
      sample_mem_Icc_of_block hm hj (by nlinarith)
    exact (Plane.supDist_eq_dist_le _ _).trans_lt (hmesh₁ q hq _ hmem)
  refine ⟨n, m, c, r, hm, hr, hchain, ?_, ?_, ?_⟩
  · intro j hj
    exact ⟨sample ((n + 1) * m) j, sample_mem_I hj, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    obtain ⟨j, hj, hmem⟩ := exists_mem_Icc_sample (by positivity : 0 < (n + 1) * m) ht
    exact ⟨j, hj.le, (Plane.supDist_eq_dist_le _ _).trans_lt (hmesh₂ j hj t hmem)⟩
  · intro p hp j hj hj'
    have hnear : Plane.supDist (c j) (c (p * m)) < 2 * d := by
      by_cases hcase : j ≤ p * m + m
      · rw [hcpm]
        exact (hbase p (by omega) j hj hcase).trans (by linarith)
      · have h₁ : (p + 1) * m ≤ j := by nlinarith
        have h₂ : j ≤ (p + 1) * m + m := by nlinarith
        have hA := hbase (p + 1) (by omega) j h₁ h₂
        have hB : Plane.supDist (α (sample (n + 1) (p + 1))) (α (sample (n + 1) p)) < d :=
          (Plane.supDist_eq_dist_le _ _).trans_lt (hmesh₁ p (by omega) _
            ⟨sample_mono (Nat.le_succ p), le_rfl⟩)
        rw [hcpm]
        calc
          Plane.supDist (c j) (α (sample (n + 1) p)) ≤
              Plane.supDist (c j) (α (sample (n + 1) (p + 1))) +
              Plane.supDist (α (sample (n + 1) (p + 1))) (α (sample (n + 1) p)) :=
            Plane.supDist_triangle _ _ _
          _ < d + d := add_lt_add hA hB
          _ = 2 * d := by ring
    dsimp [r]
    linarith


theorem frontier_closedSquare_subset_pointSet_chainUnion
    {n m : ℕ} {c : ℕ → Plane} {r : ℝ} (hr : 0 < r)
    {j : ℕ} (hj : j ≤ (n + 1) * m) :
    frontier (Plane.closedSquare (c j) r) ⊆
      Graph.pointSet (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n)
        segmentDrawing := by
  obtain ⟨i, hi, h₁, h₂⟩ := exists_block_index (j := j) (n := n) (m := m) hj
  have hle₁ : familySquare c ((n + 1) * m) r j ≤ familyChain c ((n + 1) * m) m r i :=
    Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
      (fun _ _ _ => familySquare_le) h₁ h₂
  have hle₂ : familyChain c ((n + 1) * m) m r i ≤
      Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n :=
    Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
      (fun _ _ _ => familyChain_le) (Nat.zero_le _) (by omega)
  rw [← pointSet_familySquare (c := c) hr hj]
  exact Graph.pointSet_mono (hle₁.trans hle₂)

end Schoenflies
