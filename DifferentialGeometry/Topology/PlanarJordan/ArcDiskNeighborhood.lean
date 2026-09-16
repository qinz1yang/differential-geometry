import DifferentialGeometry.External.Schoenflies.SquareCycle
import DifferentialGeometry.External.Schoenflies.FaceCyclesLand

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies
open scoped Graph

private theorem exists_square_chain {α : ℝ → Plane}
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

open Classical in
theorem exists_polygonal_jordan_neighborhood_of_isArc {A U : Set Plane}
    (hA : IsArc A) (hU : U ∈ 𝓝ˢ A) :
    ∃ J : Set Plane, IsJordanCurve J ∧ IsPolygonal J ∧ A ⊆ inside J ∧ closure (inside J) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := (Metric.hasBasis_nhdsSet_thickening hA.isCompact).mem_iff.mp hU
  obtain ⟨α, hα, hinj, hαA⟩ := hA
  obtain ⟨n, m, c, r, hm, hr, hchain, hc, hcover, hnear⟩ :=
    exists_square_chain hα hinj (div_pos hε (by norm_num : (0 : ℝ) < 8))
  let G := Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n
  let _ : G.Finite := hchain.block_finite (by omega)
  have hdraw : G.IsDrawing segmentDrawing := hchain.block_isDrawing (by omega)
  obtain ⟨b, hb, hbunb⟩ := Graph.exists_unbounded_face hdraw
  obtain ⟨e, u, v, D, hface⟩ := Graph.face_cycles' hdraw
    (hchain.block_polygonal (by omega)) (hchain.block_isTwoConnected (by omega)) b hb
  let J := Graph.edgesCover segmentDrawing (e :: D)
  have hJ : IsJordanCurve J := hdraw.cycle_isJordanCurve hface.isCycle
  have hpoly : IsPolygonal J := hdraw.isPolygonal_edgesCover
    (hchain.block_polygonal (by omega)) hface.isCycle.isWalk_cons (List.cons_ne_nil _ _)
  have hout : Graph.face G segmentDrawing b = outside J :=
    hface.eq_inside_or_outside.resolve_left fun heq => hbunb (heq ▸ hface.isSeparating.isBounded_inside)
  have hfr (j : ℕ) (hj : j ≤ (n + 1) * m) :
      frontier (Plane.closedSquare (c j) r) ⊆ Graph.pointSet G segmentDrawing := by
    obtain ⟨i, hi, h₁, h₂⟩ := exists_block_index (j := j) (n := n) (m := m) hj
    have hle₁ : familySquare c ((n + 1) * m) r j ≤ familyChain c ((n + 1) * m) m r i :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familySquare_le) h₁ h₂
    have hle₂ : familyChain c ((n + 1) * m) m r i ≤ G :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familyChain_le) (Nat.zero_le _) (by omega)
    rw [← pointSet_familySquare (c := c) hr hj]
    exact Graph.pointSet_mono (hle₁.trans hle₂)
  refine ⟨J, hJ, hpoly, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := hcover x (hαA.symm ▸ hx)
    have hxcl : x ∉ closure (Graph.face G segmentDrawing b) := by
      intro hxcl
      obtain ⟨z, hzj, hzF⟩ := mem_closure_iff_nhds.mp hxcl _
        ((Plane.isOpen_openSquare (c j) r).mem_nhds hxj)
      exact notMem_face_of_mem_openSquare (hfr j hj) hbunb hzj hzF
    have hxJ : x ∉ J := fun h => hxcl
      (frontier_subset_closure (hface.frontier_eq.symm ▸ h))
    have hxIO : x ∈ inside J ∪ outside J := by rw [inside_union_outside]; exact hxJ
    exact hxIO.resolve_right fun h => hxcl (subset_closure (hout.symm ▸ h))
  · intro x hx
    apply hεU
    by_contra hxε
    have hfar : ∀ p, p + 1 ≤ n → 3 * (ε / 8) < Plane.supDist x (c (p * m)) := by
      intro p hp
      have hcm : c (p * m) ∈ A := hαA ▸ hc (p * m) (by nlinarith)
      have hdist : ε ≤ dist x (c (p * m)) := le_of_not_gt fun hlt => hxε
        (Metric.mem_thickening_iff.mpr ⟨c (p * m), hcm, hlt⟩)
      have hlt := lt_supDist_of_le_dist hε hdist
      linarith
    obtain ⟨hxG, hxu⟩ := outer_face_familyChain hchain (outerOnPairs_familyChain hnear hfar)
    have hxout : x ∈ outside J := by
      rw [← hout, ← Graph.unbounded_face_unique hdraw hxu hbunb]
      exact Graph.mem_face hxG
    rw [(IsRegionOf.inside J).closure_eq hface.isSeparating] at hx
    rcases hx with hx | hx
    · exact disjoint_left.mp disjoint_inside_outside hx hxout
    · exact hxout.1 hx

end DifferentialGeometry.Topology.PlanarJordan
