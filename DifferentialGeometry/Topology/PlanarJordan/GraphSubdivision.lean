import DifferentialGeometry.Topology.PlanarJordan.ArcFamilyDrawing
import DifferentialGeometry.External.Schoenflies.ArcComplementPrep
import DifferentialGeometry.External.Schoenflies.Subarc

open Set Schoenflies
open scoped Graph

namespace Graph

noncomputable def subdivisionDrawing {β : Type*} (G : Graph Plane β) (drawing : β → ℝ → Plane)
    (n : E(G) → ℕ) (d : Σ e : E(G), Fin (n e)) : ℝ → Plane :=
  subarc (drawing d.1) (sample (n d.1) d.2) (sample (n d.1) (d.2 + 1))

theorem edgeArc_subdivisionDrawing {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} {n : E(G) → ℕ} (d : Σ e : E(G), Fin (n e)) :
    edgeArc (subdivisionDrawing G drawing n) d =
      drawing d.1 '' Icc (sample (n d.1) d.2) (sample (n d.1) (d.2 + 1)) := by
  rw [edgeArc, subdivisionDrawing, subarc_image, uIcc_of_le (sample_mono (Nat.le_succ _))]

theorem edgeArc_subdivisionDrawing_subset {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} {n : E(G) → ℕ} (d : Σ e : E(G), Fin (n e)) :
    edgeArc (subdivisionDrawing G drawing n) d ⊆ edgeArc drawing d.1 := by
  rw [edgeArc_subdivisionDrawing]
  exact image_mono (Icc_sample_subset_I (Nat.succ_le_of_lt d.2.isLt))

theorem edgeArc_eq_iUnion_subdivisionDrawing {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} {n : E(G) → ℕ} (hn : ∀ d, 0 < n d) (d : E(G)) :
    edgeArc drawing d = ⋃ i : Fin (n d), edgeArc (subdivisionDrawing G drawing n) ⟨d, i⟩ := by
  apply Subset.antisymm
  · rintro x ⟨t, ht, rfl⟩
    obtain ⟨i, hi, hit⟩ := exists_mem_Icc_sample (hn d) ht
    apply mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [edgeArc_subdivisionDrawing]
    exact mem_image_of_mem (drawing d) hit
  · exact iUnion_subset fun i => edgeArc_subdivisionDrawing_subset ⟨d, i⟩

theorem IsDrawing.subdivision {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (h : IsDrawing G drawing) (n : E(G) → ℕ) :
    IsDrawing (curveGraph (subdivisionDrawing G drawing n) V(G))
      (subdivisionDrawing G drawing n) := by
  let f := subdivisionDrawing G drawing n
  have hleft (d : Σ e : E(G), Fin (n e)) : sample (n d.1) d.2 ∈ unitInterval :=
    sample_mem_I d.2.isLt.le
  have hright (d : Σ e : E(G), Fin (n e)) : sample (n d.1) (d.2 + 1) ∈ unitInterval :=
    sample_mem_I (Nat.succ_le_of_lt d.2.isLt)
  have hV (d : Σ e : E(G), Fin (n e)) : edgeArc f d ∩ V(G) ⊆ {f d 0, f d 1} := by
    rintro x ⟨hx, hxV⟩
    rw [edgeArc_subdivisionDrawing] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htI := Icc_sample_subset_I (Nat.succ_le_of_lt d.2.isLt) ht
    have hxA : drawing d.1 t ∈ edgeArc drawing d.1 := mem_image_of_mem _ htI
    rcases h.vertex_mem_edgeArc (h.edge_param d.1.2).2.2 hxV hxA with h0 | h1
    · have ht0 := (h.edge_param d.1.2).2.1 htI zero_mem_I h0
      have ha : sample (n d.1) d.2 = 0 := by linarith [(hleft d).1, ht.1]
      left
      change drawing d.1 t = subarc (drawing d.1) _ _ 0
      rw [subarc_zero, ha, ht0]
    · have ht1 := (h.edge_param d.1.2).2.1 htI one_mem_I h1
      have hb : sample (n d.1) (d.2 + 1) = 1 := by linarith [(hright d).2, ht.2]
      right
      change drawing d.1 t = subarc (drawing d.1) _ _ 1
      rw [subarc_one, hb, ht1]
  apply isDrawing_curveGraph
  · intro d
    exact continuousOn_subarc (h.edge_param d.1.2).1 (hleft d) (hright d)
  · intro d
    exact injOn_subarc ((h.edge_param d.1.2).2.1.mono (uIcc_subset_I (hleft d) (hright d)))
      (sample_strictMono (Nat.zero_lt_of_lt d.2.isLt) (Nat.lt_succ_self _)).ne
  · exact hV
  · intro d j hdj x hx
    by_cases heq : d.1 = j.1
    · rcases d with ⟨d, i⟩
      rcases j with ⟨j, k⟩
      dsimp only at heq
      subst j
      have hik : i ≠ k := fun hik => hdj (by cases hik; rfl)
      rw [edgeArc_subdivisionDrawing, edgeArc_subdivisionDrawing] at hx
      obtain ⟨⟨t, ht, rfl⟩, ⟨u, hu, heq⟩⟩ := hx
      have htu := (h.edge_param d.2).2.1
        (Icc_sample_subset_I (Nat.succ_le_of_lt k.isLt) hu)
        (Icc_sample_subset_I (Nat.succ_le_of_lt i.isLt) ht) heq
      subst u
      rcases lt_or_gt_of_ne hik with hik | hki
      · have hle := sample_mono (n := n d) (Nat.succ_le_of_lt hik)
        have htend : t = sample (n d) (i + 1) := by linarith [ht.2, hu.1]
        right
        change drawing d t = subarc (drawing d) _ _ 1
        rw [subarc_one, htend]
      · have hle := sample_mono (n := n d) (Nat.succ_le_of_lt hki)
        have htend : t = sample (n d) i := by linarith [ht.1, hu.2]
        left
        change drawing d t = subarc (drawing d) _ _ 0
        rw [subarc_zero, htend]
    · exact hV d ⟨hx.1, h.arcs_meet_at_vertex d.1.2 j.1.2
        (fun he => heq (Subtype.ext he))
        (edgeArc_subdivisionDrawing_subset d hx.1) (edgeArc_subdivisionDrawing_subset j hx.2)⟩

theorem pointSet_subdivisionDrawing {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} {n : E(G) → ℕ} (hn : ∀ d, 0 < n d) :
    pointSet (curveGraph (subdivisionDrawing G drawing n) V(G)) (subdivisionDrawing G drawing n) =
      pointSet G drawing := by
  let f := subdivisionDrawing G drawing n
  apply Subset.antisymm
  · rintro x (((hx | ⟨d, rfl⟩) | ⟨d, rfl⟩) | hx)
    · exact vertexSet_subset_pointSet hx
    · exact edgeArc_subset_pointSet d.1.2 (edgeArc_subdivisionDrawing_subset d
        (mem_image_of_mem (f d) zero_mem_I))
    · exact edgeArc_subset_pointSet d.1.2 (edgeArc_subdivisionDrawing_subset d
        (mem_image_of_mem (f d) one_mem_I))
    · obtain ⟨d, _, hd⟩ := mem_iUnion₂.mp hx
      exact edgeArc_subset_pointSet d.1.2 (edgeArc_subdivisionDrawing_subset d hd)
  · rintro x (hx | hx)
    · exact Or.inl (Or.inl (Or.inl hx))
    · obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
      rw [edgeArc_eq_iUnion_subdivisionDrawing hn ⟨d, hd⟩] at hxd
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxd
      exact edgeArc_subset_pointSet (G := curveGraph f V(G)) (mem_univ ⟨⟨d, hd⟩, i⟩) hi

open Classical in
theorem IsDrawing.exists_subdivisionDrawing_diam_lt {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (h : IsDrawing G drawing) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : E(G) → ℕ, (∀ d, 0 < n d) ∧
      ∀ d : Σ e : E(G), Fin (n e), Metric.diam (edgeArc (subdivisionDrawing G drawing n) d) < ε := by
  have hmesh (d : E(G)) := exists_mesh (h.edge_param d.2).1
    (show 0 < ε / 4 by positivity) 1 zero_lt_one
  choose n hn hsmall using hmesh
  simp only [one_mul] at hsmall
  refine ⟨n, hn, fun d => ?_⟩
  have hball : edgeArc (subdivisionDrawing G drawing n) d ⊆
      Metric.closedBall (drawing d.1 (sample (n d.1) d.2)) (ε / 4) := by
    rw [edgeArc_subdivisionDrawing]
    rintro x ⟨t, ht, rfl⟩
    exact (hsmall d.1 d.2 d.2.isLt t ht).le
  exact (Metric.diam_le_of_subset_closedBall (by positivity) hball).trans_lt (by linarith)

end Graph
