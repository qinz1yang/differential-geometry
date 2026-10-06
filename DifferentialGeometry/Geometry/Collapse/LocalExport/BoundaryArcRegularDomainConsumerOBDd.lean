import DifferentialGeometry.Topology.Manifold.OneManifold.ArcRegularDomainOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimAtlasBCF

/-!
# Consumers of the arc / interval kernels (lane S-BD2d, suffix `_OBDd`), group G10c

* `exists_Icc_decomposition_Icc_OBDd`: the decomposition kernel applied to the closed interval
  `A = [a, b] ⊆ [0, 1]` (frontier `{a, b}`, no isolated point) — a compiled inhabitant of its
  hypotheses;
* `exists_open_inter_subset_arc_image_line_OBDd`: the open-neighbourhood kernel for the line
  `ℝ¹` with its identity graph atlas and the arc `t ↦ t • e₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology

namespace DifferentialGeometry.Topology

/-- The decomposition kernel on `A = [a, b]`. -/
theorem exists_Icc_decomposition_Icc_OBDd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (N : ℕ) (s e : Fin N → ℝ), (∀ i, s i < e i) ∧
      (∀ i, s i ∈ frontier (Icc a b) ∧ e i ∈ frontier (Icc a b)) ∧
      Icc a b = ⋃ i, Icc (s i) (e i) ∧
      Pairwise fun i j => Disjoint (Icc (s i) (e i)) (Icc (s j) (e j)) := by
  refine exists_Icc_decomposition_OBDd (F := {a, b}) isClosed_Icc
    (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩) (Set.toFinite _) ?_ ?_
  · rw [frontier_Icc hab.le]
  · intro t ht δ hδ
    by_cases hlt : t + min (δ / 2) ((b - a) / 2) ≤ b
    · refine ⟨t + min (δ / 2) ((b - a) / 2), ⟨by
        have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
        linarith [ht.1], hlt⟩, by
        have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
        linarith, ?_⟩
      have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
      rw [add_sub_cancel_left, abs_of_pos this]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · refine ⟨t - min (δ / 2) ((b - a) / 2), ⟨by
        have h1 := min_le_right (δ / 2) ((b - a) / 2)
        have h2 := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
        linarith [not_le.1 hlt, ht.2], by
        have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
        linarith [ht.2]⟩, by
        have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
        linarith, ?_⟩
      have := lt_min (half_pos hδ) (half_pos (sub_pos.2 hab))
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos this]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- The open-neighbourhood kernel on the line `ℝ¹` (identity graph atlas) and the arc
`t ↦ t • e₀`. -/
theorem exists_open_inter_subset_arc_image_line_OBDd {t₀ δ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 < δ) :
    ∃ G : Set (EuclideanSpace ℝ (Fin 1)), IsOpen G ∧
      t₀ • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ G ∧
      G ∩ univ ⊆ (fun t : ℝ => t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ''
        Ioo (t₀ - δ) (t₀ + δ) := by
  obtain ⟨At⟩ := DifferentialGeometry.Geometry.Collapse.exists_graphAtlas_euclidLine_BCF
  have hne : EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp at this
  exact exists_open_inter_subset_arc_image_OBDd At
    (continuous_id.smul continuous_const).continuousOn
    (fun x _ y _ h => smul_left_injective ℝ hne h) (mapsTo_univ _ _) ht₀ hδ

end DifferentialGeometry.Topology
