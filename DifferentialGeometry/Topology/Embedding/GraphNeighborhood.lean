import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith

open Set Topology

namespace Topology.IsInducing

theorem exists_isOpen_inter_range_eq_graph
    {E F M : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace M]
    {e : M → E × F} (he : IsInducing e) (χ : OpenPartialHomeomorph E M)
    {s : Set E} (hs : IsOpen s) (hsource : s ⊆ χ.source)
    {q : E → F} (hgraph : ∀ y ∈ s, e (χ y) = (y, q y)) :
    ∃ U : Set (E × F), IsOpen U ∧ (fun y => (y, q y)) '' s ⊆ U ∧ U ⊆ s ×ˢ univ ∧
      U ∩ range e = U ∩ {z | z.2 = q z.1} := by
  obtain ⟨V, hV, hpre⟩ := he.isOpen_iff.mp (χ.isOpen_image_of_subset_source hs hsource)
  refine ⟨V ∩ s ×ˢ univ, hV.inter (hs.prod isOpen_univ), ?_, inter_subset_right, ?_⟩
  · rintro z ⟨a, ha, rfl⟩
    refine ⟨?_, ha, mem_univ _⟩
    change (a, q a) ∈ V
    rw [← hgraph a ha]
    change χ a ∈ e ⁻¹' V
    rw [hpre]
    exact mem_image_of_mem χ ha
  · ext z
    constructor
    · rintro ⟨hz, x, hx⟩
      have hxV : x ∈ e ⁻¹' V := by
        change e x ∈ V
        rw [hx]
        exact hz.1
      rw [hpre] at hxV
      obtain ⟨y, hy, hxy⟩ := hxV
      have heq : (y, q y) = z := (hgraph y hy).symm.trans (hxy ▸ hx)
      exact ⟨hz, heq ▸ rfl⟩
    · rintro ⟨hz, hq⟩
      refine ⟨hz, χ z.1, ?_⟩
      exact (hgraph z.1 hz.2.1).trans (Prod.ext rfl hq.symm)

open Metric

theorem exists_prod_closedBall_inter_range_eq_graph
    {E F M : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [TopologicalSpace M]
    {e : M → E × F} (he : IsInducing e) (χ : OpenPartialHomeomorph E M)
    {s : Set E} (hs : IsOpen s) (hsource : s ⊆ χ.source)
    {q : E → F} (hgraph : ∀ y ∈ s, e (χ y) = (y, q y)) {a : E} (ha : a ∈ s)
    (hq : ContinuousAt q a) :
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧ closedBall a r ⊆ s ∧
      (∀ y ∈ closedBall a r, q y ∈ ball (q a) t) ∧
      (closedBall a r ×ˢ closedBall (q a) t) ∩ range e =
        (fun y => (y, q y)) '' closedBall a r := by
  obtain ⟨U, hU, hgraphU, hUs, hUr⟩ :=
    he.exists_isOpen_inter_range_eq_graph χ hs hsource hgraph
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp
    (hU.mem_nhds (hgraphU (mem_image_of_mem _ ha)))
  obtain ⟨δ, hδ, hδq⟩ := Metric.mem_nhds_iff.mp
    (hq.preimage_mem_nhds (ball_mem_nhds (q a) (half_pos hR)))
  let r := min (R / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hδ)
  have hrR : r < R := (min_le_left _ _).trans_lt (by linarith)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
  have hprod : closedBall a r ×ˢ closedBall (q a) (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz.1).trans_lt hrR,
      (mem_closedBall.mp hz.2).trans_lt (by linarith)⟩
  have hrs : closedBall a r ⊆ s := by
    intro y hy
    exact (hUs (hprod (show (y, q a) ∈ closedBall a r ×ˢ closedBall (q a) (R / 2) from
      ⟨hy, mem_closedBall_self (half_pos hR).le⟩))).1
  have hrq : ∀ y ∈ closedBall a r, q y ∈ ball (q a) (R / 2) := by
    intro y hy
    exact hδq (closedBall_subset_ball hrδ hy)
  refine ⟨r, hr, R / 2, half_pos hR, hrs, hrq, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hze⟩
    have hzq : z.2 = q z.1 := by
      have h : z ∈ U ∩ range e := ⟨hprod hz, hze⟩
      rw [hUr] at h
      exact h.2
    exact ⟨z.1, hz.1, Prod.ext rfl hzq.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨hy, ball_subset_closedBall (hrq y hy)⟩, χ y, hgraph y (hrs hy)⟩

end Topology.IsInducing
