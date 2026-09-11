import DifferentialGeometry.Topology.Embedding.ProductChartEndpoint
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Embedding

theorem exists_inward_segment_of_graph_chart_endpoint
    {X Y N : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace N] [CompactSpace N] [PreconnectedSpace N] [Nonempty N]
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (P K Q : Set X) (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (Sminus Splus : Set X)
    (hboundary : frontier (range f) = f '' Sminus ∪ f '' Splus)
    (hplusQ : Splus ⊆ Q) (hinternal : f '' K ⊆ interior (range f))
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens Y) (Φ : O ≃ₜ V)
    (t₀ : ℝ) (a b : N → ℝ) (ha : Continuous a) (hb : Continuous b)
    (h₀a : ∀ p, t₀ < a p) (hab : ∀ p, a p < b p)
    (hstrip : {x : N × ℝ | t₀ ≤ x.2 ∧ x.2 ≤ b x.1} ⊆ O)
    (hminus : f '' Sminus = range (fun p : N ↦
      (Φ ⟨(p, t₀), hstrip ⟨le_rfl, ((h₀a p).trans (hab p)).le⟩⟩ : Y)))
    (hcollar : f '' K = (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}))
    (hfar : f '' (K ∩ Q) ⊆ range (fun p : N ↦
      (Φ ⟨(p, b p), hstrip ⟨((h₀a p).trans (hab p)).le, le_rfl⟩⟩ : Y))) :
    ∃ r : ℝ, 0 < r ∧
      ∃ hsegment : (univ : Set N) ×ˢ Icc t₀ (t₀ + r) ⊆ O,
        ∀ p : N, ∀ t (ht : t ∈ Icc t₀ (t₀ + r)),
          (Φ ⟨(p, t), hsegment ⟨mem_univ _, ht⟩⟩ : Y) ∈ range f := by
  obtain ⟨p₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (univ_nonempty : (univ : Set N).Nonempty) hb.continuousOn
  let r := b p₀ - t₀
  have hr : 0 < r := sub_pos.mpr ((h₀a p₀).trans (hab p₀))
  have hle (p : N) : t₀ + r ≤ b p := by
    have hp : b p₀ ≤ b p := hmin (mem_univ p)
    dsimp [r]
    linarith only [hp]
  have hsegment : (univ : Set N) ×ˢ Icc t₀ (t₀ + r) ⊆ O := by
    rintro x ⟨_, hx⟩
    exact hstrip ⟨hx.1, hx.2.trans (hle x.1)⟩
  refine ⟨r, hr, hsegment, ?_⟩
  intro p t ht
  exact graph_chart_endpoint_strip_subset_range f hf P K Q hP hK hQ hcover hdisj
    Sminus Splus hboundary hplusQ hinternal O V Φ t₀ a b ha hb h₀a hab hstrip
    hminus hcollar hfar p t ⟨ht.1, ht.2.trans (hle p)⟩

end DifferentialGeometry.Topology.Embedding
