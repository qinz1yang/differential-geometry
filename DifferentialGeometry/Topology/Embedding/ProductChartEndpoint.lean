import DifferentialGeometry.Topology.Connected.EndpointStripRange
import DifferentialGeometry.Topology.GraphBandChart

noncomputable section
open Set Topology

namespace Poincare.Topology.Embedding

theorem graph_chart_endpoint_strip_subset_range
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
    ∀ p : N, ∀ t (ht : t₀ ≤ t ∧ t ≤ b p),
      (Φ ⟨(p, t), hstrip ht⟩ : Y) ∈ range f := by
  let A : Set (N × ℝ) := {x | t₀ ≤ x.2 ∧ x.2 ≤ b x.1}
  let B : Set (N × ℝ) := {x | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}
  let F : O → Y := fun x ↦ Φ x
  let D := F '' ((Subtype.val : O → N × ℝ) ⁻¹' A)
  have hBO : B ⊆ O := fun x hx ↦ hstrip ⟨(h₀a x.1).le.trans hx.1, hx.2⟩
  have hAc : IsCompact A := isCompact_graphBand (fun _ : N ↦ t₀) b
    continuous_const hb (fun p ↦ (h₀a p).trans (hab p))
  have hAr : closure (interior A) = A := by
    rw [interior_graphBand (fun _ : N ↦ t₀) b continuous_const hb
      (fun p ↦ (h₀a p).trans (hab p)),
      closure_openGraphBand (fun _ : N ↦ t₀) b continuous_const hb
        (fun p ↦ (h₀a p).trans (hab p))]
  have hAi : IsPreconnected (interior A) := by
    rw [interior_graphBand (fun _ : N ↦ t₀) b continuous_const hb
      (fun p ↦ (h₀a p).trans (hab p))]
    exact isPreconnected_openGraphBand (fun _ : N ↦ t₀) b continuous_const hb
      (fun p ↦ (h₀a p).trans (hab p))
  have hDreg : closure (interior D) = D :=
    closure_interior_opens_chart_image O V Φ hAc hstrip hAr
  have hDconn : IsPreconnected (interior D) :=
    isPreconnected_interior_opens_chart_image O V Φ hAi (interior_subset.trans hstrip)
  have hKD : f '' K ⊆ D := by
    rw [hcollar]
    apply image_mono
    intro x hx
    exact ⟨(h₀a (x : N × ℝ).1).le.trans hx.1, hx.2⟩
  have hKne : (interior (f '' K)).Nonempty := by
    rw [hcollar, interior_opens_chart_image O V Φ B, interior_graphBand a b ha hb hab]
    let p : N := Classical.choice inferInstance
    have hc : a p < (a p + b p) / 2 ∧ (a p + b p) / 2 < b p := by
      constructor <;> linarith [hab p]
    exact ⟨F ⟨(p, (a p + b p) / 2), hBO ⟨hc.1.le, hc.2.le⟩⟩,
      ⟨(p, (a p + b p) / 2), hBO ⟨hc.1.le, hc.2.le⟩⟩, hc, rfl⟩
  have hsections : f '' Sminus ∪ f '' (K ∩ Q) ⊆ frontier D := by
    rw [frontier_graphBand_of_opens_product_chart O V Φ (fun _ : N ↦ t₀) b
      continuous_const hb (fun p ↦ (h₀a p).trans (hab p)) hstrip, hminus]
    exact union_subset_union subset_rfl hfar
  have hDinside := endpoint_strip_subset_image_of_embedded_collar f hf P K Q hP hK hQ
    hcover hdisj Sminus Splus hboundary.le hplusQ
    (by rw [hboundary]; exact subset_union_right) hinternal D hDreg hDconn hKD hKne hsections
  intro p t ht
  exact image_subset_range f (P ∪ K) (hDinside ⟨⟨(p, t), hstrip ht⟩, ht, rfl⟩)

theorem product_chart_endpoint_strip_subset_range
    {X Y N : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace N] [CompactSpace N] [PreconnectedSpace N] [Nonempty N]
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (P K Q : Set X) (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (Sminus Splus : Set X)
    (hboundary : frontier (range f) = f '' Sminus ∪ f '' Splus)
    (hplusQ : Splus ⊆ Q) (hinternal : f '' K ⊆ interior (range f))
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens Y) (Φ : O ≃ₜ V)
    (t₀ a b : ℝ) (h₀a : t₀ < a) (hab : a < b)
    (hstrip : (univ : Set N) ×ˢ Icc t₀ b ⊆ O)
    (hminus : f '' Sminus = range (fun p : N ↦
      (Φ ⟨(p, t₀), hstrip ⟨mem_univ _, le_rfl, (h₀a.trans hab).le⟩⟩ : Y)))
    (hcollar : f '' K = range (fun x : N × Icc a b ↦
      (Φ ⟨(x.1, (x.2 : ℝ)),
        hstrip ⟨mem_univ _, h₀a.le.trans x.2.property.1, x.2.property.2⟩⟩ : Y)))
    (hfar : f '' (K ∩ Q) ⊆ range (fun p : N ↦
      (Φ ⟨(p, b), hstrip ⟨mem_univ _, (h₀a.trans hab).le, le_rfl⟩⟩ : Y))) :
    ∀ p : N, ∀ t (ht : t ∈ Icc t₀ b),
      (Φ ⟨(p, t), hstrip ⟨mem_univ _, ht⟩⟩ : Y) ∈ range f := by
  have hcollar' : f '' K = (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x : N × ℝ | a ≤ x.2 ∧ x.2 ≤ b}) := by
    rw [hcollar]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x.1, (x.2 : ℝ)),
        hstrip ⟨mem_univ _, h₀a.le.trans x.2.property.1, x.2.property.2⟩⟩,
          x.2.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((x : N × ℝ).1, ⟨(x : N × ℝ).2, hx⟩), rfl⟩
  exact graph_chart_endpoint_strip_subset_range f hf P K Q hP hK hQ hcover hdisj
    Sminus Splus hboundary hplusQ hinternal O V Φ t₀ (fun _ ↦ a) (fun _ ↦ b)
    continuous_const continuous_const (fun _ ↦ h₀a) (fun _ ↦ hab)
    (fun x hx ↦ hstrip ⟨mem_univ x.1, hx⟩) hminus hcollar' hfar

end Poincare.Topology.Embedding
