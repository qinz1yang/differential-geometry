import DifferentialGeometry.Topology.Connected.SeparatingCollarStrip
import DifferentialGeometry.Topology.GraphBandChart

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Embedding

theorem cover_and_between_subset_of_chart_graph_collars
    {X Y N : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace N] [CompactSpace N] [Nonempty N]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (P₀ K₀ Q₀ P₁ K₁ Q₁ : Set X)
    (hP₀ : IsClosed P₀) (hK₀ : IsClosed K₀) (hQ₀ : IsClosed Q₀)
    (hP₁ : IsClosed P₁) (hK₁ : IsClosed K₁) (hQ₁ : IsClosed Q₁)
    (hcover₀ : P₀ ∪ K₀ ∪ Q₀ = univ) (hcover₁ : P₁ ∪ K₁ ∪ Q₁ = univ)
    (hdisj₀ : Disjoint P₀ Q₀) (hdisj₁ : Disjoint P₁ Q₁)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens Y) (Φ : O ≃ₜ V)
    (a b c d : N → ℝ) (ha : Continuous a) (hd : Continuous d)
    (hab : ∀ p, a p < b p) (hbc : ∀ p, b p < c p) (hcd : ∀ p, c p < d p)
    (l r : ℝ) (hla : ∀ p, l ≤ a p) (hdr : ∀ p, d p ≤ r)
    (htrunc : (univ : Set N) ×ˢ Icc l r ⊆ O)
    (himage₀ : f '' K₀ = (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}))
    (himage₁ : f '' K₁ = (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x : N × ℝ | c x.1 ≤ x.2 ∧ x.2 ≤ d x.1}))
    (hleft : (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' range (fun p : N ↦ (p, a p))) ⊆ f '' (P₀ ∩ K₀))
    (hright : (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' range (fun p : N ↦ (p, d p))) ⊆ f '' (K₁ ∩ Q₁)) :
    let D := (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ d x.1})
    let T := (fun x : O ↦ (Φ x : Y)) ''
      ((Subtype.val : O → N × ℝ) ⁻¹' ((univ : Set N) ×ˢ Icc l r))
    P₀ ∪ f ⁻¹' D ∪ Q₁ = univ ∧
      (interior P₀)ᶜ ∩ (interior Q₁)ᶜ ⊆ f ⁻¹' D ∧ D ⊆ T := by
  intro D T
  let A : Set (N × ℝ) := {x | a x.1 ≤ x.2 ∧ x.2 ≤ d x.1}
  have had (p : N) : a p < d p := (hab p).trans ((hbc p).trans (hcd p))
  have hAO : A ⊆ O := fun x hx ↦
    htrunc ⟨mem_univ _, (hla x.1).trans hx.1, hx.2.trans (hdr x.1)⟩
  have hKD₀ : K₀ ⊆ f ⁻¹' D := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := himage₀ ▸ (show f x ∈ f '' K₀ from ⟨x, hx, rfl⟩)
    exact ⟨y, ⟨hy.1, hy.2.trans ((hbc (y : N × ℝ).1).trans (hcd (y : N × ℝ).1)).le⟩, hxy⟩
  have hKD₁ : K₁ ⊆ f ⁻¹' D := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := himage₁ ▸ (show f x ∈ f '' K₁ from ⟨x, hx, rfl⟩)
    exact ⟨y, ⟨((hab (y : N × ℝ).1).trans (hbc (y : N × ℝ).1)).le.trans hy.1, hy.2⟩, hxy⟩
  have hne : K₀.Nonempty := by
    let p : N := Classical.choice inferInstance
    have hxA : (p, a p) ∈ A := ⟨le_rfl, (had p).le⟩
    have hx : (Φ ⟨(p, a p), hAO hxA⟩ : Y) ∈ f '' K₀ := by
      rw [himage₀]
      exact ⟨⟨(p, a p), hAO hxA⟩, ⟨le_rfl, (hab p).le⟩, rfl⟩
    obtain ⟨x, hx, _⟩ := hx
    exact ⟨x, hx⟩
  have hfront : frontier (f ⁻¹' D) ⊆ (P₀ ∩ K₀) ∪ (K₁ ∩ Q₁) := by
    intro x hx
    have hfx := hf.frontier_preimage_subset D hx
    change f x ∈ frontier D at hfx
    rw [frontier_graphBand_of_opens_product_chart O V Φ a d ha hd had hAO] at hfx
    rcases hfx with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact Or.inl (hinj.mem_set_image.mp
        (hleft ⟨⟨(p, a p), hAO ⟨le_rfl, (had p).le⟩⟩, ⟨p, rfl⟩, hp⟩))
    · exact Or.inr (hinj.mem_set_image.mp
        (hright ⟨⟨(p, d p), hAO ⟨(had p).le, le_rfl⟩⟩, ⟨p, rfl⟩, hp⟩))
  obtain ⟨hcover, hbetween⟩ := cover_and_between_subset_of_separating_collars
    P₀ K₀ Q₀ P₁ K₁ Q₁ (f ⁻¹' D) hP₀ hK₀ hQ₀ hP₁ hK₁ hQ₁
    hcover₀ hcover₁ hdisj₀ hdisj₁ hne hKD₀ hKD₁ hfront
  refine ⟨hcover, hbetween, image_mono ?_⟩
  intro x hx
  exact ⟨mem_univ _, (hla (x : N × ℝ).1).trans hx.1,
    hx.2.trans (hdr (x : N × ℝ).1)⟩

end DifferentialGeometry.Topology.Embedding
