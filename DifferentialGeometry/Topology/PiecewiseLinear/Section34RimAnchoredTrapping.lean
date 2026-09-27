import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingRimSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorRegionTrapping

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem component_closure_trapping_reanchor {X : Type*} [TopologicalSpace X]
    {D T : Set X} {a b : X}
    (htrap : ∀ y ∈ D, y ∉ connectedComponentIn D a →
      closure (connectedComponentIn D y) ⊆ T) (hb : b ∈ D) (hbT : b ∉ T) :
    ∀ y ∈ D, y ∉ connectedComponentIn D b → closure (connectedComponentIn D y) ⊆ T := by
  have hbC : b ∈ connectedComponentIn D a := by
    by_contra hnot
    exact hbT (htrap b hb hnot (subset_closure (mem_connectedComponentIn hb)))
  intro y hy hyn
  apply htrap y hy
  rwa [connectedComponentIn_eq hbC]

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_distinguished_rim_anchors
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ a ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1),
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      a ∈ G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e ∧
      b ∈ G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e ∧ a ∉ Tp e ∧ b ∉ Tp e ∧
      (∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a) ∧
      ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨x, hx⟩ := hann.ends_nonempty.1
  obtain ⟨y, hy⟩ := hann.ends_nonempty.2
  have hex : ∃ a ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1),
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      a ∈ G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e ∧
      b ∈ G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e := by
    rcases section34_opposite_second_rim_sides hprep hpack e with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact ⟨x, ⟨hann.first_subset hx, h₀ hx⟩, y, ⟨hann.second_subset hy, h₁ hy⟩,
        Or.inl hx, Or.inr hy⟩
    · exact ⟨y, ⟨hann.second_subset hy, h₁ hy⟩, x, ⟨hann.first_subset hx, h₀ hx⟩,
        Or.inr hy, Or.inl hx⟩
  obtain ⟨a, ha, b, hb, haR, hbR⟩ := hex
  obtain ⟨-, -, -, -, -, -, -, -, hends, -, -, -, -, -, hin, hout, -⟩ := hpack
  have hdis : Disjoint (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) (Tp e) := by
    rw [← image_union]
    exact (hends e).2
  have haT := disjoint_left.mp hdis haR
  have hbT := disjoint_left.mp hdis hbR
  obtain ⟨a₀, -, hinside⟩ := hin e
  obtain ⟨b₀, -, houtside⟩ := hout e
  have haa := hinside a ⟨ha.1, interior_subset ha.2⟩ haT
  have hbb := houtside b hb hbT
  refine ⟨a, ha, b, hb, haR, hbR, haT, hbT, ?_, ?_⟩
  · exact fun z hz hzT => (connectedComponentIn_eq haa) ▸ hinside z hz hzT
  · exact fun z hz hzT => (connectedComponentIn_eq hbb) ▸ houtside z hz hzT

theorem section34_region_subset_inner_tube_of_rim_avoidance
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {R : Set M₂}
    (hR : IsClosed R) (hconn : IsPreconnected R)
    (hRB : R ⊆ G (ends e).2 '' CpBd (ends e).2)
    (hmeet : (R ∩ G (ends e).2 '' Bb e).Nonempty)
    (hcomponent : ∀ z ∈ R \ G (ends e).1 '' CpBd (ends e).1,
      connectedComponentIn
        (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R)
    (hdis : Disjoint R (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e)) :
    R ⊆ G (ends e).2 '' Bb e ∩ Tp e := by
  obtain ⟨a, ha, b, hb, haR, hbR, -, -, hin, hout⟩ :=
    exists_section34_distinguished_rim_anchors hprep hpack e
  exact section34_region_subset_inner_tube_of_anchor_avoidance hprep hpack e
    ⟨ha.1, interior_subset ha.2⟩ hb hin hout hR hconn hRB hmeet hcomponent
    (fun hx => disjoint_left.mp hdis hx haR) (fun hx => disjoint_left.mp hdis hx hbR)

theorem section34_region_subset_inner_tube_interior_of_rim_avoidance
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hanchors : ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
        (∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
        ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e))
    {R : Set M₂} (hR : IsClosed R) (hconn : IsPreconnected R)
    (hRB : R ⊆ G (ends e).2 '' CpBd (ends e).2)
    (hmeet : (R ∩ G (ends e).2 '' Bb e).Nonempty)
    (hcomponent : ∀ z ∈ R \ G (ends e).1 '' CpBd (ends e).1,
      connectedComponentIn
        (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R)
    (hdis : Disjoint R (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e)) :
    R ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e) := by
  obtain ⟨a, ha, b, hb, haR, hbR, haT, hbT, -, -⟩ :=
    exists_section34_distinguished_rim_anchors hprep hpack e
  obtain ⟨a₀, -, b₀, -, hin, hout⟩ := hanchors
  have hin' := component_closure_trapping_reanchor hin
    ⟨ha.1, interior_subset ha.2⟩ (fun hx => haT (interior_subset hx))
  have hout' := component_closure_trapping_reanchor hout hb
    (fun hx => hbT (interior_subset hx))
  exact section34_region_subset_inner_tube_interior_of_anchor_avoidance hprep hpack e
    ⟨ha.1, interior_subset ha.2⟩ hb hin' hout' hR hconn hRB hmeet hcomponent
    (fun hx => disjoint_left.mp hdis hx haR) (fun hx => disjoint_left.mp hdis hx hbR)

end DifferentialGeometry.Topology.PiecewiseLinear
