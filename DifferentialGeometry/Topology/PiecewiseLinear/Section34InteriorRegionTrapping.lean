import DifferentialGeometry.Topology.PiecewiseLinear.Section34DistinguishedComponents

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem section34_region_subset_inner_tube_interior_of_anchor_avoidance
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {a b : M₂} {R : Set M₂}
    (ha : a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1)
    (hb : b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1)
    (hin : ∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      y ∉ connectedComponentIn
        (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
      closure (connectedComponentIn
        (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e))
    (hout : ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      y ∉ connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
      closure (connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e))
    (hR : IsClosed R) (hconn : IsPreconnected R)
    (hRB : R ⊆ G (ends e).2 '' CpBd (ends e).2)
    (hmeet : (R ∩ G (ends e).2 '' Bb e).Nonempty)
    (hcomponent : ∀ z ∈ R \ G (ends e).1 '' CpBd (ends e).1,
      connectedComponentIn
        (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R)
    (haR : a ∉ R) (hbR : b ∉ R) : R ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e) := by
  have hinside : ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a := by
    intro z hz hzT
    by_contra hn
    exact hzT (interior_subset (hin z hz hn (subset_closure (mem_connectedComponentIn hz))))
  have houtside : ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b := by
    intro z hz hzT
    by_contra hn
    exact hzT (interior_subset (hout z hz hn (subset_closure (mem_connectedComponentIn hz))))
  have hbase := section34_region_subset_inner_tube_of_anchor_avoidance hprep hpack e
    ha hb hinside houtside hR hconn hRB hmeet hcomponent haR hbR
  have hinsideEq := section34_inside_component_closure_eq hprep hpack e
  have houtsideEq := section34_trace_free_component_eq_outside hprep hpack e
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, htrace, -, -, -, hG, -⟩ := hpack
  have hBbB : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  intro z hz
  have hzB := (hbase hz).1
  refine ⟨hzB, ?_⟩
  by_cases hzBd : z ∈ G (ends e).1 '' CpBd (ends e).1
  · exact (htrace e ⟨hzBd, hRB hz⟩).2
  have hcc : connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R :=
    (connectedComponentIn_mono z (sdiff_subset_sdiff_left hBbB)).trans
      (hcomponent z ⟨hz, hzBd⟩)
  by_cases hzA : z ∈ G (ends e).1 '' Cp (ends e).1
  · have hzi : z ∈ interior (G (ends e).1 '' Cp (ends e).1) := by
      by_contra hnot
      apply hzBd
      rw [((hCp _).image (hG _)).boundary_eq_frontier]
      exact ⟨subset_closure hzA, hnot⟩
    have hnot : z ∉ connectedComponentIn
        (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a := by
      intro hzcomp
      have hacomp : a ∈ connectedComponentIn
          (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) z := by
        rw [← connectedComponentIn_eq hzcomp]
        exact mem_connectedComponentIn ha
      rw [← hinsideEq z ⟨hzB, hzi⟩] at hacomp
      exact haR (closure_minimal hcc hR hacomp)
    exact hin z ⟨hzB, hzA⟩ hnot (subset_closure (mem_connectedComponentIn ⟨hzB, hzA⟩))
  · have hnot : z ∉ connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b := by
      intro hzcomp
      have hbcomp : b ∈ connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) z := by
        rw [← connectedComponentIn_eq hzcomp]
        exact mem_connectedComponentIn hb
      rw [← houtsideEq z ⟨hzB, hzA⟩] at hbcomp
      exact hbR (hcc hbcomp)
    exact hout z ⟨hzB, hzA⟩ hnot (subset_closure (mem_connectedComponentIn ⟨hzB, hzA⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
