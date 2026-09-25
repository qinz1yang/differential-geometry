import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

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


theorem exists_section34_distinguished_interior_anchors
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ a ∈ G (ends e).2 '' Bb e ∩ interior (G (ends e).1 '' Cp (ends e).1),
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      (∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a) ∧
      ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b := by
  have hlocal := section34_inside_local_sides hprep hpack e
  have hBclosed := (section34_second_annulus_isCompact hprep hpack e).isClosed
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -, -, -, hin, hout, -⟩ := hpack
  obtain ⟨a, ha, hside⟩ := hin e
  obtain ⟨b, hb, hbside⟩ := hout e
  obtain ⟨V, -, -, hconn, hacl⟩ := hlocal a ha
  have hclsub : closure (G (ends e).2 '' Bb e ∩
      interior (G (ends e).1 '' Cp (ends e).1) ∩ V) ⊆
      G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1 :=
    closure_minimal (fun z hz => ⟨hz.1.1, interior_subset hz.1.2⟩)
      (hBclosed.inter ((hCp _).image (hG _)).isCompact.isClosed)
  have hcc := hconn.closure.subset_connectedComponentIn hacl hclsub
  obtain ⟨z, hz⟩ := closure_nonempty_iff.mp ⟨a, hacl⟩
  have hza := hcc (subset_closure hz)
  refine ⟨z, hz.1, b, hb, ?_, hbside⟩
  intro w hw hwT
  rw [← connectedComponentIn_eq hza]
  exact hside w hw hwT

theorem section34_trace_free_component_trapped_of_anchor_avoidance
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {a b y : M₂}
    (ha : a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1)
    (hb : b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1)
    (hinside : ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a)
    (houtside : ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b)
    (hy : y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1)
    (havoidA : a ∉ closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y))
    (havoidB : b ∉ closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y)) :
    closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) y) ⊆ Tp e := by
  have hclosed := (section34_inner_tube_isCompact hprep hpack e).isClosed
  apply closure_minimal ?_ hclosed
  intro z hz
  by_contra hzT
  have hzB := (connectedComponentIn_subset _ _ hz).1
  rcases section34_trace_free_component_side hprep hpack e y with hin | hout
  · have hyi := hin (mem_connectedComponentIn hy)
    have hzclosed := hinside z ⟨hzB, interior_subset (hin hz)⟩ hzT
    have heq := section34_inside_component_closure_eq hprep hpack e y ⟨hy.1, hyi⟩
    have hzcomp := heq ▸ subset_closure hz
    have hacomp : a ∈ connectedComponentIn
        (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y := by
      rw [connectedComponentIn_eq hzcomp, ← connectedComponentIn_eq hzclosed]
      exact mem_connectedComponentIn ha
    exact havoidA (heq.symm ▸ hacomp)
  · have hyo := hout (mem_connectedComponentIn hy)
    have hzclosed := houtside z ⟨hzB, hout hz⟩ hzT
    have heq := section34_trace_free_component_eq_outside hprep hpack e y ⟨hy.1, hyo⟩
    have hzcomp := heq ▸ hz
    have hbcomp : b ∈ connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y := by
      rw [connectedComponentIn_eq hzcomp, ← connectedComponentIn_eq hzclosed]
      exact mem_connectedComponentIn hb
    exact havoidB (subset_closure (heq.symm ▸ hbcomp))


theorem section34_region_subset_inner_tube_of_anchor_avoidance
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {a b : M₂} {R : Set M₂}
    (ha : a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1)
    (hb : b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1)
    (hinside : ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a)
    (houtside : ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b)
    (hR : IsClosed R) (hconn : IsPreconnected R)
    (hRB : R ⊆ G (ends e).2 '' CpBd (ends e).2)
    (hmeet : (R ∩ G (ends e).2 '' Bb e).Nonempty)
    (hcomponent : ∀ z ∈ R \ G (ends e).1 '' CpBd (ends e).1,
      connectedComponentIn
        (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R)
    (haR : a ∉ R) (hbR : b ∉ R) : R ⊆ G (ends e).2 '' Bb e ∩ Tp e := by
  have hinsideEq := section34_inside_component_closure_eq hprep hpack e
  have houtsideEq := section34_trace_free_component_eq_outside hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, htrace, -, hends, -, hG, -⟩ := hpack
  have hBbB : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  have hRT : R ∩ G (ends e).2 '' Bb e ⊆ Tp e := by
    intro z hz
    by_contra hzT
    have hzBd : z ∉ G (ends e).1 '' CpBd (ends e).1 :=
      fun hzBd => hzT (interior_subset (htrace e ⟨hzBd, hRB hz.1⟩).2)
    have hcc : connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) z ⊆ R :=
      (connectedComponentIn_mono z (sdiff_subset_sdiff_left hBbB)).trans
        (hcomponent z ⟨hz.1, hzBd⟩)
    by_cases hzA : z ∈ G (ends e).1 '' Cp (ends e).1
    · have hzi : z ∈ interior (G (ends e).1 '' Cp (ends e).1) := by
        by_contra hnot
        apply hzBd
        rw [((hCp _).image (hG _)).boundary_eq_frontier]
        exact ⟨subset_closure hzA, hnot⟩
      have hzcomp := hinside z ⟨hz.2, hzA⟩ hzT
      have hacomp : a ∈ connectedComponentIn
          (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) z := by
        rw [← connectedComponentIn_eq hzcomp]
        exact mem_connectedComponentIn ha
      rw [← hinsideEq z ⟨hz.2, hzi⟩] at hacomp
      exact haR (closure_minimal hcc hR hacomp)
    · have hzcomp := houtside z ⟨hz.2, hzA⟩ hzT
      have hbcomp : b ∈ connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) z := by
        rw [← connectedComponentIn_eq hzcomp]
        exact mem_connectedComponentIn hb
      rw [← houtsideEq z ⟨hz.2, hzA⟩] at hbcomp
      exact hbR (hcc hbcomp)
  have hRends : Disjoint R (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    refine disjoint_left.mpr fun z hzR hzends => ?_
    have hzBb := union_subset hann.first_subset hann.second_subset hzends
    rw [← image_union] at hzends
    exact disjoint_left.mp (hends e).2 hzends (hRT ⟨hzR, hzBb⟩)
  have hRBb := ((hCp _).image (hG _)).subset_annulus_of_isPreconnected_of_disjoint_boundary
    hann hBbB hRB hconn hmeet hRends
  exact fun z hz => ⟨hRBb hz, hRT ⟨hz, hRBb hz⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
