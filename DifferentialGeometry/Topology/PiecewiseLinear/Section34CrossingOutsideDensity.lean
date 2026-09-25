import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_connected_outside_slice_of_chart_crossing {M : Type*} [TopologicalSpace M]
    {A X : Set M} {x : M} (hXc : IsClosed X) (hreg : closure (interior X) = X)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hx : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x)) (hxF : x ∈ frontier X)
    (hA : ∀ N ∈ 𝓝 x, ∃ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → M), 0 < r ∧ ContinuousOn g (Metric.ball a r) ∧
        InjOn g (Metric.ball a r) ∧ MapsTo g (Metric.ball a r) (A ∩ N) ∧ g a = x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ IsPreconnected ((A \ X) ∩ U) ∧
      x ∈ closure ((A \ X) ∩ U) := by
  let Y := (interior X)ᶜ
  have hY : IsClosed Y := isOpen_interior.isClosed_compl
  have hYi : interior Y = Xᶜ := by
    change interior (interior X)ᶜ = Xᶜ
    rw [interior_compl, hreg]
  have hYf : frontier Y = frontier X := by
    change frontier (interior X)ᶜ = frontier X
    rw [frontier_compl, frontier, hreg, interior_interior, frontier, hXc.closure_eq]
  have hxY : x ∈ closure (interior Y) := by
    rw [hYi, closure_compl]
    exact hxF.2
  obtain ⟨U, hU, hxU, hconn, hdense⟩ := exists_connected_inside_slice_of_chart_crossing
    hY hxY c hx (hYf.symm ▸ hcross) hA
  rw [hYi, ← Set.sdiff_eq] at hconn hdense
  exact ⟨U, hU, hxU, hconn, hdense⟩

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


theorem section34_crossing_outside_slice
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e) :
    ∃ V : Set M₂, IsOpen V ∧ x ∈ V ∧
      IsPreconnected ((G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) ∩ V) ∧
      x ∈ closure ((G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) ∩ V) := by
  have hAeq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨hG, -, -, -, -, -, hmeet, -, hBdis, -, hGp, -, -, -, -, -, -, -, -, hcross, -⟩ :=
    id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hxmeet := hmeet e ⟨hx.1, image_mono (hBb e).1 hx.2⟩
  have hxtrace : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
    ⟨image_mono sdiff_subset hxmeet.1.1, hx.2⟩
  obtain ⟨c, -, hxc, hcross⟩ := hcross e x hxtrace
  have hcongr : ∀ᶠ z in 𝓝 (c x),
      z ∈ c '' (G (ends e).1 '' Aa e ∩ c.source) ↔
        z ∈ c '' (frontier (G (ends e).1 '' Cp (ends e).1) ∩ c.source) := by
    filter_upwards [(c.isOpen_image_source_inter isOpen_interior).mem_nhds
      ⟨x, ⟨hxc, hxmeet.2⟩, rfl⟩] with z hz
    obtain ⟨y, ⟨hys, hyT⟩, rfl⟩ := hz
    have hmem (S : Set M₂) : c y ∈ c '' (S ∩ c.source) ↔ y ∈ S := by
      constructor
      · rintro ⟨w, ⟨hw, hws⟩, hwy⟩
        exact c.injOn hws hys hwy ▸ hw
      · exact fun hy => ⟨y, ⟨hy, hys⟩, rfl⟩
    rw [hmem, hmem, hAeq, ← hcellA.boundary_eq_frontier]
    exact and_iff_left (interior_subset hyT)
  have hcross' := hcross.symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hcongr
  refine exists_connected_outside_slice_of_chart_crossing hcellA.isCompact.isClosed
    (X := G (ends e).1 '' Cp (ends e).1) ?_ c hxc hcross' ?_ ?_
  · have hcl : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
        G (ends e).1 '' Cp (ends e).1 := by
      rw [← hcellA.sdiff_boundary_eq_interior]
      exact hcellA.closure_sdiff_boundary
    exact hcl
  · exact hcellA.boundary_eq_frontier ▸ hx.1
  · intro N hN
    apply hcellB.exists_ball_chart_in_annulus hann (image_mono (hBb e).1) hx.2 ?_ hN
    intro hxends
    rw [← image_union] at hxends
    exact disjoint_left.mp (hBdis e).2 hxends (interior_subset hxmeet.2)

end DifferentialGeometry.Topology.PiecewiseLinear
