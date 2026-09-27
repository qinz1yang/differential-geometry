import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingOutsideDensity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology

theorem opposite_sides_of_local_two_set_cover
    {X : Type*} [TopologicalSpace X] {A B O₀ O₁ V : Set X} {x : X}
    (hA : IsClosed A) (h₀ : IsPreconnected O₀) (h₁ : IsPreconnected O₁)
    (hd₀ : Disjoint O₀ (frontier A)) (hd₁ : Disjoint O₁ (frontier A))
    (hin : x ∈ closure (B ∩ interior A)) (hout : x ∈ closure (B \ A))
    (hV : V ∈ 𝓝 x) (hcover : V ∩ B ⊆ O₀ ∪ O₁ ∪ frontier A) :
    (O₀ ⊆ interior A ∧ O₁ ⊆ Aᶜ) ∨ (O₀ ⊆ Aᶜ ∧ O₁ ⊆ interior A) := by
  obtain ⟨y, hyV, hyB, hyA⟩ := mem_closure_iff_nhds.mp hin V hV
  obtain ⟨z, hzV, hzB, hzA⟩ := mem_closure_iff_nhds.mp hout V hV
  have hy : y ∈ O₀ ∪ O₁ := (hcover ⟨hyV, hyB⟩).resolve_right
    (fun hf => disjoint_left.mp disjoint_interior_frontier hyA hf)
  have hz : z ∈ O₀ ∪ O₁ := (hcover ⟨hzV, hzB⟩).resolve_right
    (fun hf => hzA (hA.frontier_subset hf))
  have hext {O : Set X} (hc : IsPreconnected O) (hd : Disjoint O (frontier A))
      (hzO : z ∈ O) : O ⊆ Aᶜ := by
    have h := subset_interior_of_isPreconnected_of_disjoint_frontier hc
      (frontier_compl A ▸ hd) (B := Aᶜ)
    rw [hA.isOpen_compl.interior_eq] at h
    exact h ⟨z, hzO, hzA⟩
  rcases hy with hy | hy
  · have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier h₀ hd₀ ⟨y, hy, hyA⟩
    have hz₁ := hz.resolve_left (fun hz₀ => hzA (interior_subset (hsub hz₀)))
    exact Or.inl ⟨hsub, hext h₁ hd₁ hz₁⟩
  · have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier h₁ hd₁ ⟨y, hy, hyA⟩
    have hz₀ := hz.resolve_right (fun hz₁ => hzA (interior_subset (hsub hz₁)))
    exact Or.inr ⟨hext h₀ hd₀ hz₀, hsub⟩

namespace PiecewiseLinear

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

theorem section34_opposite_band_sides_of_local_cover
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e)
    {O₀ O₁ V : Set M₂} (h₀ : IsPreconnected O₀) (h₁ : IsPreconnected O₁)
    (hd₀ : Disjoint O₀ (G (ends e).1 '' CpBd (ends e).1))
    (hd₁ : Disjoint O₁ (G (ends e).1 '' CpBd (ends e).1))
    (hV : V ∈ 𝓝 x)
    (hcover : V ∩ G (ends e).2 '' Bb e ⊆ O₀ ∪ O₁ ∪ G (ends e).1 '' CpBd (ends e).1) :
    (O₀ ⊆ interior (G (ends e).1 '' Cp (ends e).1) ∧
        O₁ ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ) ∨
      (O₀ ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
        O₁ ⊆ interior (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcell := (hCp (ends e).1).image (hGp (ends e).1)
  obtain ⟨V₀, -, -, -, hin⟩ := section34_crossing_inside_slice hprep hpack e hx
  obtain ⟨V₁, -, -, -, hout⟩ := section34_crossing_outside_slice hprep hpack e hx
  rw [hcell.boundary_eq_frontier] at hd₀ hd₁ hcover
  exact opposite_sides_of_local_two_set_cover hcell.isCompact.isClosed h₀ h₁ hd₀ hd₁
    (closure_mono inter_subset_left hin) (closure_mono inter_subset_left hout) hV hcover

theorem section34_opposite_lateral_band_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {f g : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    {J L : Set M₂}
    (hann : IsAnnulusOn (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) J L)
    (hB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hfends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1)
    (hgends : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    {x : M₂} (hxcross : x ∈ G (ends e).1 '' CpBd (ends e).1)
    (hx : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) (hxend : x ∉ J ∪ L) :
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1) ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ) ∨
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  obtain ⟨hc⟩ := ((hCp (ends e).2).image (hGp (ends e).2)).nonempty_chartedSpace_boundary
  let _ := hc
  obtain ⟨V, hV, hcover⟩ := exists_neighborhood_lateral_pair_cover hfi hgi hann
    (hB.trans (image_mono (hBb e).1)) hfends hgends hx hxend
  have hconn := (isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))
  exact section34_opposite_band_sides_of_local_cover hprep hpack e ⟨hxcross, hB hx⟩
    (hconn.image f (hf.mono (prod_mono_right Ioo_subset_Icc_self))).isPreconnected
    (hconn.image g (hg.mono (prod_mono_right Ioo_subset_Icc_self))).isPreconnected
    hfempty hgempty hV
    ((inter_subset_inter_right V (image_mono (hBb e).1)).trans hcover)

end PiecewiseLinear

end DifferentialGeometry.Topology
