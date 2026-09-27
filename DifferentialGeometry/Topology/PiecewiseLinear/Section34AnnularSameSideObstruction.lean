import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCrossingGerms
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandSeparation

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


theorem section34_annular_band_subset_of_same_side
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {C D F : Set M₂} (hC : closure (interior C) = C) (hD : IsClosed D)
    (hfront : frontier C = D ∪ F)
    (hfirst : G (ends e).1 '' CpBd (ends e).1 ∩ C = F)
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) D)
    (hside : (C ⊆ G (ends e).1 '' Cp (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      (C ∩ G (ends e).1 '' Cp (ends e).1 ⊆ G (ends e).1 '' CpBd (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ))
    (hmeet : (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∩ F).Nonempty) :
    f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C ∧
      G (ends e).1 '' CpBd (ends e).1 ∩
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ F := by
  obtain ⟨x, hxf, hxF⟩ := hmeet
  have hxfirst : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ C := hfirst.symm ▸ hxF
  have hxD : x ∉ D := fun hxD => disjoint_left.mp hdis hxf hxD
  obtain ⟨V, hV, hxV, hVD, hin, hout⟩ := section34_crossing_connected_ambient_sides
    hprep hpack e ⟨hxfirst.1, hfB hxf⟩ (hD.isOpen_compl.mem_nhds hxD)
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := hpack
  have hcell := (hCp (ends e).1).image (hGp (ends e).1)
  have hreg : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
      G (ends e).1 '' Cp (ends e).1 := by
    rw [← hcell.sdiff_boundary_eq_interior]
    exact hcell.closure_sdiff_boundary
  have hFsub : F ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hy => (hfirst.symm ▸ hy).1
  have hlocal : V ∩ frontier C ⊆ frontier (G (ends e).1 '' Cp (ends e).1) := by
    rintro y ⟨hyV, hyC⟩
    rw [hfront] at hyC
    rcases hyC with hyD | hyF
    · exact False.elim (hVD hyV hyD)
    · exact hcell.boundary_eq_frontier ▸ hFsub hyF
  have havoid : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (frontier C) := by
    rw [hfront]
    apply disjoint_union_right.mpr
    exact ⟨hdis.mono_left (image_mono (prod_mono_right Ioo_subset_Icc_self)),
      hempty.mono_right hFsub⟩
  have hsub : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C := by
    apply image_lateral_subset_of_same_side hf (hC ▸ isClosed_closure) hreg
      (hC.symm ▸ hxfirst.2) hxf (hV.mem_nhds hxV) hin hout hlocal havoid
    rcases hside with hside | ⟨hCA, hfA⟩
    · exact Or.inl hside
    · exact Or.inr ⟨fun y hy => hcell.boundary_eq_frontier ▸ hCA hy, hfA⟩
  exact ⟨hsub, fun _ hy => hfirst ▸ ⟨hy.1, hsub hy.2⟩⟩

theorem section34_annular_endpoints_subset_of_same_side
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {C D F : Set M₂} (hC : closure (interior C) = C) (hD : IsClosed D)
    (hfront : frontier C = D ∪ F)
    (hfirst : G (ends e).1 '' CpBd (ends e).1 ∩ C = F)
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) D)
    (hside : (C ⊆ G (ends e).1 '' Cp (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      (C ∩ G (ends e).1 '' Cp (ends e).1 ⊆ G (ends e).1 '' CpBd (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ))
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e)
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    (hmeet : (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∩ F).Nonempty) :
    Pg e i ∪ Pg e j ⊆ F := by
  have hsub := (section34_annular_band_subset_of_same_side hprep hpack e hC hD hfront hfirst
    hf hfB hempty hdis hside hmeet).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hAaCp : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hPgCp (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hy => image_mono hAaCp (image_mono sdiff_subset ((hPg e k hk).2 hy).1)
  have hends : Pg e i ∪ Pg e j ⊆ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hzero, ← hone]
    exact union_subset (image_mono (prod_mono_right (by simp)))
      (image_mono (prod_mono_right (by simp)))
  exact fun _ hy => hsub ⟨(union_subset (hPgCp i hi) (hPgCp j hj)) hy, hends hy⟩

theorem section34_annular_band_disjoint_of_endpoint_outside
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {C D F : Set M₂} (hC : closure (interior C) = C) (hD : IsClosed D)
    (hfront : frontier C = D ∪ F)
    (hfirst : G (ends e).1 '' CpBd (ends e).1 ∩ C = F)
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) D)
    (hside : (C ⊆ G (ends e).1 '' Cp (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      (C ∩ G (ends e).1 '' Cp (ends e).1 ⊆ G (ends e).1 '' CpBd (ends e).1 ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ))
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e)
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    (houtside : ¬ Pg e i ∪ Pg e j ⊆ F) :
    Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) F := by
  refine disjoint_left.mpr fun x hxf hxF => houtside ?_
  exact section34_annular_endpoints_subset_of_same_side hprep hpack e hC hD hfront hfirst
    hf hfB hempty hdis hside hi hj hzero hone ⟨x, hxf, hxF⟩

end DifferentialGeometry.Topology.PiecewiseLinear
