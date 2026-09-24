import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandUniqueness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeRims

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.inter_eq_lateral_band_of_essential_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hL : IsPolyhedralSphere (n := 3) 1 L) (hJA : J ⊆ A) (hLA : L ⊆ A)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A)
    (hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A)
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfA : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    {C : Set M} (hfC : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C)
    (hfront : frontier C ∩ B ⊆ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hCends : Disjoint C (A₀ ∪ A₁)) :
    B ∩ C = f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨P, u, φ, -, hu, hφ, hφP, hφA, hφ₀, hφ₁, hcert⟩ :=
    hS.exists_annular_band_with_filling_trace hA hAB hJ hL hJA hLA hJL hJend hLend
      hJess hLess
  have hmap : MapsTo φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hφP ⟨x, hx, rfl⟩
  have heq := hS.image_lateral_eq_of_same_ends hA hAB hJ hL hJA hLA hJL hJend hLend
    hJess hLess hf hfi (hu.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hmap)
    (fun x hx y hy hxy => hφ.bijOn.injOn hx hy (hu.injOn (hmap hx) (hmap hy) hxy))
    hfA hφA hf₀ hf₁ hφ₀ hφ₁
  rw [← heq] at hcert
  exact hcert C hfC hfront hCends

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

theorem section34_annular_region_second_trace
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    {C F : Set M₂} (hC : IsClosed C) (hCT : C ⊆ Tp e)
    (hfront : frontier C = f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F)
    (hFtrace : F ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ Pg e i ∪ Pg e j) :
    G (ends e).2 '' CpBd (ends e).2 ∩ C =
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, hTube, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := hpack
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hends (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).2
    have hzCp := hBCp ((union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGcp (ends e).2).injOn (hBCp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hsub (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).2 '' Bb e :=
    fun _ hx => image_mono sdiff_subset ((hPg e k hk).2 hx).2
  have hfC : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C :=
    (hfront.symm ▸ subset_union_left).trans hC.frontier_subset
  have hendf : Pg e i ∪ Pg e j ⊆
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hf₀, ← hf₁]
    exact union_subset (image_mono (prod_mono_right (by simp)))
      (image_mono (prod_mono_right (by simp)))
  have hfront' : frontier C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [hfront]
    rintro x ⟨hx | hx, hxB⟩
    · exact hx
    · exact hendf (hFtrace ⟨hx, hxB⟩)
  have hCends : Disjoint C (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    exact (hTube e).2.symm.mono_left hCT
  exact ((hCp (ends e).2).image (hGcp (ends e).2)).inter_eq_lateral_band_of_essential_ends
    hann (image_mono (hBb e).1) (hPg e i hi).1 (hPg e j hj).1 (hsub i hi) (hsub j hj)
    (hdisj e i hi j hj hij) (hends i hi) (hends j hj) hiess hjess hf hfi hfB hf₀ hf₁
    hfC hfront' hCends

theorem section34_annular_region_second_trace_of_empty_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {f g : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    (hg₀ : g '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hg₁ : g '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    (hempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).2 '' CpBd (ends e).2))
    {C : Set M₂} (hC : IsClosed C) (hCT : C ⊆ Tp e)
    (hfront : frontier C = f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) :
    G (ends e).2 '' CpBd (ends e).2 ∩ C =
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  apply section34_annular_region_second_trace hprep hpack e hi hj hij hiess hjess
    hf hfi hfB hf₀ hf₁ hC hCT hfront
  rintro _ ⟨⟨p, hp, rfl⟩, hxB⟩
  by_cases h₀ : p.2 = 0
  · exact Or.inl (hg₀.subset ⟨p, ⟨hp.1, h₀⟩, rfl⟩)
  by_cases h₁ : p.2 = 1
  · exact Or.inr (hg₁.subset ⟨p, ⟨hp.1, h₁⟩, rfl⟩)
  exact (disjoint_left.mp hempty
    ⟨p, ⟨hp.1, lt_of_le_of_ne hp.2.1 (Ne.symm h₀), lt_of_le_of_ne hp.2.2 h₁⟩, rfl⟩
    hxB).elim

end DifferentialGeometry.Topology.PiecewiseLinear
