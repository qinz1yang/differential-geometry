import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandTargetTrace

open Set

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

theorem exists_section34_first_annular_band_of_essential_second_pair
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).1 '' Aa e ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j ∧
      ∀ C : Set M₂, (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C →
        frontier C ∩ G (ends e).1 '' CpBd (ends e).1 ⊆
          (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) →
        Disjoint C (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) →
          G (ends e).1 '' CpBd (ends e).1 ∩ C =
            (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hiA := (section34_piercing_generators_of_essential_second hprep hpack e hi hiess).2.2
  have hjA := (section34_piercing_generators_of_essential_second hprep hpack e hj hjess).2.2
  have hann := (section34_piercing_annuli hprep hpack e).1
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := hpack
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hACp := hAB.trans (hCp (ends e).1).boundary_subset
  have hends (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).1
    have hzCp := hACp ((union_subset (hAa e).2.first_subset (hAa e).2.second_subset) hz)
    have heq := (hGcp (ends e).1).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hsub (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).1 '' Aa e := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := ((hPg e k hk).2 hx).1
    exact ⟨z, hz.1, hzx⟩
  simpa only [image_union] using
    ((hCp (ends e).1).image (hGcp (ends e).1)).exists_annular_band_with_filling_trace
    hann (image_mono hAB) (hPg e i hi).1 (hPg e j hj).1 (hsub i hi) (hsub j hj)
    (hdisj e i hi j hj hij) (hends i hi) (hends j hj) hiA hjA

theorem exists_section34_matching_annular_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D : Set M₂} (hDT : D ⊆ Tp e)
    (htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i ∪ Pg e j) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).1 '' Aa e ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j ∧
      D ∩ (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = Pg e i ∪ Pg e j ∧
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ D ⊆ Tp e ∧
      ∀ C : Set M₂, (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ C →
        frontier C ∩ G (ends e).1 '' CpBd (ends e).1 ⊆
          (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) →
        Disjoint C (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) →
          G (ends e).1 '' CpBd (ends e).1 ∩ C =
            (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨P, u, φ, hP, hu, hφ, hφP, hband, hzero, hone, hcert⟩ :=
    exists_section34_first_annular_band_of_essential_second_pair hprep hpack e
      hi hj hij hiess hjess
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, htube, -⟩ := hpack
  have hAB : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hAT : G (ends e).1 '' Aa e ⊆ Tp e := by
    rw [(htube e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have hends : Pg e i ∪ Pg e j ⊆
      (u ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hzero, ← hone]
    exact union_subset
      (image_mono (prod_mono_right (by simp)))
      (image_mono (prod_mono_right (by simp)))
  refine ⟨P, u, φ, hP, hu, hφ, hφP, hband, hzero, hone, ?_,
    union_subset (hband.trans hAT) hDT, hcert⟩
  apply Subset.antisymm
  · exact fun x hx => htrace.subset ⟨hx.1, hAB (hband hx.2)⟩
  · exact fun x hx => ⟨(htrace.superset hx).1, hends hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
