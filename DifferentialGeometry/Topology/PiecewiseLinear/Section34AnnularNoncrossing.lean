import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularSameSideObstruction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedAnnularBands

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


theorem section34_annular_endpoints_mem_interval_iff
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [Preorder ι] {σ : ι → Fin (cnt e)} {i j k l : ι}
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
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ k))
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ l))
    (hinterval : ∀ r, Pg e (σ r) ⊆ F ↔ i ≤ r ∧ r ≤ j) :
    (i ≤ k ∧ k ≤ j) ↔ i ≤ l ∧ l ≤ j := by
  have hends : Pg e (σ k) ∪ Pg e (σ l) ⊆
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hzero, ← hone]
    exact union_subset (image_mono (prod_mono_right (by simp)))
      (image_mono (prod_mono_right (by simp)))
  have hkne : (Pg e (σ k)).Nonempty := by
    rw [← hzero]
    exact ((isConnected_stdSimplexBoundary 0).nonempty.prod (singleton_nonempty 0)).image f
  have hlne : (Pg e (σ l)).Nonempty := by
    rw [← hone]
    exact ((isConnected_stdSimplexBoundary 0).nonempty.prod (singleton_nonempty 1)).image f
  have hprop (hx : (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∩ F).Nonempty) :=
    section34_annular_endpoints_subset_of_same_side hprep hpack e hC hD hfront hfirst
      hf hfB hempty hdis hside (σ k).isLt (σ l).isLt hzero hone hx
  constructor
  · intro hk
    obtain ⟨x, hx⟩ := hkne
    have hall := hprop ⟨x, hends (Or.inl hx), (hinterval k).mpr hk hx⟩
    exact (hinterval l).mp (fun _ hy => hall (Or.inr hy))
  · intro hl
    obtain ⟨x, hx⟩ := hlne
    have hall := hprop ⟨x, hends (Or.inr hx), (hinterval l).mpr hl hx⟩
    exact (hinterval k).mp (fun _ hy => hall (Or.inl hy))

theorem section34_annular_not_interleaved_of_interval_trace
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [Preorder ι] {σ : ι → Fin (cnt e)} {i j k l : ι}
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
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ k))
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ l))
    (hinterval : ∀ r, Pg e (σ r) ⊆ F ↔ i ≤ r ∧ r ≤ j) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  rintro ⟨hik, hkj, hjl⟩
  have hiff := section34_annular_endpoints_mem_interval_iff hprep hpack e hC hD hfront
    hfirst hf hfB hempty hdis hside hzero hone hinterval
  exact hjl.not_ge (hiff.mp ⟨hik.le, hkj.le⟩).2

theorem section34_annular_not_interleaved_of_ordered_caps
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [Preorder ι] {σ : ι → Fin (cnt e)} {i j k l : ι}
    {D₀ D₁ : ι → Set M₂} {C D : Set M₂} (hC : closure (interior C) = C) (hD : IsClosed D)
    (hfront : frontier C = D ∪ (D₁ i ∩ D₀ j))
    (hfirst : G (ends e).1 '' CpBd (ends e).1 ∩ C = D₁ i ∩ D₀ j)
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
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ k))
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ l))
    (hleft : ∀ r s, Pg e (σ r) ⊆ D₀ s ↔ r ≤ s)
    (hright : ∀ r s, Pg e (σ r) ⊆ D₁ s ↔ s ≤ r) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  apply section34_annular_not_interleaved_of_interval_trace hprep hpack e hC hD hfront
    hfirst hf hfB hempty hdis hside hzero hone
  exact fun r => subset_inter_of_ordered_caps_iff hleft hright i j r

end DifferentialGeometry.Topology.PiecewiseLinear
