import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularNoncrossing

open Set Topology

namespace DifferentialGeometry.Topology

theorem same_side_of_nonempty_subset {X : Type*} [TopologicalSpace X] {A C O P : Set X}
    (hCside : C ⊆ A ∨ C ∩ A ⊆ frontier A) (hO : O.Nonempty) (hOC : O ⊆ C)
    (hside : (O ⊆ interior A ∧ P ⊆ interior A) ∨ (O ⊆ Aᶜ ∧ P ⊆ Aᶜ)) :
    (C ⊆ A ∧ P ⊆ interior A) ∨ (C ∩ A ⊆ frontier A ∧ P ⊆ Aᶜ) := by
  obtain ⟨x, hx⟩ := hO
  rcases hside with ⟨hOA, hPA⟩ | ⟨hOA, hPA⟩
  · rcases hCside with hCA | hCA
    · exact Or.inl ⟨hCA, hPA⟩
    · exact False.elim ((hCA ⟨hOC hx, interior_subset (hOA hx)⟩).2 (hOA hx))
  · rcases hCside with hCA | hCA
    · exact False.elim (hOA hx (hCA (hOC hx)))
    · exact Or.inr ⟨hCA, hPA⟩

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


theorem section34_annular_not_interleaved_of_same_band_side
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [Preorder ι] {σ : ι → Fin (cnt e)} {i j k l : ι}
    {D₀ D₁ : ι → Set M₂} {C D : Set M₂} (hC : closure (interior C) = C)
    (hfront : frontier C = D ∪ (D₁ i ∩ D₀ j))
    (hfirst : G (ends e).1 '' CpBd (ends e).1 ∩ C = D₁ i ∩ D₀ j)
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) D)
    {g : (Fin 3 → ℝ) × ℝ → M₂}
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgD : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D)
    (hCside : C ⊆ G (ends e).1 '' Cp (ends e).1 ∨
      C ∩ G (ends e).1 '' Cp (ends e).1 = D₁ i ∩ D₀ j)
    (hbands : (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ))
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ k))
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ l))
    (hleft : ∀ r s, Pg e (σ r) ⊆ D₀ s ↔ r ≤ s)
    (hright : ∀ r s, Pg e (σ r) ⊆ D₁ s ↔ s ≤ r) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  have hD : IsClosed D := hgD ▸
    (isAnnulusOn_stdSimplex_lateral.isCompact.image_of_continuousOn hg).isClosed
  have hCc : IsClosed C := hC ▸ isClosed_closure
  have hODC : g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ C := by
    intro x hx
    apply hCc.frontier_subset
    rw [hfront]
    exact Or.inl (hgD.subset (image_mono (prod_mono_right Ioo_subset_Icc_self) hx))
  have hOD : (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)).Nonempty :=
    ((isConnected_stdSimplexBoundary 0).nonempty.prod
      (nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))).image g
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcell := (hCp (ends e).1).image (hGp (ends e).1)
  have hCside' : C ⊆ G (ends e).1 '' Cp (ends e).1 ∨
      C ∩ G (ends e).1 '' Cp (ends e).1 ⊆
        frontier (G (ends e).1 '' Cp (ends e).1) := by
    rcases hCside with hCA | hCA
    · exact Or.inl hCA
    · refine Or.inr fun x hx => ?_
      have hxF := hCA.subset hx
      exact hcell.boundary_eq_frontier ▸ (hfirst.superset hxF).1
  have hsides := same_side_of_nonempty_subset hCside' hOD hODC hbands
  apply section34_annular_not_interleaved_of_ordered_caps hprep hpack e hC hD hfront
    hfirst hf hfB hempty hdis ?_ hzero hone hleft hright
  rcases hsides with hsides | ⟨hCA, hfA⟩
  · exact Or.inl hsides
  · exact Or.inr ⟨fun x hx => hcell.boundary_eq_frontier.symm ▸ hCA hx, hfA⟩

end PiecewiseLinear

end DifferentialGeometry.Topology
