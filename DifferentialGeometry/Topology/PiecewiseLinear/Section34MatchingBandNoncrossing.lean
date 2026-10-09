import DifferentialGeometry.Topology.PiecewiseLinear.Section34PrescribedAnnularRegion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandSide

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

theorem section34_annular_not_interleaved_of_matching_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [LinearOrder ι] {σ : ι → Fin (cnt e)} (hσ : Function.Injective σ)
    {i j k l : ι}
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e (σ i)) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e (σ j)) ∧ D ⊆ G (ends e).2 '' Bb e)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    {g : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)))
    (hgP : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P)
    (hgT : (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
      G (ends e).2 '' Bb e ∩ interior (Tp e))
    (hg₀ : (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ i))
    (hg₁ : (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ j))
    (hgempty : Disjoint ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    {f : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ k))
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ l))
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    {F : Set M₂} (hF : IsAnnulusOn F (Pg e (σ i)) (Pg e (σ j)))
    (hFA : F ⊆ G (ends e).1 '' Aa e)
    (hinterval : ∀ r, Pg e (σ r) ⊆ F ↔ i ≤ r ∧ r ≤ j)
    (hbands : ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ)) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  rintro ⟨hik, hkj, hjl⟩
  have hij := hik.trans hkj
  obtain ⟨C, hCcompact, hCreg, -, hfront, -, -, -, hfirst, hCside⟩ :=
    exists_section34_annular_region_of_matching_band hprep hpack e (σ i).isLt (σ j).isLt
      (fun h => hij.ne (hσ (Fin.ext h))) hiess hjess hu hg hgP hgT hg₀ hg₁ hgempty hF hFA
  have hgmap : MapsTo g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hgP ⟨x, hx, rfl⟩
  have hgc := hu.continuousOn.comp hg.isPiecewiseAffineOn.continuousOn hgmap
  have hgi := hu.injOn.comp hg.bijOn.injOn hgmap
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, hPgdis, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hPgA (r : ι) : Pg e (σ r) ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hx => image_mono (sdiff_subset.trans ((hAa e).1 ▸ inter_subset_left))
      ((hPg e (σ r) (σ r).isLt).2 hx).1
  have hendsG : (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hg₀, hg₁]
    exact union_subset (hPgA i) (hPgA j)
  have hendsF : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hf₀, hf₁]
    exact union_subset (hPgA k) (hPgA l)
  have hcircles {r s : ι} (hrs : r ≠ s) : Disjoint (Pg e (σ r)) (Pg e (σ s)) :=
    hPgdis e (σ r) (σ r).isLt (σ s) (σ s).isLt (fun h => hrs (hσ (Fin.ext h)))
  have hendsDis : Disjoint ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}))
      (f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ f '' (stdSimplexBoundary 2 ×ˢ {1})) := by
    rw [hg₀, hg₁, hf₀, hf₁, disjoint_union_left, disjoint_union_right,
      disjoint_union_right]
    exact ⟨⟨hcircles hik.ne, hcircles (hij.trans hjl).ne⟩,
      ⟨hcircles hkj.ne', hcircles hjl.ne⟩⟩
  have hdis := hcellB.disjoint_lateral_bands_of_disjoint_ends hgc hgi hf hfi
    ((hgT.trans inter_subset_left).trans (image_mono (hBb e).1))
    (hfB.trans (image_mono (hBb e).1)) hendsG hendsF hgempty hfempty hendsDis
  have hDclosed : IsClosed ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) :=
    (isAnnulusOn_stdSimplex_lateral.isCompact.image_of_continuousOn hgc).isClosed
  have hODC : (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ C := by
    intro x hx
    apply hCcompact.isClosed.frontier_subset
    rw [hfront]
    exact Or.inl (image_mono (prod_mono_right Ioo_subset_Icc_self) hx)
  have hOD := ((isConnected_stdSimplexBoundary 0).nonempty.prod
    (nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))).image (u ∘ g)
  have hFfront : F ⊆ frontier (G (ends e).1 '' Cp (ends e).1) :=
    fun _ hx => hcellA.boundary_eq_frontier ▸ (hfirst.superset hx).1
  have hCside' := hCside.imp id (fun h => h.subset.trans hFfront)
  have hsides := same_side_of_nonempty_subset hCside' hOD hODC hbands
  apply section34_annular_not_interleaved_of_interval_trace hprep hpack e hCreg
    hDclosed hfront hfirst hf hfB hfempty hdis.symm ?_ hf₀ hf₁ hinterval
    ⟨hik, hkj, hjl⟩
  exact hsides.imp id (fun h => ⟨fun x hx => hcellA.boundary_eq_frontier.symm ▸ h.1 hx, h.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
