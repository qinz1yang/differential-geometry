import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingOrderedBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InternalBandTrapping

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

theorem exists_section34_piercing_second_ordered_bands_interior
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hanchors : ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
        (∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
        ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e))
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (σ : Fin (cnt e) ≃ Fin (cnt e)) (D₀ D₁ : Fin (cnt e) → Set M₂),
      (∀ i, IsPLCellOn 2 (D₀ i) (Pg e (σ i).val) ∧
        IsPLCellOn 2 (D₁ i) (Pg e (σ i).val) ∧
        D₀ i ∪ D₁ i = G (ends e).2 '' CpBd (ends e).2 ∧
        D₀ i ∩ D₁ i = Pg e (σ i).val ∧
        G (ends e).2 '' Bb₀ e ⊆ D₀ i ∧ G (ends e).2 '' Bb₁ e ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₁ j ↔ j ≤ i) ∧
      ∀ i j, i < j →
        ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
          (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).2 '' Cp (ends e).2 ∧
        IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ i).val ∧
        (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ j).val ∧
        (∀ k, Pg e (σ k).val ⊆ (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
          i ≤ k ∧ k ≤ j) ∧
        (j.val = i.val + 1 →
          Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
            (G (ends e).1 '' CpBd (ends e).1) ∧
          (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
            G (ends e).2 '' Bb e ∩ interior (Tp e)) := by
  obtain ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright, hbands⟩ :=
    exists_section34_piercing_second_ordered_bands hprep hpack e hess
  have hRdis := section34_second_rims_disjoint_first_boundary hprep hpack e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPg, -⟩ := id hpack
  have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hPgBd (r : Fin (cnt e)) : Pg e (σ r).val ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hx => image_mono hAaBd
      (image_mono sdiff_subset ((hPg e (σ r).val (σ r).isLt).2 hx).1)
  refine ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright, ?_⟩
  intro i j hij
  obtain ⟨P, u, f, hP, hu, huP, hf, hfP, himage, hsub, hzero, hone, hpos, hempty⟩ :=
    hbands i j hij
  refine ⟨P, u, f, hP, hu, huP, hf, hfP, himage, hsub, hzero, hone, hpos, ?_⟩
  intro hadj
  have hmaps : MapsTo f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hfP ⟨x, hx, rfl⟩
  have hcont := hu.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hmaps
  have hinj := hu.injOn.comp hf.bijOn.injOn hmaps
  have hends : (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      (u ∘ f) '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hzero, hone]
    exact union_subset (hPgBd i) (hPgBd j)
  have havoid : Disjoint ((u ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    refine disjoint_left.mpr fun x hx hxrim => ?_
    have hxcap := himage.subset hx
    rcases hxrim with hx₀ | hx₁
    · have hxJ := (hcap i).2.2.2.1.subset ⟨(hcap i).2.2.2.2.1 hx₀, hxcap.1⟩
      exact disjoint_left.mp hRdis (Or.inl hx₀) (hPgBd i hxJ)
    · have hxJ := (hcap j).2.2.2.1.subset ⟨hxcap.2, (hcap j).2.2.2.2.2 hx₁⟩
      exact disjoint_left.mp hRdis (Or.inr hx₁) (hPgBd j hxJ)
  exact ⟨hempty hadj, section34_internal_band_subset_inner_tube_interior hprep hpack e
    hanchors hcont hinj hsub hends (hempty hadj) havoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
