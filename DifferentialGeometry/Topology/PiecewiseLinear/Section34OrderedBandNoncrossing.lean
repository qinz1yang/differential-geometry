import DifferentialGeometry.Topology.PiecewiseLinear.Section34MatchingBandNoncrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandAlternation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralBandReversal

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

theorem section34_ordered_matching_band_not_interleaved
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
    {D₀ D₁ : ι → Set M₂}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (Pg e (σ r)) ∧
      IsPLCellOn 2 (D₁ r) (Pg e (σ r)) ∧
      D₀ r ∪ D₁ r = G (ends e).1 '' CpBd (ends e).1 ∧
      D₀ r ∩ D₁ r = Pg e (σ r))
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    (hleft : ∀ r s, Pg e (σ r) ⊆ D₀ s ↔ r ≤ s)
    (hright : ∀ r s, Pg e (σ r) ⊆ D₁ s ↔ s ≤ r)
    (hbandA : ∀ r s, r < s → D₁ r ∩ D₀ s ⊆ G (ends e).1 '' Aa e)
    (hbands : ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ)) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  intro hcross
  have hij := hcross.1.trans hcross.2.1
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcell := (hCp (ends e).1).image (hGp (ends e).1)
  have hF := hcell.isAnnulusOn_inter_of_disk_caps (hcap i).1 (hcap j).2.1
    (hcap i).2.2.1 (hcap i).2.2.2 (hcap j).2.2.1 (hcap j).2.2.2 (hdis i j hij)
  exact section34_annular_not_interleaved_of_matching_bands hprep hpack e hσ hiess hjess
    hu hg hgP hgT hg₀ hg₁ hgempty hf hfi hfB hf₀ hf₁ hfempty hF (hbandA i j hij)
    (fun r => subset_inter_of_ordered_caps_iff hleft hright i j r) hbands hcross

theorem section34_sorted_matching_bands_not_interleaved
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [LinearOrder ι] {σ : ι → Fin (cnt e)} (hσ : Function.Injective σ)
    {i j k l : ι}
    (hess : ∀ r, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e (σ r)) ∧ D ⊆ G (ends e).2 '' Bb e)
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
    {D₀ D₁ : ι → Set M₂}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (Pg e (σ r)) ∧
      IsPLCellOn 2 (D₁ r) (Pg e (σ r)) ∧
      D₀ r ∪ D₁ r = G (ends e).1 '' CpBd (ends e).1 ∧
      D₀ r ∩ D₁ r = Pg e (σ r))
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    (hleft : ∀ r s, Pg e (σ r) ⊆ D₀ s ↔ r ≤ s)
    (hright : ∀ r s, Pg e (σ r) ⊆ D₁ s ↔ s ≤ r)
    (hbandA : ∀ r s, r < s → D₁ r ∩ D₀ s ⊆ G (ends e).1 '' Aa e)
    (hbands : ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1) ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          interior (G (ends e).1 '' Cp (ends e).1)) ∨
      ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
          (G (ends e).1 '' Cp (ends e).1)ᶜ)) :
    ¬ (min i j < min k l ∧ min k l < max i j ∧ max i j < max k l) := by
  obtain ⟨g', hg', hgP', hgclosed, hgopen, hgzero, hgone⟩ :
      ∃ g' : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn g' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (g' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        g' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
          (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
        (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
          (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
        (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ (min i j)) ∧
        (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ (max i j)) := by
    rcases le_total i j with hij | hji
    · exact ⟨g, hg, hgP, rfl, rfl, by simpa only [min_eq_left hij] using hg₀,
        by simpa only [max_eq_right hij] using hg₁⟩
    · obtain ⟨g', hg', hgP', hgc, hgo, hgz, hgon⟩ := exists_lateral_PL_band_reversal u hg hgP
      exact ⟨g', hg', hgP', hgc, hgo,
        by simpa only [min_eq_right hji] using hgz.trans hg₁,
        by simpa only [max_eq_left hji] using hgon.trans hg₀⟩
  obtain ⟨f', hf', hfi', hfclosed, hfopen, hfzero, hfone⟩ :
      ∃ f' : (Fin 3 → ℝ) × ℝ → M₂,
        ContinuousOn f' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
        InjOn f' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
        f' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
          f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
        f' '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
          f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
        f' '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ (min k l)) ∧
        f' '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ (max k l)) := by
    rcases le_total k l with hkl | hlk
    · exact ⟨f, hf, hfi, rfl, rfl, by simpa only [min_eq_left hkl] using hf₀,
        by simpa only [max_eq_right hkl] using hf₁⟩
    · obtain ⟨f', hf', hfi', hfc, hfo, hfz, hfon⟩ := exists_lateral_band_reversal hf hfi
      exact ⟨f', hf', hfi', hfc, hfo,
        by simpa only [min_eq_right hlk] using hfz.trans hf₁,
        by simpa only [max_eq_left hlk] using hfon.trans hf₀⟩
  exact section34_ordered_matching_band_not_interleaved hprep hpack e hσ
    (hess (min i j)) (hess (max i j)) hu hg' hgP' (hgclosed ▸ hgT) hgzero hgone
    (hgopen ▸ hgempty) hf' hfi' (hfclosed ▸ hfB) hfzero hfone (hfopen ▸ hfempty)
    hcap hdis hleft hright hbandA (by rwa [hgopen, hfopen])

end DifferentialGeometry.Topology.PiecewiseLinear
