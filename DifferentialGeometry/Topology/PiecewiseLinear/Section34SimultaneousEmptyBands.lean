import DifferentialGeometry.Topology.PiecewiseLinear.Section34AdjacentBandFamily
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleOrderAdjacency
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandNoncrossing

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

theorem exists_section34_simultaneous_empty_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (hlt : 1 < cnt e)
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
    ∃ i < cnt e, ∃ j < cnt e, i ≠ j ∧
      (¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) ∧
      (¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e) ∧
      ∃ (F : Set M₂) (P : Set (EuclideanSpace ℝ (Fin 3)))
        (u : EuclideanSpace ℝ (Fin 3) → M₂)
        (g : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsAnnulusOn F (Pg e i) (Pg e j) ∧ F ⊆ G (ends e).1 '' Aa e ∧
        Disjoint (F \ (Pg e i ∪ Pg e j)) (G (ends e).2 '' CpBd (ends e).2) ∧
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).2 '' Cp (ends e).2 ∧
        IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
          G (ends e).2 '' Bb e ∩ interior (Tp e) ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j ∧
        Disjoint ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
          (G (ends e).1 '' CpBd (ends e).1) := by
  obtain ⟨σA, A₀, A₁, hcapA, -, -, hdisA, hleftA, hrightA, hbandsA⟩ :=
    exists_section34_piercing_first_ordered_bands hprep hpack e hess
  obtain ⟨σB, B₀, B₁, -, -, -, -, -, -, P, u, g, hchosen, hside⟩ :=
    exists_section34_adjacent_band_family_interior hprep hpack e hlt hanchors hess
  have hbandA (i j : Fin (cnt e)) (hij : i < j) :
      A₁ i ∩ A₀ j ⊆ G (ends e).1 '' Aa e := by
    obtain ⟨P', u', f', -, -, -, -, -, himage, hsub, -⟩ := hbandsA i j hij
    exact himage ▸ hsub
  have hnc (i j k l : Fin (cnt e)) (hij : i.val + 1 = j.val)
      (hkl : k.val + 1 = l.val) (hpar : i.val % 2 = k.val % 2) :
      ¬ (min (σA.symm (σB i)) (σA.symm (σB j)) <
          min (σA.symm (σB k)) (σA.symm (σB l)) ∧
        min (σA.symm (σB k)) (σA.symm (σB l)) <
          max (σA.symm (σB i)) (σA.symm (σB j)) ∧
        max (σA.symm (σB i)) (σA.symm (σB j)) <
          max (σA.symm (σB k)) (σA.symm (σB l))) := by
    have hi : i.val + 1 < cnt e := hij ▸ j.isLt
    have hk : k.val + 1 < cnt e := hkl ▸ l.isLt
    obtain ⟨-, hui, -, hgi, hgiP, -, -, hgi₀, hgi₁, -, hemptyi, hTi⟩ := hchosen i.val hi
    obtain ⟨-, huk, -, hgk, hgkP, -, hBk, hgk₀, hgk₁, -, hemptyk, -⟩ := hchosen k.val hk
    have hmaps : MapsTo (g k.val) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (P k.val) :=
      fun x hx => hgkP ⟨x, hx, rfl⟩
    apply section34_sorted_matching_bands_not_interleaved hprep hpack e σA.injective
      (i := σA.symm (σB i)) (j := σA.symm (σB j))
      (k := σA.symm (σB k)) (l := σA.symm (σB l))
      (fun r => hess (σA r).val (σA r).isLt) hui hgi hgiP hTi ?_ ?_ hemptyi
      (huk.continuousOn.comp hgk.isPiecewiseAffineOn.continuousOn hmaps)
      (huk.injOn.comp hgk.bijOn.injOn hmaps) hBk ?_ ?_ hemptyk
      (fun r => ⟨(hcapA r).1, (hcapA r).2.1, (hcapA r).2.2.1, (hcapA r).2.2.2.1⟩)
      hdisA hleftA hrightA hbandA (hside i.val k.val hi hk hpar)
    · simpa only [σA.apply_symm_apply] using hgi₀
    · simpa only [σA.apply_symm_apply, hij] using hgi₁
    · simpa only [σA.apply_symm_apply] using hgk₀
    · simpa only [σA.apply_symm_apply, hkl] using hgk₁
  obtain ⟨a₀, a₁, b₀, b₁, ha, hb, hlabels⟩ :=
    Equiv.exists_common_adjacent_labels_of_same_parity_noninterleaving hlt σA σB hnc
  have hAlt : a₀ < a₁ := by change a₀.val < a₁.val; omega
  obtain ⟨Q, v, f, -, hv, -, hf, hfQ, -, hfA, hf₀, hf₁, -, hfempty⟩ :=
    hbandsA a₀ a₁ hAlt
  have hfmaps : MapsTo f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) Q :=
    fun x hx => hfQ ⟨x, hx, rfl⟩
  have hfc := hv.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hfmaps
  have hfi := hv.injOn.comp hf.bijOn.injOn hfmaps
  have hF := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hfc hfi
  rw [hf₀, hf₁] at hF
  have hFempty := hfempty ha.symm
  rw [image_lateral_open_eq_sdiff_ends hfi, hf₀, hf₁] at hFempty
  have hmatch :
      IsAnnulusOn ((v ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
        (Pg e (σB b₀).val) (Pg e (σB b₁).val) ∧
      Disjoint (((v ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) \
        (Pg e (σB b₀).val ∪ Pg e (σB b₁).val)) (G (ends e).2 '' CpBd (ends e).2) := by
    rcases hlabels with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · simpa only [h₀, h₁] using And.intro hF hFempty
    · constructor
      · simpa only [h₀, h₁] using hF.symm
      · simpa only [h₀, h₁, union_comm] using hFempty
  have hbvalid : b₀.val + 1 < cnt e := hb ▸ b₁.isLt
  obtain ⟨hP, hu, huP, hg, hgP, -, -, hg₀, hg₁, -, hempty, hT⟩ := hchosen b₀.val hbvalid
  have hne : (σB b₀).val ≠ (σB b₁).val := by
    intro h
    have heq := congrArg Fin.val (σB.injective (Fin.ext h))
    omega
  refine ⟨(σB b₀).val, (σB b₀).isLt, (σB b₁).val, (σB b₁).isLt, hne,
    hess _ (σB b₀).isLt, hess _ (σB b₁).isLt,
    (v ∘ f) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1), P b₀.val, u b₀.val, g b₀.val,
    hmatch.1, hfA, hmatch.2, hP, hu, huP, hg, hgP, hT, hg₀, ?_, hempty⟩
  simpa only [hb] using hg₁

end DifferentialGeometry.Topology.PiecewiseLinear
