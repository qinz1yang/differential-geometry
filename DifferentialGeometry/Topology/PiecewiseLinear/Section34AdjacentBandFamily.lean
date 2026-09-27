import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedOrderedBands
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandSideParity

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

theorem exists_section34_adjacent_band_family_interior
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
      ∃ (P : ℕ → Set (EuclideanSpace ℝ (Fin 3)))
        (u : ℕ → EuclideanSpace ℝ (Fin 3) → M₂)
        (g : ℕ → (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        (∀ r (hr : r + 1 < cnt e),
          IsPLBall 3 (P r) ∧ IsPLHomeomorphInto 3 (u r) (P r) ∧
          u r '' P r = G (ends e).2 '' Cp (ends e).2 ∧
          IsPLHomeomorphOn (g r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
            (g r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
          g r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P r ∧
          (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
            D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
          (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
            G (ends e).2 '' Bb e ∧
          (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ ⟨r, by omega⟩).val ∧
          (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ ⟨r + 1, hr⟩).val ∧
          (∀ k, Pg e (σ k).val ⊆
              (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
            r ≤ k.val ∧ k.val ≤ r + 1) ∧
          Disjoint ((u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
            (G (ends e).1 '' CpBd (ends e).1) ∧
          (u r ∘ g r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
            G (ends e).2 '' Bb e ∩ interior (Tp e)) ∧
        ∀ i j, i + 1 < cnt e → j + 1 < cnt e → i % 2 = j % 2 →
          (((u i ∘ g i) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
              interior (G (ends e).1 '' Cp (ends e).1) ∧
            (u j ∘ g j) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
              interior (G (ends e).1 '' Cp (ends e).1)) ∨
          ((u i ∘ g i) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
              (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
            (u j ∘ g j) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
              (G (ends e).1 '' Cp (ends e).1)ᶜ)) := by
  classical
  obtain ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright, hbands⟩ :=
    exists_section34_piercing_second_ordered_bands_interior hprep hpack e hanchors hess
  have hex (r : Fin (cnt e - 1)) :=
    hbands ⟨r.val, by omega⟩ ⟨r.val + 1, by omega⟩ (by exact_mod_cast Nat.lt_succ_self r.val)
  choose P u g hcert using hex
  let q (r : ℕ) : Fin (cnt e - 1) :=
    if hr : r < cnt e - 1 then ⟨r, hr⟩ else ⟨0, by omega⟩
  have hq (r : ℕ) (hr : r + 1 < cnt e) : (q r).val = r := by
    simp only [q, dif_pos (show r < cnt e - 1 by omega)]
  let P' := fun r => P (q r)
  let u' := fun r => u (q r)
  let g' := fun r => g (q r)
  have hchosen (r : ℕ) (hr : r + 1 < cnt e) :
      IsPLBall 3 (P' r) ∧ IsPLHomeomorphInto 3 (u' r) (P' r) ∧
      u' r '' P' r = G (ends e).2 '' Cp (ends e).2 ∧
      IsPLHomeomorphOn (g' r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (g' r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      g' r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P' r ∧
      (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
      (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e ∧
      (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ ⟨r, by omega⟩).val ∧
      (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ ⟨r + 1, hr⟩).val ∧
      (∀ k, Pg e (σ k).val ⊆
          (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
        r ≤ k.val ∧ k.val ≤ r + 1) ∧
      Disjoint ((u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
        (G (ends e).1 '' CpBd (ends e).1) ∧
      (u' r ∘ g' r) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
        G (ends e).2 '' Bb e ∩ interior (Tp e) := by
    obtain ⟨hP, hu, huP, hg, hgP, himage, hB, hzero, hone, hpos, hadj⟩ := hcert (q r)
    have hq' := hq r hr
    have hpair := hadj rfl
    refine ⟨hP, hu, huP, hg, hgP, ?_, hB, ?_, ?_, ?_, hpair⟩
    · simpa only [hq'] using himage
    · simpa only [hq'] using hzero
    · simpa only [hq'] using hone
    · intro k
      simpa only [Fin.le_iff_val_le_val, hq'] using hpos k
  refine ⟨σ, D₀, D₁, hcap, hmono, hanti, hdis, hleft, hright,
    P', u', g', hchosen, ?_⟩
  intro i j hi hj hpar
  apply section34_ordered_band_sides_eq_of_parity hprep hpack e σ.injective
    (fun r => ⟨(hcap r).1, (hcap r).2.1, (hcap r).2.2.1, (hcap r).2.2.2.1⟩)
    hmono.monotone hanti.antitone hdis ?_ hi hj hpar
  intro r hr
  obtain ⟨-, hu, -, hg, hgP, himage, hB, hzero, hone, -, hempty, -⟩ := hchosen r hr
  have hmaps : MapsTo (g' r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (P' r) :=
    fun x hx => hgP ⟨x, hx, rfl⟩
  exact ⟨hu.continuousOn.comp hg.isPiecewiseAffineOn.continuousOn hmaps,
    hu.injOn.comp hg.bijOn.injOn hmaps, himage, hzero, hone, hB, hempty⟩

end DifferentialGeometry.Topology.PiecewiseLinear
