import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedAnnularBandsTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularSideAlternation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isAnnulusOn_inter_of_disk_caps {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D₀ D₁ F₀ F₁ J L : Set M} (hS : IsPLCellOn 3 S B)
    (hD : IsPLCellOn 2 D₀ J) (hF : IsPLCellOn 2 F₁ L)
    (hDU : D₀ ∪ D₁ = B) (hDI : D₀ ∩ D₁ = J)
    (hFU : F₀ ∪ F₁ = B) (hFI : F₀ ∩ F₁ = L) (hdis : Disjoint D₀ F₁) :
    IsAnnulusOn (D₁ ∩ F₀) J L := by
  obtain ⟨P, u, f, -, hu, -, hf, hfP, himage, hzero, hone⟩ :=
    hS.exists_lateral_annulus_eq_inter_of_disk_caps hD hF hDU hDI hFU hFI hdis
  have hmap : MapsTo f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hfP ⟨x, hx, rfl⟩
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hu.continuousOn.comp hf.isPiecewiseAffineOn.continuousOn hmap)
    (hu.injOn.comp hf.bijOn.injOn hmap)
  rwa [himage, hzero, hone] at hann

theorem IsPLCellOn.isAnnulusOn_union_of_ordered_caps {M ι : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [Preorder ι] {S B : Set M} {J D₀ D₁ : ι → Set M} (hS : IsPLCellOn 3 S B)
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (J r) ∧ IsPLCellOn 2 (D₁ r) (J r) ∧
      D₀ r ∪ D₁ r = B ∧ D₀ r ∩ D₁ r = J r)
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    {i j k : ι} (hij : i < j) (hjk : j < k) :
    IsAnnulusOn ((D₁ i ∩ D₀ j) ∪ (D₁ j ∩ D₀ k)) (J i) (J k) := by
  rw [← inter_caps_eq_union_of_ordered_caps (fun r => (hcap r).2.2.1)
    hmono hanti hij.le hjk.le]
  exact hS.isAnnulusOn_inter_of_disk_caps (hcap i).1 (hcap k).2.1
    (hcap i).2.2.1 (hcap i).2.2.2 (hcap k).2.2.1 (hcap k).2.2.2
    (hdis i k (hij.trans hjk))

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

theorem section34_opposite_ordered_band_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {ι : Type*} [Preorder ι] {σ : ι → Fin (cnt e)} (hσ : Function.Injective σ)
    {D₀ D₁ : ι → Set M₂}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (Pg e (σ r)) ∧
      IsPLCellOn 2 (D₁ r) (Pg e (σ r)) ∧
      D₀ r ∪ D₁ r = G (ends e).2 '' CpBd (ends e).2 ∧
      D₀ r ∩ D₁ r = Pg e (σ r))
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    {i j k : ι} (hij : i < j) (hjk : j < k)
    {f g : (Fin 3 → ℝ) × ℝ → M₂}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (himagef : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j)
    (himageg : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ j ∩ D₀ k)
    (hfzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ i))
    (hfone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ j))
    (hgzero : g '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e (σ j))
    (hgone : g '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e (σ k))
    (hB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ G (ends e).2 '' Bb e)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1)) :
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1) ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ) ∨
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆
        interior (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, hPgdis, -⟩ := id hpack
  have hcell := (hCp (ends e).2).image (hGp (ends e).2)
  have hann : IsAnnulusOn (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) (Pg e (σ i)) (Pg e (σ k)) := by
    rw [himagef, himageg]
    exact hcell.isAnnulusOn_union_of_ordered_caps hcap hmono hanti hdis hij hjk
  have hAaCp : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hPgCp (r : ι) : Pg e (σ r) ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hy => image_mono hAaCp
      (image_mono sdiff_subset ((hPg e (σ r) (σ r).isLt).2 hy).1)
  have hfends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hfzero, hfone]
    exact union_subset (hPgCp i) (hPgCp j)
  have hgends : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hgzero, hgone]
    exact union_subset (hPgCp j) (hPgCp k)
  obtain ⟨T, hT⟩ := (hPg e (σ j) (σ j).isLt).1
  obtain ⟨x, hx⟩ : (Pg e (σ j)).Nonempty :=
    T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
  have hxf : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    image_mono (prod_mono_right (by simp)) (hfone.symm ▸ hx)
  have hxend : x ∉ Pg e (σ i) ∪ Pg e (σ k) := by
    rintro (hxi | hxk)
    · exact disjoint_left.mp (hPgdis e (σ j) (σ j).isLt (σ i) (σ i).isLt
        (fun h => hij.ne' (hσ (Fin.ext h)))) hx hxi
    · exact disjoint_left.mp (hPgdis e (σ j) (σ j).isLt (σ k) (σ k).isLt
        (fun h => hjk.ne (hσ (Fin.ext h)))) hx hxk
  exact section34_opposite_lateral_band_sides hprep hpack e hf hfi hg hgi hann hB hfends
    hgends hfempty hgempty (hPgCp j hx) (Or.inl hxf) hxend

end DifferentialGeometry.Topology.PiecewiseLinear
