import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterMatchedAnnularRegion

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



theorem exists_section34_outer_region_of_empty_annular_bands
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {X As A A₀ A₁ Y Bs B B₀ B₁ J L : Set M₂} (hX : IsPLCellOn 3 X As)
    (hA : IsAnnulusOn A A₀ A₁) (hAAs : A ⊆ As) (hAS : A ⊆ interior (Sp e))
    (hY : IsPLCellOn 3 Y Bs) (hB : IsAnnulusOn B B₀ B₁)
    (hBBs : B ⊆ Bs) (hBS : B ⊆ interior (Sp e))
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hL : IsPolyhedralSphere (n := 3) 1 L)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hJendB : Disjoint J (B₀ ∪ B₁)) (hLendB : Disjoint L (B₀ ∪ B₁))
    (hJcarry : CarriesFundamentalGroupOnto J (Sp e))
    (hLcarry : CarriesFundamentalGroupOnto L (Sp e))
    {D F : Set (EuclideanSpace ℝ (Fin 3))}
    {v w : EuclideanSpace ℝ (Fin 3) → M₂}
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w F)
    {φ ψ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hDB : v '' D ⊆ B) (hFA : w '' F ⊆ A)
    (hφ₀ : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hφ₁ : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    (hψ₀ : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hψ₁ : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    (hempty : Disjoint ((v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) As)
    (hFempty : Disjoint ((w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) Bs) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = v '' D ∪ w '' F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ interior (Sp e) ∧ IsCompact (u '' R.space) ∧
      closure (interior (u '' R.space)) = u '' R.space ∧
      IsConnected (interior (u '' R.space)) ∧
      frontier (u '' R.space) = v '' D ∪ w '' F ∧ As ∩ u '' R.space = w '' F ∧
      Bs ∩ u '' R.space = v '' D ∧
      (u '' R.space ⊆ X ∨ u '' R.space ∩ X = w '' F) := by
  obtain ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRS,
    hcompact, hreg', hint', htarget, hfirst, hside⟩ :=
    exists_section34_outer_region_of_empty_second_band hprep hpack e hX hA hAAs hAS
      hJ hL hJL hJend hLend hJcarry hLcarry hv hw hφ hψ (hDB.trans hBS) hFA
      hφ₀ hφ₁ hψ₀ hψ₁ hempty
  have hφfull : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = v '' D := by
    rw [image_comp, hφ.image_eq]
  have hψfull : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = w '' F := by
    rw [image_comp, hψ.image_eq]
  have hannD := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hv.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hφ.bijOn.mapsTo)
    (hv.injOn.comp hφ.bijOn.injOn hφ.bijOn.mapsTo)
  rw [hφfull, hφ₀, hφ₁] at hannD
  have hopen := image_lateral_open_eq_sdiff_ends
    (hw.injOn.comp hψ.bijOn.injOn hψ.bijOn.mapsTo)
  rw [hψfull, hψ₀, hψ₁] at hopen
  have hDC : v '' D ⊆ u '' R.space :=
    subset_union_left.trans (htarget ▸ hcompact.isClosed.frontier_subset)
  have hfrontBs : frontier (u '' R.space) ∩ Bs ⊆ v '' D := by
    rw [htarget]
    rintro x ⟨hxD | hxF, hxBs⟩
    · exact hxD
    · have hxends : x ∈ J ∪ L := by
        by_contra hn
        exact disjoint_left.mp hFempty (hopen.symm ▸ And.intro hxF hn) hxBs
      exact union_subset hannD.first_subset hannD.second_subset hxends
  have hsecond := hY.inter_eq_annulus_of_carrier_ends hB hBBs hJ hL hJL hJendB hLendB
    (section34_tubes_are_topological_solid_tori hprep hpack e).1
    (hBS.trans interior_subset) hJcarry hLcarry hannD hDB hDC hfrontBs
    (hRS.trans interior_subset)
  exact ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRS,
    hcompact, hreg', hint', htarget, hfirst, hsecond, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
