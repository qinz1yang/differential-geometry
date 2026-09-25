import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterMatchedAnnularContacts
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterSolidBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierFaceAlignedFilling

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



theorem exists_section34_outer_face_aligned_filling_of_empty_bands
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
    Section34FaceAlignedBandFilling (G (ends e).1 '' Cc (ends e).1) X As Bs
      (interior (Sp e)) (v '' D) (w '' F) J L := by
  have hφfull : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = v '' D := by
    rw [image_comp, hφ.image_eq]
  have hψfull : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = w '' F := by
    rw [image_comp, hψ.image_eq]
  have hφmap := hφ.bijOn.mapsTo
  have hψmap := hψ.bijOn.mapsTo
  have hannD := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hv.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hφmap)
    (hv.injOn.comp hφ.bijOn.injOn hφmap)
  have hannF := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hw.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn hψmap)
    (hw.injOn.comp hψ.bijOn.injOn hψmap)
  rw [hφfull, hφ₀, hφ₁] at hannD
  rw [hψfull, hψ₀, hψ₁] at hannF
  have hopen := image_lateral_open_eq_sdiff_ends (hv.injOn.comp hφ.bijOn.injOn hφmap)
  rw [hφfull, hφ₀, hφ₁] at hopen
  have hJF : J ∪ L ⊆ w '' F := union_subset hannF.first_subset hannF.second_subset
  have hJD : J ∪ L ⊆ v '' D := union_subset hannD.first_subset hannD.second_subset
  have htrace : v '' D ∩ As = J ∪ L := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact disjoint_left.mp hempty (hopen.symm ▸ And.intro hx.1 hn) hx.2
    · exact fun x hx => ⟨hJD hx, hAAs (hFA (hJF hx))⟩
  have hDF : v '' D ∩ w '' F = J ∪ L :=
    Subset.antisymm (fun x hx => htrace.subset ⟨hx.1, hAAs (hFA hx.2)⟩)
      (fun x hx => ⟨hJD hx, hJF hx⟩)
  have hφends : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) = J ∪ L := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl,
      prod_union, image_union, hφ₀, hφ₁]
  have hψends : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) = J ∪ L := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl,
      prod_union, image_union, hψ₀, hψ₁]
  obtain ⟨P₀, u₀, R₀, -, hu₀, -, hR₀fin, hR₀, hfront₀, -, -, -, hR₀P, hR₀S,
    -, -, -, -, hfirst₀, hsecond₀, hside₀⟩ :=
    exists_section34_outer_region_of_empty_annular_bands hprep hpack e hX hA hAAs hAS
      hY hB hBBs hBS hJ hL hJL hJend hLend hJendB hLendB hJcarry hLcarry
      hv hw hφ hψ hDB hFA hφ₀ hφ₁ hψ₀ hψ₁ hempty hFempty
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  have hsolid := exists_section34_outer_solid_band_filling_of_region hprep hpack e hv hw
    hφ hψ (hDF.trans hφends.symm) (hφends.trans hψends.symm) (hφ₀.symm ▸ hJcarry)
    hu₀ R₀ hR₀ hR₀P hfront₀ hR₀S hfirst₀ hsecond₀ hside₀
  exact hsolid.toFaceAlignedBandFilling_of_carrying_rims
    (section34_tubes_are_topological_solid_tori hprep hpack e).1 interior_subset
    hJ hL hJL hJcarry hLcarry hannF hannD.isCompact.isClosed hDF

end DifferentialGeometry.Topology.PiecewiseLinear
