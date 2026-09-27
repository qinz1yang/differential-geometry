import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterAnnularFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierAnnulusContact

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


theorem exists_section34_outer_region_of_empty_second_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {X As A A₀ A₁ J L : Set M₂} (hX : IsPLCellOn 3 X As)
    (hA : IsAnnulusOn A A₀ A₁) (hAAs : A ⊆ As) (hAS : A ⊆ interior (Sp e))
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hL : IsPolyhedralSphere (n := 3) 1 L)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hJcarry : CarriesFundamentalGroupOnto J (Sp e))
    (hLcarry : CarriesFundamentalGroupOnto L (Sp e))
    {D F : Set (EuclideanSpace ℝ (Fin 3))}
    {v w : EuclideanSpace ℝ (Fin 3) → M₂}
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w F)
    {φ ψ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hDS : v '' D ⊆ interior (Sp e)) (hFA : w '' F ⊆ A)
    (hφ₀ : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hφ₁ : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    (hψ₀ : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hψ₁ : (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    (hempty : Disjoint ((v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) As) :
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
      (u '' R.space ⊆ X ∨ u '' R.space ∩ X = w '' F) := by
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
  obtain ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRS⟩ :=
    exists_section34_filling_of_annulus_pair_in_outer_interior hprep hpack e hv hw hφ hψ
      hDS (hFA.trans hAS) (hDF.trans hφends.symm) (hφends.trans hψends.symm)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have hcompact := hRpoly.isCompact.image_of_continuousOn huR.continuousOn
  have htarget : frontier (u '' R.space) = v '' D ∪ w '' F := by
    rw [← huR.image_frontier_of_isCompact hRpoly.isCompact, hfront]
  have hreg' : closure (interior (u '' R.space)) = u '' R.space := by
    apply Subset.antisymm (closure_minimal interior_subset hcompact.isClosed)
    calc
      u '' R.space = u '' closure (interior R.space) := by rw [hreg]
      _ ⊆ closure (u '' interior R.space) :=
        ContinuousOn.image_closure (by rw [hreg]; exact huR.continuousOn)
      _ = closure (interior (u '' R.space)) := by rw [huR.image_interior]
  have hint' := hint.image u (huR.continuousOn.mono interior_subset)
  rw [huR.image_interior] at hint'
  have hFC : w '' F ⊆ u '' R.space :=
    subset_union_right.trans (htarget ▸ hcompact.isClosed.frontier_subset)
  have hfrontAs : frontier (u '' R.space) ∩ As ⊆ w '' F := by
    rw [htarget]
    rintro x ⟨hxD | hxF, hxAs⟩
    · exact hJF (htrace.subset ⟨hxD, hxAs⟩)
    · exact hxF
  have hfirst := hX.inter_eq_annulus_of_carrier_ends hA hAAs hJ hL hJL hJend hLend
    (section34_tubes_are_topological_solid_tori hprep hpack e).1
    (hAS.trans interior_subset) hJcarry hLcarry hannF hFA hFC hfrontAs
    (hRS.trans interior_subset)
  have hside := subset_or_inter_eq_of_connected_interior hX.isCompact.isClosed hreg'
    hint'.isPreconnected (hX.boundary_eq_frontier ▸ hfirst)
    (htarget.symm ▸ subset_union_right)
  exact ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRS,
    hcompact, hreg', hint', htarget, hfirst, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
