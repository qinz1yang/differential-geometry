import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingInTubeModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledPiercingConfiguration

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

theorem exists_section34_outer_solid_band_filling_of_region
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {X As Bs : Set M₂} {D F P₀ : Set (EuclideanSpace ℝ (Fin 3))}
    {v w u₀ : EuclideanSpace ℝ (Fin 3) → M₂}
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w F)
    {φ ψ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hDF : v '' D ∩ w '' F = (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hends : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      (w ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hcarry : CarriesFundamentalGroupOnto
      ((v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0})) (Sp e))
    (hu₀ : IsPLHomeomorphInto 3 u₀ P₀)
    (R₀ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R₀.faces]
    (hR₀ : IsCombinatorialManifoldWithBoundary 3 R₀) (hR₀P : R₀.space ⊆ P₀)
    (hfront₀ : u₀ '' frontier R₀.space = v '' D ∪ w '' F)
    (hR₀S : u₀ '' R₀.space ⊆ interior (Sp e))
    (hfirst₀ : As ∩ u₀ '' R₀.space = w '' F)
    (hsecond₀ : Bs ∩ u₀ '' R₀.space = v '' D)
    (hside₀ : u₀ '' R₀.space ⊆ X ∨ u₀ '' R₀.space ∩ X = w '' F) :
    Section34SolidBandFilling (G (ends e).1 '' Cc (ends e).1) X As Bs
      (interior (Sp e)) (v '' D) (w '' F) := by
  obtain ⟨P, u, S, f, hP, hu, hcell, hSfin, hSP, hSimage, hS, hf, hendsS⟩ :=
    exists_section34_outer_tube_cylindrical_model hprep hpack e
  let _ : Finite S.faces := hSfin.to_subtype
  have huS : IsPLHomeomorphInto 3 u S.space :=
    (hu.isPLOn.mono_of_isPolyhedron (isPolyhedron_space S) hSP).isPLHomeomorphInto_model
      (isPolyhedron_space S).isCompact (hu.injOn.mono hSP)
  have huR₀ : IsPLHomeomorphInto 3 u₀ R₀.space :=
    (hu₀.isPLOn.mono_of_isPolyhedron (isPolyhedron_space R₀) hR₀P).isPLHomeomorphInto_model
      (isPolyhedron_space R₀).isCompact (hu₀.injOn.mono hR₀P)
  obtain ⟨R, hRfin, hR, hRS, hRimage, hfrontimage⟩ :=
    huS.exists_recharted_manifold_interior S R₀ huR₀ hR₀ (hSimage.symm ▸ hR₀S)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space ⊆ P := hRS.trans (interior_subset.trans hSP)
  have hfront := hfrontimage.trans hfront₀
  have hclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have htor := hu.isPLTorus_of_image_eq_annulus_pair hv hw hφ hψ
    (hclosed.frontier_subset.trans hRP) hfront hDF hends
  have hφfull : (v ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = v '' D := by
    rw [image_comp, hφ.image_eq]
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hv.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hφ.bijOn.mapsTo)
    (hv.injOn.comp hφ.bijOn.injOn hφ.bijOn.mapsTo)
  rw [hφfull] at hann
  have hJF := hann.first_subset.trans (subset_union_left.trans hfront.symm.subset)
  have hFS : u '' frontier R.space ⊆ Sp e :=
    (image_mono hclosed.frontier_subset).trans ((hRimage ▸ hR₀S).trans interior_subset)
  have hgen := hcarry.mono_of_isPathConnected hann.ends_nonempty.1 hJF hFS
    (htor.isPathConnected.image' (hu.continuousOn.mono (hclosed.frontier_subset.trans hRP)))
  rw [← hSimage] at hgen
  have hgenmodel := huS.carriesFundamentalGroupOnto_of_image_of_subset (isPolyhedron_space S).isCompact
    (hclosed.frontier_subset.trans (hRS.trans interior_subset)) hgen
  obtain ⟨B, hBfin, hBspace⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_stdSimplex 2
  have hfB : IsCylindricalDiagram f B.space S.space := hBspace.symm ▸ hf
  have hendsB : ∀ x ∈ B.space, f (x, 0) = f (x, 1) := hBspace.symm ▸ hendsS
  obtain ⟨-, g, hg, hgend, hgfront⟩ :=
    hfB.exists_cylindrical_model_of_interior_torus_carrier B S R hB hS hendsB hR hRS htor
      hgenmodel isPLBall_unit_square (by simp [Module.finrank_prod])
  have hRT : u '' R.space ⊆ interior (Sp e) := hRimage ▸ hR₀S
  have hfirst : As ∩ u '' R.space = w '' F := hRimage ▸ hfirst₀
  have hcontact : u '' R.space ∩ frontier (interior (Sp e)) =
      w '' F ∩ frontier (interior (Sp e)) := by
    have hdis := disjoint_interior_frontier (s := interior (Sp e))
    rw [interior_interior] at hdis
    rw [Disjoint.inter_eq (hdis.mono_left hRT),
      Disjoint.inter_eq (hdis.mono_left ((hfirst.symm.subset.trans inter_subset_right).trans hRT))]
  exact ⟨P, u, R, g, hP, hu, hcell, hRfin, hR, hRP,
    hg.isCombinatorialSolidTorus isPLBall_unit_square (by simp), hg, hgend, hgfront,
    hfront, hRT, hfirst, hRimage ▸ hsecond₀, hcontact, hRimage ▸ hside₀⟩

end DifferentialGeometry.Topology.PiecewiseLinear
