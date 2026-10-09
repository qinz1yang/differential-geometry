import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingTorus
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EmptyAnnularRegion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_recharted_manifold_interior
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (S R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite R.faces]
    {u v : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u S.space) (hv : IsPLHomeomorphInto 3 v R.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsub : v '' R.space ⊆ interior (u '' S.space)) :
    ∃ N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
      N.space ⊆ interior S.space ∧ u '' N.space = v '' R.space ∧
      u '' frontier N.space = v '' frontier R.space := by
  let τ := Function.invFunOn u S.space ∘ v
  have hτ := hv.isPLHomeomorphOn_invFunOn_comp (isPolyhedron_space R) hu
    (hsub.trans interior_subset)
  obtain ⟨N, hNfin, hNspace, hτN⟩ :=
    exists_isPLHomeomorphOn_image R hτ.isPiecewiseAffineOn hτ.bijOn.injOn
  let _ : Finite N.faces := hNfin.to_subtype
  have hNsub : N.space ⊆ interior S.space := by
    rw [hNspace]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hu.image_interior.symm.subset (hsub ⟨x, hx, rfl⟩)
    dsimp only [τ, Function.comp_apply]
    rw [← heq, hu.injOn.leftInvOn_invFunOn (interior_subset hy)]
    exact hy
  have hcomp : EqOn (u ∘ τ) v R.space := fun x hx =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 (interior_subset (hsub ⟨x, hx, rfl⟩))
  have himage : u '' N.space = v '' R.space := by
    rw [hNspace, ← image_comp]
    exact image_congr hcomp
  have hfront := hτN.image_frontier rfl (isPolyhedron_space R).isClosed
    (isPolyhedron_space N).isClosed
  refine ⟨N, hNfin, hR.of_isPLHomeomorphOn hτN, hNsub, himage, ?_⟩
  rw [← hfront, ← image_comp]
  exact image_congr (hcomp.mono (isPolyhedron_space R).isClosed.frontier_subset)

theorem IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image_of_subset
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P) (hCP : C ⊆ P)
    (hgen : CarriesFundamentalGroupOnto (u '' C) (u '' P)) :
    CarriesFundamentalGroupOnto C P := by
  have hg := hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn
  have hginj : InjOn (Function.invFunOn u P) (u '' P) := by
    intro x hx y hy hxy
    rw [← hu.injOn.bijOn_image.invOn_invFunOn.2 hx,
      ← hu.injOn.bijOn_image.invOn_invFunOn.2 hy, hxy]
  have hcarry := hgen.image_of_compact (hP.image_of_continuousOn hu.continuousOn)
    (fun x hx => (hg x hx).continuousWithinAt) hginj
  have himage (A : Set (EuclideanSpace ℝ (Fin 3))) (hAP : A ⊆ P) :
      Function.invFunOn u P '' (u '' A) = A := by
    rw [image_image]
    exact (image_congr fun x hx => hu.injOn.leftInvOn_invFunOn (hAP hx)).trans (image_id' A)
  rwa [himage C hCP, himage P Subset.rfl] at hcarry

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


theorem section34_annular_filling_boundary_carries_generators
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i j : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hRP : R.space ⊆ P) (hT : IsPLTorus (frontier R.space))
    (hfront : u '' frontier R.space = D ∪ F) (hRT : u '' R.space ⊆ Tp e) :
    CarriesFundamentalGroupOnto (u '' frontier R.space) (Tp e) ∧
      CarriesFundamentalGroupOnto (u '' frontier R.space) (Sp e) := by
  have hclosed := (isPolyhedron_space R).isClosed
  have hFT : u '' frontier R.space ⊆ Tp e := (image_mono hclosed.frontier_subset).trans hRT
  have hJF : Pg e i ⊆ u '' frontier R.space := by
    rw [hfront]
    exact hF.first_subset.trans subset_union_right
  have hpath := hT.isPathConnected.image'
    (hu.continuousOn.mono (hclosed.frontier_subset.trans hRP))
  have hgen := section34_piercing_generators_of_essential_second hprep hpack e hi hess
  have hFS := hFT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  exact ⟨hgen.2.1.mono_of_isPathConnected hF.ends_nonempty.1 hJF hFT hpath,
    hgen.1.mono_of_isPathConnected hF.ends_nonempty.1 hJF hFS hpath⟩

theorem exists_section34_empty_annular_filling_in_tube_model
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {PD : Set (EuclideanSpace ℝ (Fin 3))} {uD : EuclideanSpace ℝ (Fin 3) → M₂}
    (huD : IsPLHomeomorphInto 3 uD PD)
    {φ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)))
    (hφP : φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ PD)
    (hDT : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆
      G (ends e).2 '' Bb e ∩ interior (Tp e))
    (hzero : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hone : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    (hempty : Disjoint ((uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (G (ends e).1 '' CpBd (ends e).1))
    {F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hFA : F ⊆ G (ends e).1 '' Aa e)
    (hFempty : Disjoint (F \ (Pg e i ∪ Pg e j))
      (G (ends e).2 '' CpBd (ends e).2)) :
    let D := (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (S R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      S.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 S ∧ S.space ⊆ P ∧
      u '' S.space = Sp e ∧ IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S.space ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1)) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space ⊆ interior S.space ∧ IsPLTorus (frontier R.space) ∧
      CarriesFundamentalGroupOnto (frontier R.space) S.space ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ Tp e ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F ∧
      G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      (u '' R.space ⊆ G (ends e).1 '' Cp (ends e).1 ∨
        u '' R.space ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  obtain ⟨P₀, u₀, R₀, hDF, -, hu₀, -, hR₀fin, hR₀, hfront₀, -, -, -, hR₀P,
    hR₀T, hcontact, -, -, hfirst, hsecond, hside⟩ :=
    exists_section34_empty_annular_region hprep hpack e hi hj hij hiess hjess
      huD hφ hφP hDT hzero hone hempty hF hFA hFempty
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨P, u, S, f, hP, hu, hcell, hSfin, hSP, hSimage, hS, hf, hends⟩ :=
    exists_section34_outer_tube_cylindrical_model hprep hpack e
  let _ : Finite S.faces := hSfin.to_subtype
  have huS : IsPLHomeomorphInto 3 u S.space :=
    (hu.isPLOn.mono_of_isPolyhedron (isPolyhedron_space S) hSP).isPLHomeomorphInto_model
      (isPolyhedron_space S).isCompact (hu.injOn.mono hSP)
  have huR₀ : IsPLHomeomorphInto 3 u₀ R₀.space :=
    (hu₀.isPLOn.mono_of_isPolyhedron (isPolyhedron_space R₀) hR₀P).isPLHomeomorphInto_model
      (isPolyhedron_space R₀).isCompact (hu₀.injOn.mono hR₀P)
  have hR₀S : u₀ '' R₀.space ⊆ interior (u '' S.space) := by
    rw [hSimage]
    exact hR₀T.trans (section34_inner_tube_subset_interior_outer hprep hpack e)
  obtain ⟨R, hRfin, hR, hRS, hRimage, hfrontimage⟩ :=
    huS.exists_recharted_manifold_interior S R₀ huR₀ hR₀ hR₀S
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space ⊆ P := hRS.trans (interior_subset.trans hSP)
  have hfront := hfrontimage.trans hfront₀
  have hRT : u '' R.space ⊆ Tp e := hRimage ▸ hR₀T
  have htor := section34_annular_filling_frontier_isPLTorus hprep hpack e hi hj hij
    hiess hjess huD hφ hφP hzero hone hF hFA hDF hu R hRP hfront
  have hgen := (section34_annular_filling_boundary_carries_generators hprep hpack e hi
    hiess hF hu R hRP htor hfront hRT).2
  rw [← hSimage] at hgen
  have hgenmodel := huS.carriesFundamentalGroupOnto_of_image_of_subset (isPolyhedron_space S).isCompact
    ((isPolyhedron_space R).isClosed.frontier_subset.trans (hRS.trans interior_subset)) hgen
  refine ⟨P, u, S, R, f, hP, hu, hcell, hSfin, hS, hSP, hSimage, hf, hends,
    hRfin, hR, hRS, htor, hgenmodel, hfront, hRT, ?_, ?_, ?_, ?_⟩
  · rwa [hRimage]
  · rwa [hRimage]
  · rwa [hRimage]
  · rwa [hRimage]

end DifferentialGeometry.Topology.PiecewiseLinear
