import DifferentialGeometry.Topology.PiecewiseLinear.Section34PrescribedAnnularRegion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.isPLTorus_of_image_eq_annulus_pair
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C D F : Set (EuclideanSpace ℝ (Fin 3))}
    {u v w : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hv : IsPLHomeomorphInto 3 v D) (hw : IsPLHomeomorphInto 3 w F)
    {ρ σ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hσ : IsPLHomeomorphOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hCP : C ⊆ P) (himage : u '' C = v '' D ∪ w '' F)
    (hmeet : v '' D ∩ w '' F = (v ∘ ρ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hends : (v ∘ ρ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      (w ∘ σ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1})) : IsPLTorus C := by
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have hsub : v '' D ∪ w '' F ⊆ u '' P := himage.symm ▸ image_mono hCP
  have htorus := hu.isPLTorus_invFunOn_of_annulus_pair hv hw hcircle hcircle hρ hσ
    (subset_union_left.trans hsub) (subset_union_right.trans hsub) hmeet hends
  have heq : Function.invFunOn u P '' (u '' C) = C := by
    rw [image_image]
    exact (image_congr fun x hx => hu.injOn.leftInvOn_invFunOn (hCP hx)).trans (image_id' C)
  rwa [← himage, heq] at htorus

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

theorem section34_annular_filling_frontier_isPLTorus
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
    (hzero : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {0}) = Pg e i)
    (hone : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {1}) = Pg e j)
    {F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hFA : F ⊆ G (ends e).1 '' Aa e)
    (hDF : ((uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ F =
      Pg e i ∪ Pg e j)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hRP : R.space ⊆ P)
    (hfront : u '' frontier R.space =
      (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F) :
    IsPLTorus (frontier R.space) := by
  obtain ⟨PF, uF, ψ, -, huF, hψ, hψP, hψA, hψ₀, hψ₁, -⟩ :=
    exists_section34_first_annular_band_of_essential_second_pair hprep hpack e
      hi hj hij hiess hjess
  let L := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  have hmaps : MapsTo ψ L PF := fun x hx => hψP ⟨x, hx, rfl⟩
  have hFann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (huF.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn hmaps)
    (huF.injOn.comp hψ.bijOn.injOn hmaps)
  rw [hψ₀, hψ₁] at hFann
  have hFeq := section34_first_band_eq_of_same_essential_ends hprep hpack e hi hj hij
    hiess hjess hFann hF hψA hFA
  have hFimage : uF '' (ψ '' L) = F := by rw [← image_comp]; exact hFeq
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have hpoly : IsPolyhedron L := hcircle.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hDpoly := hpoly.image_of_isPiecewiseAffineOn hφ.isPiecewiseAffineOn hφ.bijOn.injOn
  have hFpoly := hpoly.image_of_isPiecewiseAffineOn hψ.isPiecewiseAffineOn hψ.bijOn.injOn
  have hDu : IsPLHomeomorphInto 3 uD (φ '' L) :=
    (huD.isPLOn.mono_of_isPolyhedron hDpoly hφP).isPLHomeomorphInto_model
      hDpoly.isCompact (huD.injOn.mono hφP)
  have hFu : IsPLHomeomorphInto 3 uF (ψ '' L) :=
    (huF.isPLOn.mono_of_isPolyhedron hFpoly hψP).isPLHomeomorphInto_model
      hFpoly.isCompact (huF.injOn.mono hψP)
  have hendsD : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      Pg e i ∪ Pg e j := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl, prod_union, image_union, hzero, hone]
  have hendsF : (uF ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      Pg e i ∪ Pg e j := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl, prod_union, image_union, hψ₀, hψ₁]
  apply hu.isPLTorus_of_image_eq_annulus_pair hDu hFu hφ hψ
    ((isPolyhedron_space R).isClosed.frontier_subset.trans hRP) ?_ ?_
    (hendsD.trans hendsF.symm)
  · rw [hFimage, ← image_comp]
    exact hfront
  · rw [hFimage, ← image_comp, hendsD]
    exact hDF

end DifferentialGeometry.Topology.PiecewiseLinear
