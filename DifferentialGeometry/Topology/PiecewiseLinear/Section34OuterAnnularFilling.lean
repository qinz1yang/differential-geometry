import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding

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

theorem exists_section34_filling_of_annulus_pair_in_outer_interior
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {D F : Set (EuclideanSpace ℝ (Fin 3))}
    {uD uF : EuclideanSpace ℝ (Fin 3) → M₂}
    (hD : IsPLHomeomorphInto 3 uD D) (hF : IsPLHomeomorphInto 3 uF F)
    {φ ψ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hDT : uD '' D ⊆ interior (Sp e)) (hFT : uF '' F ⊆ interior (Sp e))
    (hDF : uD '' D ∩ uF '' F = (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hends : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      (uF ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1})) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = uD '' D ∪ uF '' F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ interior (Sp e) := by
  obtain ⟨P, u, K, g, hP, hu, hCc, hKfin, hKP, hKimage, hK, hg, hgends⟩ :=
    exists_section34_outer_tube_cylindrical_model hprep hpack e
  let _ : Finite K.faces := hKfin.to_subtype
  have hsolid := hg.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hgends
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  obtain ⟨R, hRfin, hR, hfront, hreg, hint, hext, hRK⟩ :=
    hu.exists_manifold_filling_of_annulus_pair_in_torus hD hF K hK hKP hsolid
      hcircle hcircle hφ hψ (hKimage.symm ▸ hDT.trans interior_subset)
      (hKimage.symm ▸ hFT.trans interior_subset) hDF hends
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space ⊆ P := hRK.trans hKP
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have hRS : u '' R.space ⊆ Sp e := hKimage ▸ image_mono hRK
  have htarget : frontier (u '' R.space) = uD '' D ∪ uF '' F := by
    rw [← huR.image_frontier_of_isCompact hRpoly.isCompact]
    exact hfront
  refine ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, ?_⟩
  intro x hx
  by_contra hxS
  have hxfront : x ∈ frontier (u '' R.space) :=
    ⟨subset_closure hx, fun h => hxS (interior_mono hRS h)⟩
  rw [htarget] at hxfront
  exact hxS (union_subset hDT hFT hxfront)

end DifferentialGeometry.Topology.PiecewiseLinear
