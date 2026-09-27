import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedAnnularFilling
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding

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

theorem exists_section34_annular_filling_with_interior_second_contact
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
    (hDT : uD '' D ⊆ interior (Tp e)) (hFT : uF '' F ⊆ Tp e)
    (hFA : uF '' F ⊆ G (ends e).1 '' CpBd (ends e).1)
    (hDF : uD '' D ∩ uF '' F = (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hends : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      (uF ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1})) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = uD '' D ∪ uF '' F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ Tp e ∧
      (u '' R.space) ∩ frontier (Tp e) = (uF '' F) ∩ frontier (Tp e) ∧
      (u '' R.space) ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) := by
  obtain ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRT⟩ :=
    exists_section34_filling_of_annulus_pair hprep hpack e hD hF hφ hψ
      (hDT.trans interior_subset) hFT hDF hends
  let _ : Finite R.faces := hRfin.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have htarget : frontier (u '' R.space) = uD '' D ∪ uF '' F := by
    rw [← huR.image_frontier_of_isCompact hRpoly.isCompact]
    exact hfront
  have hbound : uD '' D ∪ uF '' F ⊆ u '' R.space := by
    rw [← hfront]
    exact image_mono hRpoly.isClosed.frontier_subset
  have hFsub : uF '' F ⊆ u '' R.space := subset_union_right.trans hbound
  have hcontact {x : M₂} (hx : x ∈ u '' R.space) (hnot : x ∉ interior (Tp e)) :
      x ∈ uF '' F := by
    have hxfront : x ∈ frontier (u '' R.space) :=
      ⟨subset_closure hx, fun h => hnot (interior_mono hRT h)⟩
    rw [htarget] at hxfront
    exact hxfront.resolve_left (fun hxD => hnot (hDT hxD))
  refine ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRT, ?_, ?_⟩
  · exact Subset.antisymm (fun x hx => ⟨hcontact hx.1 hx.2.2, hx.2⟩)
      (inter_subset_inter_left _ hFsub)
  · intro x hx
    by_contra hnot
    obtain ⟨-, -, -, -, -, -, hcross, -⟩ := hpack
    exact hnot ((hcross e ⟨hFA (hcontact hx.1 hnot), hx.2⟩).2)

end DifferentialGeometry.Topology.PiecewiseLinear
