import DifferentialGeometry.Topology.PiecewiseLinear.Section34PrescribedAnnularRegion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularRegionSecondTrace

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

theorem exists_section34_empty_annular_region
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
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3)))
      (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      D ∩ F = Pg e i ∪ Pg e j ∧
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = D ∪ F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ Tp e ∧ (u '' R.space) ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      (u '' R.space) ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) ∧
      Disjoint (u '' R.space) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F ∧
      G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D ∧
      (u '' R.space ⊆ G (ends e).1 '' Cp (ends e).1 ∨
        (u '' R.space) ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  obtain ⟨F', P, u, R, hF', hF'A, hDF, hP, hu, hCc, hRfin, hR, hfront, hreg,
    hint, hext, hRP, hRT, hcontact, hsecond, hRdis, hfirst, hside⟩ :=
    exists_section34_matched_annular_region hprep hpack e hi hj hij hiess hjess
      huD hφ hφP hDT hzero hone hempty
  have hFeq := section34_first_band_eq_of_same_essential_ends hprep hpack e hi hj hij
    hiess hjess hF' hF hF'A hFA
  rw [hFeq] at hDF hfront hcontact hfirst hside
  let _ : Finite R.faces := hRfin.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have hclosed : IsClosed (u '' R.space) :=
    (hRpoly.isCompact.image_of_continuousOn huR.continuousOn).isClosed
  have htarget : frontier (u '' R.space) =
      (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F := by
    rw [← huR.image_frontier_of_isCompact hRpoly.isCompact]
    exact hfront
  have hmap : MapsTo φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) PD :=
    fun x hx => hφP ⟨x, hx, rfl⟩
  have hFtrace : F ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ Pg e i ∪ Pg e j := by
    intro x hx
    by_contra hn
    exact disjoint_left.mp hFempty ⟨hx.1, hn⟩ hx.2
  have hsecondEq := section34_annular_region_second_trace hprep hpack e hi hj hij hiess hjess
    (huD.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hmap)
    (fun x hx y hy hxy => hφ.bijOn.injOn hx hy (huD.injOn (hmap hx) (hmap hy) hxy))
    (hDT.trans inter_subset_left) hzero hone hclosed hRT htarget hFtrace
  exact ⟨P, u, R, hDF, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRT,
    hcontact, hsecond, hRdis, hfirst, hsecondEq, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
