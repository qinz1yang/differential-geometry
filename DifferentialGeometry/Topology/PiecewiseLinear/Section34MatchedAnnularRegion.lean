import DifferentialGeometry.Topology.PiecewiseLinear.Section34MatchingAnnularBand
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularContactControl
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeRims

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

theorem exists_section34_matched_annular_region
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
      (G (ends e).1 '' CpBd (ends e).1)) :
    let D := (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
    ∃ (F : Set M₂) (P : Set (EuclideanSpace ℝ (Fin 3)))
      (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsAnnulusOn F (Pg e i) (Pg e j) ∧ F ⊆ G (ends e).1 '' Aa e ∧
      D ∩ F = Pg e i ∪ Pg e j ∧
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = D ∪ F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ Tp e ∧ (u '' R.space) ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      (u '' R.space) ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) ∧
      Disjoint (u '' R.space) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F ∧
      (u '' R.space ⊆ G (ends e).1 '' Cp (ends e).1 ∨
        (u '' R.space) ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  let L := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let D := (uD ∘ φ) '' L
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have hdom : IsPolyhedron L := hcircle.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -, -, -, -, -, -, hPg, -⟩ := id hpack
  have hAB : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hJB (k : ℕ) (hk : k < cnt e) : Pg e k ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hx => hAB (image_mono sdiff_subset ((hPg e k hk).2 hx).1)
  have hendD : Pg e i ∪ Pg e j ⊆ D := by
    rw [← hzero, ← hone]
    exact union_subset (image_mono (prod_mono_right (by simp)))
      (image_mono (prod_mono_right (by simp)))
  have htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i ∪ Pg e j := by
    apply Subset.antisymm
    · rintro _ ⟨⟨p, hp, rfl⟩, hxA⟩
      by_cases h0 : p.2 = 0
      · exact Or.inl (hzero.subset ⟨p, ⟨hp.1, h0⟩, rfl⟩)
      by_cases h1 : p.2 = 1
      · exact Or.inr (hone.subset ⟨p, ⟨hp.1, h1⟩, rfl⟩)
      exact (disjoint_left.mp hempty
        ⟨p, ⟨hp.1, lt_of_le_of_ne hp.2.1 (Ne.symm h0), lt_of_le_of_ne hp.2.2 h1⟩, rfl⟩
        hxA).elim
    · exact fun _ hx => ⟨hendD hx, (union_subset (hJB i hi) (hJB j hj)) hx⟩
  obtain ⟨PF, uF, ψ, -, huF, hψ, hψP, hFA, hFzero, hFone, hDF, hFT, hcert⟩ :=
    exists_section34_matching_annular_band hprep hpack e hi hj hij hiess hjess
      (hDT.trans (inter_subset_right.trans interior_subset)) htrace
  let F := (uF ∘ ψ) '' L
  have hDpoly : IsPolyhedron (φ '' L) :=
    hdom.image_of_isPiecewiseAffineOn hφ.isPiecewiseAffineOn hφ.bijOn.injOn
  have hFpoly : IsPolyhedron (ψ '' L) :=
    hdom.image_of_isPiecewiseAffineOn hψ.isPiecewiseAffineOn hψ.bijOn.injOn
  have hDu : IsPLHomeomorphInto 3 uD (φ '' L) :=
    (huD.isPLOn.mono_of_isPolyhedron hDpoly hφP).isPLHomeomorphInto_model
      hDpoly.isCompact (huD.injOn.mono hφP)
  have hFu : IsPLHomeomorphInto 3 uF (ψ '' L) :=
    (huF.isPLOn.mono_of_isPolyhedron hFpoly hψP).isPLHomeomorphInto_model
      hFpoly.isCompact (huF.injOn.mono hψP)
  have hendsD : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) = Pg e i ∪ Pg e j := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl, prod_union, image_union,
      hzero, hone]
  have hendsF : (uF ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) = Pg e i ∪ Pg e j := by
    rw [show ({(0 : ℝ), 1} : Set ℝ) = {0} ∪ {1} from rfl, prod_union, image_union,
      hFzero, hFone]
  have hDint : uD '' (φ '' L) ⊆ interior (Tp e) := by
    rw [← image_comp]
    exact hDT.trans inter_subset_right
  have hFT' : uF '' (ψ '' L) ⊆ Tp e := by
    rw [← image_comp]
    exact subset_union_left.trans hFT
  have hFbound : uF '' (ψ '' L) ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [← image_comp]
    exact hFA.trans hAB
  obtain ⟨P, u, R, hP, hu, hCc, hRfin, hR, hfront, hreg, hint, hext, hRP, hRT,
    hcontact, hsecond⟩ := exists_section34_annular_filling_with_interior_second_contact
      hprep hpack e hDu hFu hφ hψ hDint hFT' hFbound
      (by simpa only [← image_comp, hendsD] using hDF) (hendsD.trans hendsF.symm)
  have hmapψ : MapsTo ψ L PF := fun x hx => hψP ⟨x, hx, rfl⟩
  have hFann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (huF.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn hmapψ)
    (fun x hx y hy hxy => hψ.bijOn.injOn hx hy (huF.injOn (hmapψ hx) (hmapψ hy) hxy))
  rw [hFzero, hFone] at hFann
  have hrims := section34_first_rims_subset_inner_frontier hprep hpack e
  have hJdis : Disjoint (Pg e i ∪ Pg e j) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) :=
    disjoint_interior_frontier.mono (hendD.trans (hDT.trans inter_subset_right)) hrims
  have hann := (section34_piercing_annuli hprep hpack e).1
  obtain ⟨hc⟩ := ((hCp (ends e).1).image (hG (ends e).1)).nonempty_chartedSpace_boundary
  let _ := hc
  rw [image_union] at hJdis
  have hFdis := hFann.disjoint_ends_of_subset_within hann hAB hFA hJdis
  rw [← image_union] at hFdis
  have hRdis : Disjoint (u '' R.space) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
    refine disjoint_left.mpr fun x hx hxR => ?_
    have hxF := (hcontact.subset ⟨hx, hrims hxR⟩).1
    rw [← image_comp] at hxF
    exact disjoint_left.mp hFdis hxF hxR
  let _ : Finite R.faces := hRfin.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have hCfront : frontier (u '' R.space) = D ∪ F := by
    rw [← huR.image_frontier_of_isCompact hRpoly.isCompact, hfront]
    simp only [D, F, L, image_comp]
  have hCF : D ∪ F ⊆ u '' R.space := hCfront ▸
    (hRpoly.isCompact.image_of_continuousOn huR.continuousOn).isClosed.frontier_subset
  have hCtrace : frontier (u '' R.space) ∩ G (ends e).1 '' CpBd (ends e).1 ⊆ F := by
    rw [hCfront]
    rintro x ⟨hxD | hxF, hxA⟩
    · exact (hDF.superset (htrace.subset ⟨hxD, hxA⟩)).2
    · exact hxF
  have hfirst := hcert (u '' R.space) (subset_union_right.trans hCF) hCtrace hRdis
  have hclosed : IsClosed (u '' R.space) :=
    (hRpoly.isCompact.image_of_continuousOn huR.continuousOn).isClosed
  have hreg' : closure (interior (u '' R.space)) = u '' R.space := by
    apply Subset.antisymm (closure_minimal interior_subset hclosed)
    calc
      u '' R.space = u '' closure (interior R.space) := by rw [hreg]
      _ ⊆ closure (u '' interior R.space) :=
        ContinuousOn.image_closure (by rw [hreg]; exact huR.continuousOn)
      _ = closure (interior (u '' R.space)) := by rw [huR.image_interior]
  have hconn := hint.isPreconnected.image u (huR.continuousOn.mono interior_subset)
  rw [huR.image_interior] at hconn
  have hcell := (hCp (ends e).1).image (hG (ends e).1)
  have hside := subset_or_inter_eq_of_connected_interior hcell.isCompact.isClosed hreg' hconn
    (by rwa [← hcell.boundary_eq_frontier]) (hCfront.symm ▸ subset_union_right)
  simp only [← image_comp] at hfront hcontact hsecond
  exact ⟨F, P, u, R, hFann, hFA, hDF, hP, hu, hCc, hRfin, hR, hfront, hreg, hint,
    hext, hRP, hRT, hcontact, hsecond, hRdis, hfirst, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
