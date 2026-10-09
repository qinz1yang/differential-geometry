import DifferentialGeometry.Topology.PiecewiseLinear.Section34MatchedAnnularRegion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandUniqueness

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

theorem section34_first_band_eq_of_same_essential_ends
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hD : IsAnnulusOn D (Pg e i) (Pg e j))
    (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hDA : D ⊆ G (ends e).1 '' Aa e) (hFA : F ⊆ G (ends e).1 '' Aa e) : D = F := by
  have hiA := (section34_piercing_generators_of_essential_second hprep hpack e hi hiess).2.2
  have hjA := (section34_piercing_generators_of_essential_second hprep hpack e hj hjess).2.2
  have hann := (section34_piercing_annuli hprep hpack e).1
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := id hpack
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hACp := hAB.trans (hCp (ends e).1).boundary_subset
  have hends (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).1
    have hzCp := hACp ((union_subset (hAa e).2.first_subset (hAa e).2.second_subset) hz)
    have heq := (hGcp (ends e).1).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  exact
    ((hCp (ends e).1).image (hGcp (ends e).1)).annulus_eq_of_same_essential_ends
      hann (image_mono hAB) (hPg e i hi).1 (hPg e j hj).1
      (hF.first_subset.trans hFA) (hF.second_subset.trans hFA)
      (hdisj e i hi j hj hij) (hends i hi) (hends j hj) hiA hjA hD hF hDA hFA

theorem exists_section34_annular_region_of_matching_band
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
    (hFA : F ⊆ G (ends e).1 '' Aa e) :
    let D := (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
    ∃ C : Set M₂, IsCompact C ∧ closure (interior C) = C ∧ IsConnected (interior C) ∧
      frontier C = D ∪ F ∧ C ⊆ Tp e ∧
      C ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ C = F ∧
      (C ⊆ G (ends e).1 '' Cp (ends e).1 ∨ C ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  obtain ⟨F', P, u, R, hF', hF'A, -, -, hu, -, hRfin, -, hfront, hreg,
    hint, -, hRP, hRT, hcontact, hsecond, -, hfirst, hside⟩ :=
    exists_section34_matched_annular_region hprep hpack e hi hj hij hiess hjess
      huD hφ hφP hDT hzero hone hempty
  have hFeq := section34_first_band_eq_of_same_essential_ends hprep hpack e hi hj hij
    hiess hjess hF' hF hF'A hFA
  rw [hFeq] at hfront hcontact hfirst hside
  let _ : Finite R.faces := hRfin.to_subtype
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have huR : IsPLHomeomorphInto 3 u R.space :=
    (hu.isPLOn.mono_of_isPolyhedron hRpoly hRP).isPLHomeomorphInto_model
      hRpoly.isCompact (hu.injOn.mono hRP)
  have hcompact := hRpoly.isCompact.image_of_continuousOn huR.continuousOn
  have hregular : closure (interior (u '' R.space)) = u '' R.space := by
    apply Subset.antisymm (closure_minimal interior_subset hcompact.isClosed)
    calc
      u '' R.space = u '' closure (interior R.space) := by rw [hreg]
      _ ⊆ closure (u '' interior R.space) :=
        ContinuousOn.image_closure (by rw [hreg]; exact huR.continuousOn)
      _ = closure (interior (u '' R.space)) := by rw [huR.image_interior]
  have hconnected := hint.image u (huR.continuousOn.mono interior_subset)
  rw [huR.image_interior] at hconnected
  refine ⟨u '' R.space, hcompact, hregular, hconnected, ?_, hRT, hcontact,
    hsecond, hfirst, hside⟩
  rw [← huR.image_frontier_of_isCompact hRpoly.isCompact]
  exact hfront

end DifferentialGeometry.Topology.PiecewiseLinear
