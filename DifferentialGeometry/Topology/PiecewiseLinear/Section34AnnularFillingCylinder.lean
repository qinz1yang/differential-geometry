import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingInTubeModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.Homogeneity

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


theorem exists_section34_empty_annular_filling_cylinder
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
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCombinatorialSolidTorus R.space ∧
      IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)) ∧
      frontier R.space = g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ Tp e ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F ∧
      G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      (u '' R.space ⊆ G (ends e).1 '' Cp (ends e).1 ∨
        u '' R.space ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  obtain ⟨P, u, S, R, f, hP, hu, hcell, hSfin, hS, hSP, -, hf, hends,
    hRfin, hR, hRS, hT, hgen, hfront, hRT, hfirst, hsecond, hcontact, hside⟩ :=
    exists_section34_empty_annular_filling_in_tube_model hprep hpack e hi hj hij hiess hjess
      huD hφ hφP hDT hzero hone hempty hF hFA hFempty
  let _ : Finite S.faces := hSfin.to_subtype
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨B, hBfin, hBspace⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_stdSimplex 2
  have hfB : IsCylindricalDiagram f B.space S.space := hBspace.symm ▸ hf
  have hendsB : ∀ x ∈ B.space, f (x, 0) = f (x, 1) := hBspace.symm ▸ hends
  obtain ⟨-, g, hg, hgend, hgfront⟩ :=
    hfB.exists_cylindrical_model_of_interior_torus_carrier B S R hB hS hendsB hR hRS hT hgen
      isPLBall_unit_square (by simp [Module.finrank_prod])
  exact ⟨P, u, R, g, hP, hu, hcell, hRfin, hR, hRS.trans (interior_subset.trans hSP),
    hg.isCombinatorialSolidTorus isPLBall_unit_square (by simp), hg, hgend, hgfront,
    hfront, hRT, hfirst, hsecond, hcontact, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
