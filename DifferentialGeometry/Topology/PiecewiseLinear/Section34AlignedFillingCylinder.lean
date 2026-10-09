import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedFillingFoliation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FullLongitudeStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalReparametrization

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

open Classical in
theorem exists_section34_aligned_filling_cylinder
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite B.faces] [Finite R.faces] (hB : IsPLBall 2 B.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hRP : R.space ⊆ P)
    {g : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g B.space R.space)
    (hends : ∀ z ∈ B.space, g (z, 0) = g (z, 1))
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hRT : u '' R.space ⊆ Tp e) (hfront : u '' frontier R.space = D ∪ F) :
    ∃ (g' : E × ℝ → EuclideanSpace ℝ (Fin 3))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (a : Fin 2 → (boundaryComplex 2 B).space),
      IsCylindricalDiagram g' B.space R.space ∧
      (∀ z ∈ B.space, g' (z, 0) = g' (z, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g' '' (B.space ×ˢ {0})) ∧
      q '' stdSimplexBoundary 2 ⊆ frontier R.space ∧ Function.Injective a ∧
      (u ∘ g') '' ({(a 0 : E)} ×ˢ Icc (0 : ℝ) 1) = Pg e i ∧
      (u ∘ g') '' ({(a 1 : E)} ×ˢ Icc (0 : ℝ) 1) = Pg e j := by
  obtain ⟨g₀, q, a, γ, hg₀, hends₀, hq, hqfront, hinj, hPg₀, hPg₁,
    hdis, hcover, hγ⟩ :=
    exists_section34_marked_filling_longitude_family hprep hpack e hi hj hij hiess hjess
      B R hB hR hu hRP hg hends hF hRT hfront
  have hxy : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj h)
  obtain ⟨Φ, hΦ, hfix, hmap⟩ :=
    exists_prism_straightening_of_full_arc_family B hB hdis hcover hγ hxy
  obtain ⟨hg', hends', hcap⟩ := hg₀.precomp_fixed_caps_with_ends hends₀ hΦ hfix
  have himage (k : Fin 2) : (u ∘ (g₀ ∘ Φ)) '' ({(a k : E)} ×ˢ Icc (0 : ℝ) 1) =
      (u ∘ g₀ ∘ γ (a k)) '' Icc 0 1 := by
    rw [singleton_prod, image_image]
    apply image_congr
    intro t ht
    apply congrArg (u ∘ g₀)
    fin_cases k
    · exact (hmap t ht).1
    · exact (hmap t ht).2
  exact ⟨g₀ ∘ Φ, q, a, hg', hends', hcap.symm ▸ hq, hqfront, hinj,
    (himage 0).trans hPg₀, (himage 1).trans hPg₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
