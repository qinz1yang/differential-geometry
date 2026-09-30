import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianDiskNormalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianGraphClass
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedFillingCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_cylinder_with_marked_meridian
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite B.faces] [Finite R.faces] (hB : IsPLBall 2 B.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {g : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g B.space R.space)
    (hends : ∀ z ∈ B.space, g (z, 0) = g (z, 1))
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P J Q : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P)
    (hRP : R.space ⊆ P) (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) (frontier R.space)) (y : Q)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hRS : u '' R.space ⊆ S)
    (hgen : CarriesFundamentalGroupOnto
      ((u ∘ f) '' (J ×ˢ {(y : EuclideanSpace ℝ (Fin 3))})) S) :
    ∃ (g' : E × ℝ → EuclideanSpace ℝ (Fin 3))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsCylindricalDiagram g' B.space R.space ∧
      (∀ z ∈ B.space, g' (z, 0) = g' (z, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g' '' (B.space ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 ⊆ frontier R.space ∧
      g' '' (B.space ×ˢ {1 / 2}) ⊆ R.space ∧
      ∀ z ∈ Q, ∃ x ∈ J,
        (q '' stdSimplexBoundary 2) ∩ (f '' (J ×ˢ {z})) = {f (x, z)} ∧
        (u '' (q '' stdSimplexBoundary 2)) ∩ ((u ∘ f) '' (J ×ˢ {z})) = {u (f (x, z))} := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hC := hg.isCombinatorialSolidTorus hB (by simp)
  obtain ⟨x, hx⟩ := hJ.nonempty
  obtain ⟨r, -, hK, hKC, hKF, hnull, hess, hmark⟩ :=
    hu.exists_PL_meridian_inclusions_of_marked_boundary_product hC hRP hJ hQ hf
      ⟨x, hx⟩ y hS hRS hgen
  have hfront := frontier_space_eq_boundaryComplex_space_of_finrank
    (d := Classical.decEq _) (by simp) R hR
  have hKB : r '' Q ⊆ (boundaryComplex 3 R).space := by
    rw [← hfront]
    exact hKF
  have hnull' : (⟨inclusion (hKB.trans (boundaryComplex_space_subset 3 R)),
      continuous_inclusion _⟩ : C(r '' Q, R.space)).Nullhomotopic := hnull
  have hess' : ¬ (⟨inclusion hKB, continuous_inclusion hKB⟩ :
      C(r '' Q, (boundaryComplex 3 R).space)).Nullhomotopic := by
    intro hn
    apply hess
    let e : C((boundaryComplex 3 R).space, frontier R.space) :=
      Homeomorph.setCongr hfront.symm
    convert hn.comp_right e using 1
    apply ContinuousMap.ext
    intro z
    rfl
  obtain ⟨g', q, hg', hends', hq, hqK, hsub⟩ :=
    hg.exists_cylinder_with_meridian B R hB hR hends (by simp) hK hKB hnull' hess'
  refine ⟨g', q, hg', hends', hq, hqK.symm ▸ hKF, hsub, ?_⟩
  intro z hz
  obtain ⟨w, hw, hmeet⟩ := hmark z hz
  refine ⟨w, hw, hqK.symm ▸ hmeet, ?_⟩
  have hFP : f '' (J ×ˢ {z}) ⊆ P := by
    calc
      f '' (J ×ˢ {z}) ⊆ f '' (J ×ˢ Q) :=
        image_mono (prod_mono_right (singleton_subset_iff.mpr hz))
      _ = frontier R.space := hf.image_eq
      _ ⊆ P := hC.isPolyhedron.isClosed.frontier_subset.trans hRP
  rw [hqK, image_comp, ← hu.injOn.image_inter (hKC.trans hRP) hFP,
    hmeet, image_singleton]

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


theorem exists_section34_marked_filling_meridian_disk
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : Set E} (hV : IsPLBall 2 V)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) (hRP : R.space ⊆ P)
    {g : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hg : IsCylindricalDiagram g V R.space)
    (hends : ∀ z ∈ V, g (z, 0) = g (z, 1))
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hRT : u '' R.space ⊆ Tp e) (hfront : u '' frontier R.space = D ∪ F) :
    ∃ (J Q : Set (EuclideanSpace ℝ (Fin 3)))
      (f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : Fin 2 → EuclideanSpace ℝ (Fin 3))
      (g' : E × ℝ → EuclideanSpace ℝ (Fin 3))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier R.space) ∧
      (∀ k, p k ∈ Q) ∧ Function.Injective p ∧
      Pg e i = (u ∘ f) '' (J ×ˢ {p 0}) ∧ Pg e j = (u ∘ f) '' (J ×ˢ {p 1}) ∧
      IsCylindricalDiagram g' V R.space ∧
      (∀ z ∈ V, g' (z, 0) = g' (z, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g' '' (V ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 ⊆ frontier R.space ∧
      g' '' (V ×ˢ {1 / 2}) ⊆ R.space ∧
      ∀ z ∈ Q, ∃ x ∈ J,
        (q '' stdSimplexBoundary 2) ∩ (f '' (J ×ˢ {z})) = {f (x, z)} ∧
        (u '' (q '' stdSimplexBoundary 2)) ∩ ((u ∘ f) '' (J ×ˢ {z})) = {u (f (x, z))} := by
  classical
  have hC := hg.isCombinatorialSolidTorus hV (by simp)
  obtain ⟨J, Q', f, p, hJ, hQ, hf, hp, hinj, hPg₀, hPg₁⟩ :=
    exists_section34_marked_filling_boundary_coordinates hprep hpack e hi hj hij hiess hjess
      hF hu hC hRP hRT hfront
  have hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {p 0})) (Sp e) := by
    rw [← hPg₀]
    exact (section34_piercing_generators_of_essential_second hprep hpack e hi hiess).1
  have hRS := hRT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  obtain ⟨B, hBfin, hBspace⟩ := hV.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ hV
  have hgB : IsCylindricalDiagram g B.space R.space := hBspace.symm ▸ hg
  have hendsB : ∀ z ∈ B.space, g (z, 0) = g (z, 1) := hBspace.symm ▸ hends
  obtain ⟨g', q, hg', hends', hq, hqfront, hqsub, hmark⟩ :=
    hu.exists_cylinder_with_marked_meridian B R hB hR hgB hendsB hRP hJ hQ hf ⟨p 0, hp 0⟩
      (section34_tubes_are_topological_solid_tori hprep hpack e).1 hRS hgen
  rw [hBspace] at hg' hends' hq hqsub
  exact ⟨J, Q', f, p, g', q, hJ, hQ, hf, hp, hinj, hPg₀, hPg₁,
    hg', hends', hq, hqfront, hqsub, hmark⟩

end DifferentialGeometry.Topology.PiecewiseLinear
