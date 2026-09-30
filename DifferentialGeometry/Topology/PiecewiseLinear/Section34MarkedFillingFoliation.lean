import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedMeridianDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LongitudeFoliation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProductFiberCarriers

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
theorem exists_section34_marked_filling_longitude_family
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
      (a : Fin 2 → (boundaryComplex 2 B).space)
      (γ : (boundaryComplex 2 B).space → ℝ → E × ℝ),
      IsCylindricalDiagram g' B.space R.space ∧
      (∀ z ∈ B.space, g' (z, 0) = g' (z, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g' '' (B.space ×ˢ {0})) ∧
      q '' stdSimplexBoundary 2 ⊆ frontier R.space ∧ Function.Injective a ∧
      (u ∘ g' ∘ γ (a 0)) '' Icc 0 1 = Pg e i ∧
      (u ∘ g' ∘ γ (a 1)) '' Icc 0 1 = Pg e j ∧
      Pairwise (fun x y => Disjoint (γ x '' Icc 0 1) (γ y '' Icc 0 1)) ∧
      (⋃ x, γ x '' Icc 0 1) = (boundaryComplex 2 B).space ×ˢ Icc (0 : ℝ) 1 ∧
      ∀ x, IsPLHomeomorphOn (γ x) (Icc 0 1) (γ x '' Icc 0 1) ∧
        γ x 0 = ((x : E), 0) ∧ γ x 1 = ((x : E), 1) ∧
        γ x '' Icc 0 1 ⊆ (boundaryComplex 2 B).space ×ˢ Icc (0 : ℝ) 1 ∧
        (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 B).space ×ˢ ({0} : Set ℝ)) =
          {((x : E), 0)} ∧
        (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 B).space ×ˢ ({1} : Set ℝ)) =
          {((x : E), 1)} := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨J, Q', f, p, g₀, q, hJ, hQ, hf, hp, hpinj, hPg₀, hPg₁,
      hg₀, he₀, hq, hqfront, -, hmark⟩ :=
    exists_section34_marked_filling_meridian_disk hprep hpack e hi hj hij hiess hjess
      hB R hR hu hRP hg hends hF hRT hfront
  have hC := hg.isCombinatorialSolidTorus hB (by simp)
  have hRS := hRT.trans
    ((section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset)
  have hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {p 0})) (Sp e) := by
    rw [← hPg₀]
    exact (section34_piercing_generators_of_essential_second hprep hpack e hi hiess).1
  have hlong (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ Q') :=
    hu.not_nullhomotopic_all_model_product_fibers hC hRP hJ hQ hf
      (section34_tubes_are_topological_solid_tori hprep hpack e).1 hRS (hp 0) hgen hz
  have hfrontR := frontier_space_eq_boundaryComplex_space_of_finrank (by simp) R hR
  have hfB : IsPLHomeomorphOn f (J ×ˢ Q') (boundaryComplex 3 R).space := hfrontR ▸ hf
  obtain ⟨g', hg', hends', hq', hseam, -⟩ :=
    hg₀.exists_rotation_with_prescribed_meridian B hB he₀ (by norm_num) hq rfl
  have hmark' : ∀ z ∈ Q', ∃ x ∈ J,
      (g' '' ((boundaryComplex 2 B).space ×ˢ ({0} : Set ℝ))) ∩
        (f '' (J ×ˢ {z})) = {f (x, z)} := by
    intro z hz
    obtain ⟨x, hx, heq, -⟩ := hmark z hz
    exact ⟨x, hx, hseam.symm ▸ heq⟩
  obtain ⟨π, γ, hπ, hdis, hcover, hγ⟩ :=
    hg'.exists_full_proper_longitude_family B R hB hR (by simp) hends' hfB
      (fun z hz => (hlong z hz).1) (fun z hz => (hlong z hz).2.2) hmark'
  choose a₀ ha₀ hπa using fun k => hπ.bijOn.surjOn (hp k)
  let a : Fin 2 → (boundaryComplex 2 B).space := fun k => ⟨a₀ k, ha₀ k⟩
  have hainj : Function.Injective a := by
    intro k l hkl
    apply hpinj
    have heq := congrArg (fun z : (boundaryComplex 2 B).space => π (z : E)) hkl
    exact (hπa k).symm.trans (heq.trans (hπa l))
  have himage (k : Fin 2) : (u ∘ g' ∘ γ (a k)) '' Icc 0 1 =
      (u ∘ f) '' (J ×ˢ {p k}) := by
    have hγk := (hγ (a k)).1.image_eq
    change γ (a k) '' Icc 0 1 =
      (B.space ×ˢ Icc (0 : ℝ) 1) ∩ g' ⁻¹' (f '' (J ×ˢ {π (a₀ k)})) at hγk
    rw [hπa k] at hγk
    have hLC : f '' (J ×ˢ {p k}) ⊆ R.space := (hlong (p k) (hp k)).2.1
    have hgL : g' '' ((B.space ×ˢ Icc (0 : ℝ) 1) ∩
        g' ⁻¹' (f '' (J ×ˢ {p k}))) = f '' (J ×ˢ {p k}) := by
      rw [image_inter_preimage, hg'.image_eq, inter_eq_right.mpr hLC]
    simp only [image_comp, hγk, hgL]
  refine ⟨g', q, a, γ, hg', hends', hq', hqfront, hainj,
    (himage 0).trans hPg₀.symm, (himage 1).trans hPg₁.symm, hdis, hcover, ?_⟩
  intro x
  exact ⟨(hγ x).1.image_eq.symm ▸ (hγ x).1, (hγ x).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
