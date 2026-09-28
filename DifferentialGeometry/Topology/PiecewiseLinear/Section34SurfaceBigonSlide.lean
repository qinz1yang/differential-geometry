import DifferentialGeometry.Topology.PiecewiseLinear.CirclePair
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_crosscut_between_boundary_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} {a : (Fin 3 → ℝ) → E}
    (ha : IsPLHomeomorphOn a (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A) {x y : E}
    (hx : x ∈ a '' stdSimplexBoundary 2) (hy : y ∈ a '' stdSimplexBoundary 2)
    (hxy : x ≠ y) :
    ∃ (P : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) P ∧ P ⊆ A ∧
      γ 0 = x ∧ γ 1 = y ∧ P ∩ a '' stdSimplexBoundary 2 = {x, y} := by
  classical
  let S := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hS : IsPLBall 2 S := isPLBall_unit_square
  have hfront : frontier S =
      Icc (0 : ℝ) 1 ×ˢ {0, 1} ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 := by
    simp only [S, frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
  have h₀ : ((0 : ℝ), (0 : ℝ)) ∈ frontier S := by rw [hfront]; simp
  have h₁ : ((1 : ℝ), (1 : ℝ)) ∈ frontier S := by rw [hfront]; simp
  obtain ⟨s, hs⟩ := hS
  have hS : IsPLBall 2 S := ⟨s, hs⟩
  obtain ⟨T, hTfin, hTspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hsT : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) T.space := hTspace.symm ▸ hs
  have hsbd : s '' stdSimplexBoundary 2 = frontier S := by
    have h := frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) T
      (show IsPLBall 2 T.space from ⟨s, hsT⟩).isCombinatorialManifoldWithBoundary
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex T hsT,
      simplexBoundary_stdVertices_space, hTspace] at h
    exact h.symm
  obtain ⟨b, hb, hb₀, hb₁⟩ := exists_isPLHomeomorphOn_pair_of_isPLSphere_one
    (hsbd ▸ hs.isPLSphere_image_stdSimplexBoundary) ha.isPLSphere_image_stdSimplexBoundary
    h₀ h₁ (by simp) hx hy hxy
  obtain ⟨H, hH, hHb⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hs ha
    (hsbd.symm ▸ hb)
  rw [hsbd] at hHb
  let δ : ℝ → ℝ × ℝ := fun t => (t, t)
  have hδ : IsPLHomeomorphOn δ (Icc 0 1) (δ '' Icc 0 1) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    · exact isPiecewiseAffineOn_of_affine_of_isHPolytope
        ((AffineMap.id ℝ ℝ).prod (AffineMap.id ℝ ℝ)) isHPolytope_Icc
    · exact (show InjOn δ (Icc 0 1) from fun _ _ _ _ h => congrArg Prod.fst h).bijOn_image
  have hδS : δ '' Icc 0 1 ⊆ S := by rintro _ ⟨t, ht, rfl⟩; exact ⟨ht, ht⟩
  have hδbd : (δ '' Icc 0 1) ∩ frontier S = {((0 : ℝ), 0), (1, 1)} := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, htf⟩
      rw [hfront] at htf
      rcases htf with ⟨-, ht⟩ | ⟨ht, -⟩ <;>
        rcases ht with ht | ht <;> change t = _ at ht <;> simp [δ, ht]
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by norm_num, rfl⟩, h₀⟩
      · exact ⟨⟨1, by norm_num, rfl⟩, h₁⟩
  have hpoly := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ
  have hγ := hδ.trans (hH.restrict hpoly.isPolyhedron hδS)
  have hH₀ : H ((0 : ℝ), (0 : ℝ)) = x := (hHb h₀).trans hb₀
  have hH₁ : H ((1 : ℝ), (1 : ℝ)) = y := (hHb h₁).trans hb₁
  refine ⟨H '' (δ '' Icc 0 1), H ∘ δ, hγ, image_subset_iff.mpr
    (hH.bijOn.mapsTo.mono_left hδS), hH₀, hH₁, ?_⟩
  have hHbd : H '' frontier S = a '' stdSimplexBoundary 2 :=
    hHb.image_eq.trans hb.image_eq
  rw [← hHbd, ← hH.bijOn.injOn.image_inter hδS
    ((show IsPLBall 2 S from ⟨s, hs⟩).isPolyhedron.isClosed.frontier_subset),
    hδbd, image_pair, hH₀, hH₁]

theorem IsCombinatorialManifold.exists_crosscut_slide_of_side_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {N A J L : Set E}
    {n a : (Fin 3 → ℝ) → E} (hn : IsPLHomeomorphOn n (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N)
    (hNK : N ⊆ K.space) (hJK : J ⊆ K.space) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) (J ∩ N))
    (hends : (J ∩ N) ∩ n '' stdSimplexBoundary 2 = {γ 0, γ 1})
    (ha : IsPLHomeomorphOn a (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A) (hAN : A ⊆ N)
    (hside : A ∩ (L ∪ n '' stdSimplexBoundary 2) ⊆ a '' stdSimplexBoundary 2)
    (h₀ : γ 0 ∈ a '' stdSimplexBoundary 2) (h₁ : γ 1 ∈ a '' stdSimplexBoundary 2)
    (h₀L : γ 0 ∉ L) (h₁L : γ 1 ∉ L) :
    ∃ H : E → E, IsPLHomeomorphOn H K.space K.space ∧
      EqOn H id (closure (K.space \ N)) ∧ H '' N = N ∧
      H '' J ∩ L = (J \ N) ∩ L := by
  have hne : γ 0 ≠ γ 1 :=
    fun h => zero_ne_one (hγ.bijOn.injOn (by norm_num) (by norm_num) h)
  obtain ⟨P, δ, hδ, hPA, hδ₀, hδ₁, hPbd⟩ :=
    ha.exists_crosscut_between_boundary_points h₀ h₁ hne
  have hPN : P ⊆ N := hPA.trans hAN
  have h₀bd : γ 0 ∈ n '' stdSimplexBoundary 2 :=
    (hends.symm.subset (by simp)).2
  have h₁bd : γ 1 ∈ n '' stdSimplexBoundary 2 :=
    (hends.symm.subset (by simp)).2
  have hPends : P ∩ n '' stdSimplexBoundary 2 = {δ 0, δ 1} := by
    rw [hδ₀, hδ₁]
    apply Subset.antisymm
    · intro x hx
      exact hPbd.subset ⟨hx.1, hside ⟨hPA hx.1, Or.inr hx.2⟩⟩
    · rintro x (rfl | rfl)
      · exact ⟨(hPbd.symm.subset (by simp)).1, h₀bd⟩
      · exact ⟨(hPbd.symm.subset (by simp)).1, h₁bd⟩
  have hPL : Disjoint P L := by
    apply disjoint_left.mpr
    intro x hxP hxL
    rcases hPbd.subset ⟨hxP, hside ⟨hPA hxP, Or.inl hxL⟩⟩ with hx | hx
    · exact h₀L (hx ▸ hxL)
    · exact h₁L (hx ▸ hxL)
  have hN : IsPLBall 2 N := ⟨n, hn⟩
  obtain ⟨g, hg, hgfix, hgP⟩ := exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    hn rfl hn rfl hγ inter_subset_right hends hδ hPN hPends
    hn.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isPLHomeomorphOn_id
    hδ₀.symm hδ₁.symm
  let C := closure (K.space \ N)
  have hC : IsPolyhedron C := (isPolyhedron_space K).closure_sdiff hN.isPolyhedron
  have hCK : C ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hNC : N ∩ C = n '' stdSimplexBoundary 2 :=
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hn hNK
  have hcover : N ∪ C = K.space := by
    apply Subset.antisymm (union_subset hNK hCK)
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (subset_closure ⟨hx, hxN⟩)
  obtain ⟨H, hH, hHg, hHC⟩ := exists_isPLHomeomorphOn_union hN.isPolyhedron hC hg
    hC.isPLHomeomorphOn_id (fun _ hx => hgfix (hNC.subset hx))
    (fun x hx => ⟨x, hx, hgfix (hNC.subset hx)⟩)
  rw [hcover] at hH
  have hHN : H '' N = N := hHg.image_eq.trans hg.image_eq
  have hHP : H '' (J ∩ N) = P :=
    (hHg.mono inter_subset_right).image_eq.trans hgP
  refine ⟨H, hH, hHC, hHN, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
    by_cases hyN : y ∈ N
    · exact (disjoint_left.mp hPL (hHP.subset ⟨y, ⟨hy, hyN⟩, rfl⟩) hyL).elim
    · have hfix := hHC (subset_closure ⟨hJK hy, hyN⟩)
      rw [hfix] at hyL ⊢
      exact ⟨⟨hy, hyN⟩, hyL⟩
  · rintro ⟨⟨hxJ, hxN⟩, hxL⟩
    exact ⟨⟨x, hxJ, hHC (subset_closure ⟨hJK hxJ, hxN⟩)⟩, hxL⟩

end DifferentialGeometry.Topology.PiecewiseLinear
