import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexDiskStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.ConvexFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_stdSimplex_starComplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hcard : T.card = n + 3) {a : E} (ha : a ∈ T) :
    ∃ f : (Fin (n + 2) → ℝ) → E,
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) (starComplex (simplexBoundary T hT) a).space ∧
      f '' stdSimplexBoundary (n + 1) =
        (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
  obtain ⟨P, g, hP, hPcard, hg, -, hboundary, -⟩ :=
    exists_isPLHomeomorphOn_simplex_vertex_star_euclidean T hT hcard ha
  let L := (starComplex (simplexBoundary T hT) a).space
  let C := (simplexBoundary (T.erase a)
    (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
  have hCL : C ⊆ L := by
    rw [show L = (starComplex (simplexBoundary T hT) a).space from rfl,
      ← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
  obtain ⟨u, hu⟩ := isPLBall_convexHull_of_affineIndependent P hP hPcard
  refine ⟨Function.invFunOn g L ∘ u, hu.trans hg.symm, ?_⟩
  rw [image_comp, hu.image_stdSimplexBoundary, ← hboundary, image_image]
  have heq : EqOn (Function.invFunOn g L ∘ g) id C :=
    fun x hx => hg.bijOn.invOn_invFunOn.1 (hCL hx)
  exact heq.image_eq.trans (image_id _)

open Classical in
theorem exists_disk_in_simplexBoundary_of_isPLSphere_one
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3))) (hcard : T.card = 4)
    {J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsPLSphere 1 J)
    (hJB : J ⊆ (simplexBoundary T hT).space) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 3)), D ⊆ (simplexBoundary T hT).space ∧
      ∃ f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D ∧ f '' stdSimplexBoundary 2 = J := by
  let B := simplexBoundary T hT
  let _ : Finite B.faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hB : IsPLSphere 2 B.space := by
    rw [show B = simplexBoundary T hT from rfl, simplexBoundary_space T hT (by omega)]
    exact isPLSphere_biUnion_erase T hT hcard
  have hnot : ¬ B.space ⊆ J := by
    intro hBJ
    have hBJ' : B.space = J := Subset.antisymm hBJ hJB
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    have hface : T.erase a ∈ B.faces := erase_mem_simplexBoundary_faces hT (by omega) ha
    have hle := card_le_of_isPLSphere B (hBJ'.symm ▸ hJ) hface
    rw [Finset.card_erase_of_mem ha, hcard] at hle
    omega
  obtain ⟨p, hpB, hpJ⟩ := not_subset.mp hnot
  obtain ⟨D₀, hD₀, hD₀sub, -⟩ := hB.isCombinatorialManifold.exists_isPLBall_subset_of_mem_nhds
    hpB (hJ.isPolyhedron.isClosed.isOpen_compl.mem_nhds hpJ)
  have hfront : frontier (convexHull ℝ (T : Set _)) = B.space :=
    frontier_convexHull_eq_simplexBoundary hT (by simpa using hcard)
  obtain ⟨a, ha, h, hh, hC, hD₀image, -⟩ :=
    exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron T hT hcard hD₀
      (hD₀sub.trans inter_subset_left |>.trans hfront.symm.subset) isOpen_univ (subset_univ _)
  have hBimage : h '' B.space = B.space := by rw [← hfront, h.image_frontier, hC]
  have hBsymm : h.symm '' B.space = B.space := by
    rw [h.image_symm, ← hBimage, h.injective.preimage_image]
    exact hBimage.symm
  have hJ₁ : IsPLSphere 1 (h '' J) :=
    hJ.of_isPLHomeomorphOn (hh.restrict hJ.isPolyhedron (subset_univ _))
  have hJstar : h '' J ⊆ openStar B a := by
    rw [openStar, show B = simplexBoundary T hT from rfl,
      avoidingUnion_simplexBoundary_eq_convexHull_erase T hT (by omega) ha]
    rintro x ⟨y, hyJ, rfl⟩
    refine ⟨hBimage ▸ mem_image_of_mem h (hJB hyJ), ?_⟩
    intro hyF
    obtain ⟨z, hz, hzy⟩ := hD₀image.symm ▸ hyF
    have hzy' : z = y := h.injective hzy
    exact (hD₀sub hz).2 (hzy'.symm ▸ hyJ)
  obtain ⟨P, g, hP, hPcard, hg, -, -, hopen⟩ :=
    exists_isPLHomeomorphOn_simplex_vertex_star_euclidean T hT (n := 1) hcard ha
  let L := (starComplex B a).space
  let Q := convexHull ℝ (P : Set (EuclideanSpace ℝ (Fin 2)))
  have hopenL : openStar B a ⊆ L := by
    rw [show B = simplexBoundary T hT from rfl,
      openStar_simplexBoundary_eq_sdiff_boundary T hT (by omega) ha]
    exact sdiff_subset
  have hJ₁L : h '' J ⊆ L := hJstar.trans hopenL
  have hJ₂ : IsPLSphere 1 (g '' (h '' J)) :=
    hJ₁.of_isPLHomeomorphOn (hg.restrict hJ₁.isPolyhedron hJ₁L)
  have hJ₂Q : g '' (h '' J) ⊆ interior Q := by
    rw [← hopen]
    exact image_mono hJstar
  obtain ⟨A, hA, hAfr, -⟩ := isPLBall_of_isPLSphere_one hJ₂
  have hQ : IsPLBall 2 Q := isPLBall_convexHull_of_affineIndependent P hP hPcard
  have hAQ : A ⊆ Q := (subset_of_isCompact_of_frontier_subset_open_convex
    hA.isPolyhedron.isCompact isOpen_interior (convex_convexHull ℝ _).interior
    hQ.interior_nonempty (hAfr ▸ hJ₂Q)).trans interior_subset
  let g' := Function.invFunOn g L
  have hg' : IsPLHomeomorphOn g' A (g' '' A) := hg.symm.restrict hA.isPolyhedron hAQ
  have hA' : IsPLBall 2 (g' '' A) := hA.of_isPLHomeomorphOn hg'
  have hh' : IsPLHomeomorphOn h.symm (g' '' A) (h.symm '' (g' '' A)) :=
    hh.homeomorph_symm.restrict hA'.isPolyhedron (subset_univ _)
  have hg'J : g' '' (g '' (h '' J)) = h '' J := by
    rw [image_image]
    have heq : EqOn (g' ∘ g) id (h '' J) := fun x hx => hg.bijOn.invOn_invFunOn.1 (hJ₁L hx)
    exact heq.image_eq.trans (image_id _)
  have hDsub : h.symm '' (g' '' A) ⊆ B.space := by
    rw [← hBsymm]
    apply image_mono
    rintro x ⟨y, hy, rfl⟩
    exact space_mono_of_faces_subset (starComplex_faces_subset B a)
      (hg.symm.bijOn.mapsTo (hAQ hy))
  obtain ⟨u, hu⟩ := hA
  refine ⟨h.symm '' (g' '' A), hDsub, h.symm ∘ g' ∘ u, (hu.trans hg').trans hh', ?_⟩
  rw [image_comp, image_comp, hu.image_stdSimplexBoundary, hAfr, hg'J,
    h.image_symm, h.injective.preimage_image]

open Classical in
theorem exists_complementary_disk_in_simplexBoundary
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3))) (hcard : T.card = 4)
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hDB : D ⊆ (simplexBoundary T hT).space)
    {f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D) :
    ∃ D' : Set (EuclideanSpace ℝ (Fin 3)),
      D ∪ D' = (simplexBoundary T hT).space ∧ D ∩ D' = f '' stdSimplexBoundary 2 ∧
      ∃ g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D' ∧
          g '' stdSimplexBoundary 2 = f '' stdSimplexBoundary 2 := by
  let B := simplexBoundary T hT
  have hfront : frontier (convexHull ℝ (T : Set _)) = B.space :=
    frontier_convexHull_eq_simplexBoundary hT (by simpa using hcard)
  have hD : IsPLBall 2 D := ⟨f, hf⟩
  obtain ⟨a, ha, h, hh, hC, hDimage, -⟩ :=
    exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron T hT hcard hD
      (hDB.trans hfront.symm.subset) isOpen_univ (subset_univ _)
  let L := (starComplex B a).space
  let F := convexHull ℝ (T.erase a : Set (EuclideanSpace ℝ (Fin 3)))
  let J := (simplexBoundary (T.erase a)
    (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
  have hDF : h '' D = F := by simpa only [F, Finset.coe_erase] using hDimage
  have hBimage : h '' B.space = B.space := by rw [← hfront, h.image_frontier, hC]
  have hFcard : (T.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hcard]
  have hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  have hhD : IsPLHomeomorphOn h D F :=
    hDF ▸ hh.restrict hD.isPolyhedron (subset_univ _)
  have hJimage : h '' (f '' stdSimplexBoundary 2) = J := by
    rw [image_image]
    exact image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull hF hFcard (hf.trans hhD)
  obtain ⟨u, hu, huJ⟩ := exists_isPLHomeomorphOn_stdSimplex_starComplex T hT (n := 1) hcard ha
  have huJ' : u '' stdSimplexBoundary 2 = J := by
    convert huJ using 1
  have hL : IsPLBall 2 L := ⟨u, hu⟩
  have hhL := hh.homeomorph_symm.restrict hL.isPolyhedron (subset_univ _)
  have hLimage : h '' (h.symm '' L) = L := by
    rw [image_image]
    simp only [Homeomorph.apply_symm_apply, image_id']
  have hinter : F ∩ L = J := by
    rw [inter_comm, show L = (starComplex B a).space from rfl,
      show B = simplexBoundary T hT from rfl, ← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact simplexAvoiding_space_inter_convexHull_erase T hT a
  refine ⟨h.symm '' L, ?_, ?_, h.symm ∘ u, hu.trans hhL, ?_⟩
  · apply h.injective.image_injective
    rw [image_union, hDF, hLimage, hBimage]
    exact (union_comm F L).trans
      (simplexBoundary_space_eq_starComplex_union_opposite_face T hT (by omega) ha).symm
  · apply h.injective.image_injective
    rw [Set.image_inter h.injective, hDF, hLimage, hJimage]
    exact hinter
  · rw [image_comp, huJ', ← hJimage, h.image_symm, h.injective.preimage_image]

theorem exists_disk_decomposition_of_isPLSphere_one_subset_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S J : Set E} (hS : IsPLSphere 2 S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) :
    ∃ D₁ D₂ : Set E, D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = J ∧
      ∃ f₁ f₂ : (Fin 3 → ℝ) → E,
        IsPLHomeomorphOn f₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
        IsPLHomeomorphOn f₂ (stdSimplex ℝ (Fin 3)) D₂ ∧
        f₁ '' stdSimplexBoundary 2 = J ∧ f₂ '' stdSimplexBoundary 2 = J := by
  classical
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) (by simp) (0 : EuclideanSpace ℝ (Fin 3)) Filter.univ_mem
  let B := (simplexBoundary T hT).space
  have hB : IsPLSphere 2 B := by
    rw [show B = (simplexBoundary T hT).space from rfl, simplexBoundary_space T hT (by omega)]
    exact isPLSphere_biUnion_erase T hT hTcard
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hB
  let φ := v ∘ Function.invFunOn u (stdSimplexBoundary 3)
  have hφ : IsPLHomeomorphOn φ S B := hu.symm.trans hv
  let ψ := Function.invFunOn φ S
  have hψ : IsPLHomeomorphOn ψ B S := hφ.symm
  have hJφ : IsPLSphere 1 (φ '' J) :=
    hJ.of_isPLHomeomorphOn (hφ.restrict hJ.isPolyhedron hJS)
  have hJφB : φ '' J ⊆ B := image_subset_iff.mpr fun x hx => hφ.bijOn.mapsTo (hJS hx)
  obtain ⟨D₁, hD₁B, f₁, hf₁, hf₁J⟩ :=
    exists_disk_in_simplexBoundary_of_isPLSphere_one T hT hTcard hJφ hJφB
  obtain ⟨D₂, hunion, hinter, f₂, hf₂, hf₂J⟩ :=
    exists_complementary_disk_in_simplexBoundary T hT hTcard hD₁B hf₁
  have hD₂B : D₂ ⊆ B := by rw [show B = (simplexBoundary T hT).space from rfl, ← hunion]; exact subset_union_right
  have hD₁ : IsPLBall 2 D₁ := ⟨f₁, hf₁⟩
  have hD₂ : IsPLBall 2 D₂ := ⟨f₂, hf₂⟩
  have hψ₁ := hψ.restrict hD₁.isPolyhedron hD₁B
  have hψ₂ := hψ.restrict hD₂.isPolyhedron hD₂B
  have hJback : ψ '' (φ '' J) = J := by
    rw [image_image]
    have heq : EqOn (ψ ∘ φ) id J := fun x hx => hφ.bijOn.invOn_invFunOn.1 (hJS hx)
    exact heq.image_eq.trans (image_id _)
  refine ⟨ψ '' D₁, ψ '' D₂, ?_, ?_, ψ ∘ f₁, ψ ∘ f₂, hf₁.trans hψ₁, hf₂.trans hψ₂, ?_, ?_⟩
  · rw [← image_union, hunion]
    exact hψ.image_eq
  · rw [← hψ.bijOn.injOn.image_inter hD₁B hD₂B, hinter, hf₁J, hJback]
  · rw [image_comp, hf₁J, hJback]
  · rw [image_comp, hf₂J, hf₁J, hJback]

end DifferentialGeometry.Topology.PiecewiseLinear
