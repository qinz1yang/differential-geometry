/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem exists_isPLBall_disjoint_of_isPLSphere_two
    {B J : Set E} (hB : IsPLSphere 2 B) (hJ : IsPLSphere 1 J) (hJB : J ⊆ B) :
    ∃ H : Set E, IsPLBall 2 H ∧ H ⊆ B ∧ Disjoint H J := by
  classical
  have hBJ : ¬ B ⊆ J := by
    intro h
    have hBJ' : B = J := Set.Subset.antisymm h hJB
    obtain ⟨K, hKfinite, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfinite.to_subtype
    have hKtwo : IsPLSphere 2 K.space := hKB.symm ▸ hB
    have hKone : IsPLSphere 1 K.space := hKB.symm ▸ hBJ' ▸ hJ
    have htwo := eulerChar_of_isPLSphere K hKtwo
    have hone := eulerChar_of_isPLSphere_one K hKone
    norm_num at htwo hone
    omega
  obtain ⟨x, hxB, hxJ⟩ := Set.not_subset.mp hBJ
  obtain ⟨K, hKfinite, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfinite.to_subtype
  have hKman : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (hKB.symm ▸ hB)
  obtain ⟨K₀, hK₀, hK₀finite, hxK₀⟩ := exists_isSubdivision_singleton_mem K (hKB.symm ▸ hxB)
  let _ : Finite K₀.faces := hK₀finite.to_subtype
  let U : Bool → Set E := fun b => if b then ({x} : Set E)ᶜ else Jᶜ
  have hU : ∀ b, IsOpen (((↑) : K₀.space → E) ⁻¹' U b) := by
    intro b
    cases b with
    | false =>
        exact hJ.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
    | true =>
        exact isOpen_compl_singleton.preimage continuous_subtype_val
  have hcover : K₀.space ⊆ ⋃ b, U b := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      exact mem_iUnion.mpr ⟨false, hxJ⟩
    · exact mem_iUnion.mpr ⟨true, hyx⟩
  obtain ⟨R, hR, hRfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K₀ U hU hcover
  let _ : Finite R.faces := hRfinite.to_subtype
  have hxR : ({x} : Finset E) ∈ R.faces := hR.singleton_mem hxK₀
  obtain ⟨b, hb⟩ := hstars {x} hxR
  have hstarU : closedStar R x ⊆ U b := by
    intro y hy
    exact hb (mem_iUnion₂.mpr ⟨x, Finset.mem_singleton_self x, hy⟩)
  have hbfalse : b = false := by
    cases b with
    | false => rfl
    | true =>
        exact (hstarU (mem_closedStar_self R hxR) (by simp)).elim
  have hstarJ : closedStar R x ⊆ Jᶜ := by
    rw [hbfalse] at hstarU
    change closedStar R x ⊆ Jᶜ at hstarU
    exact hstarU
  have hRman : IsCombinatorialManifold 2 R :=
    (hKman.of_isSubdivision hK₀).of_isSubdivision hR
  refine ⟨closedStar R x, hRman.isPLBall_closedStar hxR, ?_, ?_⟩
  · intro y hy
    have hyR := closedStar_subset_space R x hy
    rw [hR.space_eq, hK₀.space_eq, hKB] at hyR
    exact hyR
  · exact Set.disjoint_left.mpr fun y hyH hyJ => hstarJ hyH hyJ

open Classical in
private theorem closure_sdiff_closure_sdiff_eq_of_isPLBall
    {S D : Set E} (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ S) :
    closure (S \ closure (S \ D)) = D := by
  classical
  let R := closure (S \ D)
  have hcommon : D ∩ R = q '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hupper : closure (S \ R) ⊆ D := by
    apply closure_minimal
    · intro x hx
      by_contra hxD
      exact hx.2 (subset_closure ⟨hx.1, hxD⟩)
    · exact hD.isPolyhedron.isClosed
  have hopen : openSimplex (stdVertices 1) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    openSimplex_stdVertices_subset_stdSimplex
  have hopenclosure : closure (openSimplex (stdVertices 1)) = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    apply Set.Subset.antisymm
    · exact closure_minimal hopen (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).isClosed
    · rw [← convexHull_stdVertices]
      exact convexHull_subset_closure_openSimplex (by simp [stdVertices])
  have himageclosure : closure (q '' openSimplex (stdVertices 1)) = D := by
    have h := hq.image_closure (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)) hopen
    rw [hopenclosure, hq.image_eq] at h
    exact h.symm
  apply Set.Subset.antisymm hupper
  rw [← himageclosure]
  apply closure_mono
  rintro y ⟨x, hxopen, rfl⟩
  refine ⟨hDS (hq.bijOn.mapsTo (hopen hxopen)), ?_⟩
  intro hxR
  have hxcommon : q x ∈ D ∩ R := ⟨hq.bijOn.mapsTo (hopen hxopen), hxR⟩
  have hxboundary : q x ∈ q '' stdSimplexBoundary 2 := hcommon ▸ hxcommon
  obtain ⟨z, hzboundary, hzx⟩ := hxboundary
  have hxz : x = z := hq.bijOn.injOn (hopen hxopen) hzboundary.1 hzx.symm
  obtain ⟨i, hzi⟩ := hzboundary.2
  have hxi := (mem_openSimplex_stdVertices_iff 1).mp hxopen |>.1 i
  exact (ne_of_gt hxi) (hxz ▸ hzi)

open Classical in
private theorem image_stdSimplexBoundary_eq_frontier
    {D : Set (EuclideanSpace ℝ (Fin 2))} {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 2)}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) :
    q '' stdSimplexBoundary 2 = frontier D := by
  classical
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  obtain ⟨K, hKfinite, hKD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfinite.to_subtype
  have hqK : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space := hKD ▸ hq
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hqK
  rw [simplexBoundary_stdVertices_space] at hboundary
  have hKball : IsPLBall 2 K.space := hKD ▸ hD
  have hfrontier := boundaryComplex_space_eq_of_isPLBall_of_frontier K hKball
    hKball.isPLSphere_frontier rfl
  calc
    q '' stdSimplexBoundary 2 = (boundaryComplex 2 K).space := hboundary.symm
    _ = frontier K.space := hfrontier
    _ = frontier D := congrArg frontier hKD

private theorem inside_subset_inside_of_subset_inside
    {C J : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : Schoenflies.IsSeparating C) (hJ : Schoenflies.IsSeparating J)
    (hJC : J ⊆ Schoenflies.inside C) :
    Schoenflies.inside J ⊆ Schoenflies.inside C := by
  have hCJ : Disjoint C J := Set.disjoint_left.mpr fun _ hzC hzJ =>
    Schoenflies.inside_subset_compl (hJC hzJ) hzC
  have hdis : Disjoint (Schoenflies.outside C) J :=
    Schoenflies.disjoint_inside_outside.symm.mono_right hJC
  obtain ⟨W, V, hWV, hout⟩ := hJ.exists_isRegionPair_subset
    hC.isConnected_outside.isPreconnected hC.isConnected_outside.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hC.not_isBounded_outside (hJ.isBounded_inside.subset hout)).elim
  · have hCout : C ⊆ Schoenflies.outside J := by
      intro z hz
      exact hC.absorption hJ (Or.inr rfl) (Or.inr rfl) hout
        ⟨hz, Set.disjoint_left.mp hCJ hz⟩
    intro z hz
    have hzC : z ∉ C := fun h =>
      Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hCout h)
    have hzcover : z ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
      rwa [Schoenflies.inside_union_outside]
    exact hzcover.resolve_right fun h =>
      Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hout h)

open Classical in
theorem exists_isPLBall_pair_of_isPLSphere_two
    {B J : Set E} (hB : IsPLSphere 2 B) (hJ : IsPLSphere 1 J) (hJB : J ⊆ B) :
    ∃ (D₀ D₁ : Set E) (q₀ q₁ : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      q₀ '' stdSimplexBoundary 2 = J ∧ q₁ '' stdSimplexBoundary 2 = J ∧
      D₀ ∪ D₁ = B ∧ D₀ ∩ D₁ = J := by
  classical
  obtain ⟨H, hH, hHB, hHJ⟩ := exists_isPLBall_disjoint_of_isPLSphere_two hB hJ hJB
  have hHball := hH
  obtain ⟨qH, hqH⟩ := hH
  let R := closure (B \ H)
  have hR : IsPLBall 2 R := hB.isPLBall_closure_sdiff hHball hHB
  have hRB : R ⊆ B := closure_minimal sdiff_subset hB.isPolyhedron.isClosed
  obtain ⟨qR, hqR⟩ := hR
  have hHR : closure (B \ R) = H :=
    closure_sdiff_closure_sdiff_eq_of_isPLBall hB hqH hHB
  have hRboundary : R ∩ H = qR '' stdSimplexBoundary 2 := by
    have h := hB.inter_closure_sdiff_eq_image_stdSimplexBoundary hqR hRB
    rwa [hHR] at h
  have hJboundary : Disjoint J (qR '' stdSimplexBoundary 2) := by
    rw [← hRboundary]
    exact hHJ.symm.mono_right inter_subset_right
  let C := polygonalCircleOfAffineIndependentTriple standardTrianglePosition
    standardTrianglePosition_affineIndependent
  let P : Set (EuclideanSpace ℝ (Fin 2)) := closure (Schoenflies.inside C.carrier)
  have hC : IsPLSphere 1 C.carrier := isPLSphere_one_carrier C
  have hCjordan := isJordanCurve_of_isPLSphere_one hC
  have hCsep := Schoenflies.jordan_curve_theorem hCjordan
  have hP : IsPLBall 2 P := isPLBall_closure_inside_of_isPLSphere_one hC
  have hfrontierP : frontier P = C.carrier :=
    frontier_closure_inside_of_isPLSphere_one hC
  have hinteriorP : interior P = Schoenflies.inside C.carrier := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxP : x ∈ P := interior_subset hx
      have hxunion : x ∈ Schoenflies.inside C.carrier ∪ C.carrier := by
        simpa [P, closure_eq_self_union_frontier, hCsep.frontier_inside] using hxP
      exact hxunion.resolve_right fun hxC =>
        Set.disjoint_left.mp disjoint_interior_frontier hx (hfrontierP.symm ▸ hxC)
    · exact interior_maximal subset_closure hCsep.isOpen_inside
  obtain ⟨qP, hqP⟩ := hP
  let f : E → EuclideanSpace ℝ (Fin 2) :=
    qP ∘ Function.invFunOn qR (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hf : IsPLHomeomorphOn f R P := hqR.symm.trans hqP
  let J' := f '' J
  have hJR : J ⊆ R := by
    intro x hxJ
    exact subset_closure ⟨hJB hxJ, fun hxH => Set.disjoint_left.mp hHJ hxH hxJ⟩
  have hJ' : IsPLSphere 1 J' := hJ.of_isPLHomeomorphOn (hf.restrict hJ.isPolyhedron hJR)
  have hfboundary : f '' (qR '' stdSimplexBoundary 2) = frontier P := by
    calc
      f '' (qR '' stdSimplexBoundary 2) = qP '' stdSimplexBoundary 2 := by
        ext y
        constructor
        · rintro ⟨-, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨x, hx, ?_⟩
          simp only [f, Function.comp_apply]
          rw [hqR.bijOn.invOn_invFunOn.1 hx.1]
        · rintro ⟨x, hx, rfl⟩
          refine ⟨qR x, ⟨x, hx, rfl⟩, ?_⟩
          simp only [f, Function.comp_apply]
          rw [hqR.bijOn.invOn_invFunOn.1 hx.1]
      _ = frontier P := image_stdSimplexBoundary_eq_frontier hqP
  have hJ'frontier : Disjoint J' (frontier P) := by
    rw [← hfboundary]
    apply hJboundary.image hf.bijOn.injOn hJR
    rintro y ⟨x, hx, rfl⟩
    exact hqR.bijOn.mapsTo hx.1
  have hJ'interior : J' ⊆ interior P := by
    rintro y ⟨x, hxJ, rfl⟩
    apply (mem_interior_iff_notMem_frontier (hf.bijOn.mapsTo (hJR hxJ))).mpr
    exact fun hyfrontier =>
      Set.disjoint_left.mp hJ'frontier ⟨x, hxJ, rfl⟩ hyfrontier
  have hinside : Schoenflies.inside J' ⊆ Schoenflies.inside C.carrier :=
    inside_subset_inside_of_subset_inside hCsep
      (Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ'))
      (hinteriorP ▸ hJ'interior)
  let D' := closure (Schoenflies.inside J')
  have hD' : IsPLBall 2 D' := isPLBall_closure_inside_of_isPLSphere_one hJ'
  have hD'ball := hD'
  have hD'P : D' ⊆ P := by
    simpa [D', P] using closure_mono hinside
  obtain ⟨q', hq'⟩ := hD'
  have hq'boundary : q' '' stdSimplexBoundary 2 = J' := by
    rw [image_stdSimplexBoundary_eq_frontier hq']
    exact frontier_closure_inside_of_isPLSphere_one hJ'
  let g := Function.invFunOn f R
  let D₀ := g '' D'
  have hg : IsPLHomeomorphOn g D' D₀ := by
    simpa [g, D₀] using hf.symm.restrict hD'ball.isPolyhedron hD'P
  let q₀ := g ∘ q'
  have hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ := hq'.trans hg
  have hginv : g '' J' = J := by
    change Function.invFunOn f R '' (f '' J) = J
    rw [image_image]
    have hinv : EqOn (Function.invFunOn f R ∘ f) id J := fun x hx =>
      hf.bijOn.invOn_invFunOn.1 (hJR hx)
    exact hinv.image_eq.trans (image_id J)
  have hq₀boundary : q₀ '' stdSimplexBoundary 2 = J := by
    change (g ∘ q') '' stdSimplexBoundary 2 = J
    rw [image_comp, hq'boundary, hginv]
  have hD₀B : D₀ ⊆ B := by
    rintro y ⟨x, hxD', rfl⟩
    exact hRB (hf.symm.bijOn.mapsTo (hD'P hxD'))
  let D₁ := closure (B \ D₀)
  have hD₁ : IsPLBall 2 D₁ := hB.isPLBall_closure_sdiff ⟨q₀, hq₀⟩ hD₀B
  have hD₁B : D₁ ⊆ B := closure_minimal sdiff_subset hB.isPolyhedron.isClosed
  obtain ⟨q₁, hq₁⟩ := hD₁
  have hintersection : D₀ ∩ D₁ = J := by
    change D₀ ∩ closure (B \ D₀) = J
    rw [hB.inter_closure_sdiff_eq_image_stdSimplexBoundary hq₀ hD₀B, hq₀boundary]
  have hD₀back : closure (B \ D₁) = D₀ :=
    closure_sdiff_closure_sdiff_eq_of_isPLBall hB hq₀ hD₀B
  have hq₁boundary : q₁ '' stdSimplexBoundary 2 = J := by
    have h := hB.inter_closure_sdiff_eq_image_stdSimplexBoundary hq₁ hD₁B
    rw [hD₀back] at h
    calc
      q₁ '' stdSimplexBoundary 2 = D₁ ∩ D₀ := h.symm
      _ = D₀ ∩ D₁ := inter_comm D₁ D₀
      _ = J := hintersection
  have hunion : D₀ ∪ D₁ = B := by
    apply Set.Subset.antisymm (union_subset hD₀B hD₁B)
    intro x hxB
    by_cases hxD₀ : x ∈ D₀
    · exact Or.inl hxD₀
    · exact Or.inr (subset_closure ⟨hxB, hxD₀⟩)
  exact ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hq₀boundary, hq₁boundary,
    hunion, hintersection⟩

open Classical in
theorem IsPLSphere.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
    {S D J : Set E} (hS : IsPLSphere 2 S) (hD : IsPreconnected D)
    (hDS : D ⊆ S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) (hDJ : Disjoint D J) :
    ∃ (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ Q ⊆ S ∧
      Disjoint D Q ∧ q '' stdSimplexBoundary 2 = J := by
  obtain ⟨Q₀, Q₁, q₀, q₁, hq₀, hq₁, hq₀boundary, hq₁boundary, hcover, hinter⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two hS hJ hJS
  have hQ₀closed : IsClosed Q₀ := (show IsPLBall 2 Q₀ from ⟨q₀, hq₀⟩).isPolyhedron.isClosed
  have hQ₁closed : IsClosed Q₁ := (show IsPLBall 2 Q₁ from ⟨q₁, hq₁⟩).isPolyhedron.isClosed
  have hside : D ⊆ Q₀ ∨ D ⊆ Q₁ := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp hD
      Q₀ Q₁ hQ₀closed hQ₁closed (hDS.trans hcover.symm.subset)
    rw [hinter, hDJ.inter_eq]
  rcases hside with hDQ₀ | hDQ₁
  · refine ⟨Q₁, q₁, hq₁, subset_union_right.trans hcover.subset, ?_, hq₁boundary⟩
    apply disjoint_left.mpr
    intro x hxD hxQ₁
    exact disjoint_left.mp hDJ hxD (hinter.subset ⟨hDQ₀ hxD, hxQ₁⟩)
  · refine ⟨Q₀, q₀, hq₀, subset_union_left.trans hcover.subset, ?_, hq₀boundary⟩
    apply disjoint_left.mpr
    intro x hxD hxQ₀
    exact disjoint_left.mp hDJ hxD (hinter.subset ⟨hxQ₀, hDQ₁ hxD⟩)

open Classical in
theorem IsPLBall.exists_disjoint_isPLBall_with_boundary_of_isPLSphere_two
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S D J : Set G} (hD : IsPLBall 2 D) (hS : IsPLSphere 2 S)
    (hDS : D ⊆ S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) (hDJ : Disjoint D J) :
    ∃ (Q : Set G) (q : (Fin 3 → ℝ) → G),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ Q ⊆ S ∧
      Disjoint D Q ∧ q '' stdSimplexBoundary 2 = J := by
  exact hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
    hD.isConnected.isPreconnected hDS hJ hJS hDJ

end DifferentialGeometry.Topology.PiecewiseLinear
