/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SphereNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary_map
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M BdM B : Set E} (ι : X → E)
    (hB : IsPLSphere 2 B) (hBBdM : B ⊆ BdM) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N)
    (hpush : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ →
        Δ ⊆ BdM →
        ∃ D₁ : SingularTwoCell X,
          D₁.IsNonsingular ∧
          ι '' (D₁ '' D₁.domain) ⊆ M ∧
          Set.range (fun x => ι (D₁.boundary x)) = r '' stdSimplexBoundary 2 ∧
          ι '' (D₁ '' D₁.domain) ∩ BdM = r '' stdSimplexBoundary 2) :
    ∃ (D₁ : SingularTwoCell X)
        (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
      D₁.IsNonsingular ∧
      ι '' (D₁ '' D₁.domain) ⊆ M ∧
      Set.range (fun x => ι (D₁.boundary x)) =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ι '' (D₁ '' D₁.domain) ∩ BdM =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ¬loopClassMeets L₁ P₀ N := by
  have hNne : N ≠ ⊤ := by
    intro hN
    apply hL
    apply (loopClassMeets_iff_carrier_subset L P₀ N).2
    intro g hg
    rw [hN]
    exact Subgroup.mem_top g
  have hi : ∃ i, ¬loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N := by
    by_contra hi
    have hall : ∀ i,
        loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N := by
      intro i
      by_contra hmeet
      exact hi ⟨i, hmeet⟩
    exact hNne (eq_top_of_boundaryLoops_mem_normal hB D q hq hDB hdisj P₀ N hall)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨D₁, hD₁, hD₁M, hD₁boundary, hD₁intersection⟩ :=
    hpush (D i) (q i) (hq i) ((hDB i).trans hBBdM)
  let L₁ := sphereBoundaryLoop q hB hq hDB hdisj i
  have hL₁range : Set.range (fun θ => (L₁ θ : E)) =
      q i '' stdSimplexBoundary 2 :=
    sphereBoundaryLoop_range q hB hq hDB hdisj i
  refine ⟨D₁, L₁, hD₁, hD₁M, ?_, ?_, hi⟩
  · exact hD₁boundary.trans hL₁range.symm
  · exact hD₁intersection.trans hL₁range.symm

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary_double
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {B : Set E} (hB : IsPLSphere 2 B)
    (hBBdM : B ⊆ (boundaryComplex 3 K).space) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N) :
    let _ := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K (n := 1) hK)
    (∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ →
        Δ ⊆ (boundaryComplex 3 K).space →
        ∃ D₁ : SingularTwoCell (double 3 K).space,
          D₁.IsNonsingular ∧
          (fun z : (double 3 K).space => glueSnd E E z) '' (D₁ '' D₁.domain) ⊆ K.space ∧
          Set.range (fun x => glueSnd E E (D₁.boundary x)) =
            r '' stdSimplexBoundary 2 ∧
          (fun z : (double 3 K).space => glueSnd E E z) '' (D₁ '' D₁.domain) ∩
              (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2) →
      ∃ (D₁ : SingularTwoCell (double 3 K).space)
          (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
        D₁.IsNonsingular ∧
        (fun z : (double 3 K).space => glueSnd E E z) '' (D₁ '' D₁.domain) ⊆ K.space ∧
        Set.range (fun x => glueSnd E E (D₁.boundary x)) =
          Set.range (fun θ => (L₁ θ : E)) ∧
        (fun z : (double 3 K).space => glueSnd E E z) '' (D₁ '' D₁.domain) ∩
            (boundaryComplex 3 K).space = Set.range (fun θ => (L₁ θ : E)) ∧
        ¬loopClassMeets L₁ P₀ N := by
  dsimp only
  intro hpush
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K (n := 1) hK)
  exact exists_nonsingular_two_cell_of_sphere_boundary_map
    (M := K.space) (BdM := (boundaryComplex 3 K).space)
    (X := (double 3 K).space)
    (fun z : (double 3 K).space => glueSnd E E z)
    hB hBBdM D q hq hDB hdisj P₀ N L hL hpush

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E)
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.space]
    {B : Set E} (hB : IsPLSphere 2 B)
    (hBBdM : B ⊆ (boundaryComplex 3 K).space) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N)
    (hpush : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ →
        Δ ⊆ (boundaryComplex 3 K).space →
        ∃ D₁ : SingularTwoCell K.space,
          D₁.IsNonsingular ∧
          Subtype.val '' (D₁ '' D₁.domain) ⊆ K.space ∧
          Set.range (fun x => (D₁.boundary x : E)) = r '' stdSimplexBoundary 2 ∧
          Subtype.val '' (D₁ '' D₁.domain) ∩ (boundaryComplex 3 K).space =
            r '' stdSimplexBoundary 2) :
    ∃ (D₁ : SingularTwoCell K.space)
        (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
      D₁.IsNonsingular ∧
      Subtype.val '' (D₁ '' D₁.domain) ⊆ K.space ∧
      Set.range (fun x => (D₁.boundary x : E)) =
        Set.range (fun θ => (L₁ θ : E)) ∧
      Subtype.val '' (D₁ '' D₁.domain) ∩ (boundaryComplex 3 K).space =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ¬loopClassMeets L₁ P₀ N :=
  exists_nonsingular_two_cell_of_sphere_boundary_map
    (M := K.space) (BdM := (boundaryComplex 3 K).space)
    (ι := (Subtype.val : K.space → E)) hB hBBdM D q hq hDB hdisj P₀ N L hL hpush

open Classical in
theorem exists_isPLHomeomorphOn_boundaryLoop_of_sphere_disks
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {B V : Set E} (hB : IsPLSphere 2 B)
    (hBBdM : B ⊆ (boundaryComplex 3 K).space) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) (hdisj : Pairwise (Function.onFun Disjoint D))
    (hV : V = sphereWithDiskInteriorsRemoved B D) [PathConnectedSpace V]
    (P₀ : V) (N : Subgroup (FundamentalGroup V P₀)) [N.Normal] (hN : N ≠ ⊤) :
    ∃ (g : (Fin 3 → ℝ) → E) (γ : freeLoop V),
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧
      MapsTo g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space ∧
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ g ⁻¹' (boundaryComplex 3 K).space = stdSimplexBoundary 2 ∧
      g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2 ∧
      range (fun θ => (γ θ : E)) = g '' stdSimplexBoundary 2 ∧ ¬loopClassMeets γ P₀ N := by
  subst V
  have hi : ∃ i, ¬loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N := by
    by_contra hnot
    apply hN
    apply eq_top_of_boundaryLoops_mem_normal hB D q hq hDB hdisj P₀ N
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hi
  have hboundary : IsPolyhedron (stdSimplexBoundary 2) := by
    have h := (isPLSphere_simplexBoundary_std 1).isPolyhedron
    rwa [simplexBoundary_stdVertices_space] at h
  have hmap : MapsTo (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space :=
    (hq i).bijOn.mapsTo.mono_right
      ((hDB i).trans (hBBdM.trans (boundaryComplex_space_subset 3 K)))
  have hbdmap : MapsTo (q i) (stdSimplexBoundary 2) (boundaryComplex 3 K).space :=
    fun _ hx => hBBdM (hDB i ((hq i).bijOn.mapsTo hx.1))
  obtain ⟨g, hg, hgmap, hfix, hpre, htrace⟩ :=
    hK.exists_isPLHomeomorphOn_eqOn_preimage_boundary K (isPLBall_stdSimplex 2).isPolyhedron
      hboundary (fun _ hx => hx.1) (hq i).isPiecewiseAffineOn (hq i).bijOn.injOn hmap hbdmap
  refine ⟨g, sphereBoundaryLoop q hB hq hDB hdisj i, hg, hgmap, hpre,
    htrace.trans hfix.image_eq.symm, ?_, hi⟩
  exact (sphereBoundaryLoop_range q hB hq hDB hdisj i).trans hfix.image_eq.symm

namespace NormalSystem

open Classical in
theorem exists_isPLHomeomorphOn_boundaryLoop_of_isPLSphere_boundaryComponent
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) :
    ∃ (g : (Fin 3 → ℝ) → E) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (r : Path S.basepoint (γ 0)),
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧
      MapsTo g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S.manifoldComplex.space ∧
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ g ⁻¹' S.boundaryComplex.space = stdSimplexBoundary 2 ∧
      g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ S.boundaryComplex.space = g '' stdSimplexBoundary 2 ∧
      range (fun θ => (γ θ : E)) = g '' stdSimplexBoundary 2 ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ r) S.normalSubgroup := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  let _ : S.normalSubgroup.Normal := S.normal
  obtain ⟨k, D, q, hq, hDB, hdisj, heq, -, -⟩ :=
    S.exists_sphereWithDiskInteriorsRemoved_eq_boundaryNeighborhood hB
  have hN : S.normalSubgroup ≠ ⊤ := by
    intro heqN
    apply S.loopClass_avoids_normal
    apply (conjugacyClassMeets_iff_carrier_subset _ S.normalSubgroup).mpr
    rw [heqN]
    exact subset_univ _
  have hBBdM : S.boundaryComponent ⊆ S.boundaryComplex.space :=
    connectedComponentIn_subset _ _
  obtain ⟨g, γ, hg, hgmap, hpre, htrace, hrange, havoid⟩ :=
    exists_isPLHomeomorphOn_boundaryLoop_of_sphere_disks
      (V := S.boundaryNeighborhoodSpace) S.manifoldComplex S.isManifold
      hB hBBdM D q hq hDB hdisj heq.symm S.basepoint S.normalSubgroup hN
  let r : Path S.basepoint (γ 0) := PathConnectedSpace.somePath _ _
  refine ⟨g, γ, r, hg, hgmap, hpre, htrace, hrange, ?_⟩
  have hclass := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong r ⟨γ, rfl⟩
  change ¬conjugacyClassMeets (FreeLoop.conjugacyClass γ S.basepoint) S.normalSubgroup at havoid
  rwa [hclass] at havoid

open Classical in
theorem nonempty_embeddedDisk_of_isPLSphere_boundaryComponent
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) : Nonempty (EmbeddedDisk S) := by
  obtain ⟨g, γ, r, hg, hgmap, -, htrace, hrange, havoid⟩ :=
    S.exists_isPLHomeomorphOn_boundaryLoop_of_isPLSphere_boundaryComponent hB
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  let P := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))
  have hP : IsPLBall 2 P := isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨p, hp⟩ := hP
  let f := g ∘ Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hf : IsPLHomeomorphOn f P (g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hp.symm.trans hg
  have hfront : p '' stdSimplexBoundary 2 = frontier P :=
    hp.image_stdSimplexBoundary_eq_frontier
  have hboundary : f '' frontier P = g '' stdSimplexBoundary 2 := by
    rw [← hfront, image_image]
    apply EqOn.image_eq
    intro x hx
    exact congrArg g (hp.bijOn.invOn_invFunOn.1 hx.1)
  have hPL : IsPLHomeomorphOn f P (f '' P) := hf.image_eq.symm ▸ hf
  have hinter : f '' P ∩ S.boundaryComplex.space = f '' frontier P := by
    rw [hf.image_eq, hboundary]
    exact htrace
  have hfrontP : frontier P ⊆ P :=
    (show IsPLBall 2 P from ⟨p, hp⟩).isPolyhedron.isClosed.frontier_subset
  have hpre : P ∩ f ⁻¹' S.boundaryComplex.space = frontier P := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hfx⟩
      obtain ⟨y, hy, hfy⟩ := hinter.subset ⟨mem_image_of_mem f hxP, hfx⟩
      exact (hf.bijOn.injOn (hfrontP hy) hxP hfy) ▸ hy
    · intro x hx
      exact ⟨hfrontP hx, (hinter.symm.subset (mem_image_of_mem f hx)).2⟩
  exact ⟨
    { domain := P
      isPLBall_domain := ⟨p, hp⟩
      map := f
      isPLHomeomorphOn := hPL
      mapsTo := hgmap.comp hp.symm.bijOn.mapsTo
      boundaryLoop := γ
      boundary_range := hrange.trans hboundary.symm
      boundary_preimage := hpre
      connector := r
      loopClass_avoids_normal := havoid }⟩

open Classical in
theorem exists_isPLHomeomorphOn_boundaryLoop_of_comap_of_isPLSphere
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent)
    (hSK : S.manifoldComplex.space ⊆ K.space)
    (hBK : S.boundaryNeighborhood.space ⊆ (PiecewiseLinear.boundaryComplex 3 K).space)
    {V : Set E} (β : C(S.boundaryNeighborhoodSpace, V))
    (hβ : ∀ x, (β x : E) = (x : E)) {y : V} (hb : β S.basepoint = y)
    (N : Subgroup (FundamentalGroup V y)) [N.Normal]
    (hN : S.normalSubgroup = N.comap (FundamentalGroup.mapOfEq β hb)) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → E)
      (γ : freeLoop V) (r : Path y (γ 0)),
      IsPLBall 2 P ∧ IsPLHomeomorphOn f P (f '' P) ∧ MapsTo f P K.space ∧
      P ∩ f ⁻¹' (PiecewiseLinear.boundaryComplex 3 K).space = frontier P ∧
      f '' P ∩ (PiecewiseLinear.boundaryComplex 3 K).space = f '' frontier P ∧
      range (fun θ => (γ θ : E)) = f '' frontier P ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass y γ r) N := by
  let A := Classical.choice (S.nonempty_embeddedDisk_of_isPLSphere_boundaryComponent hB)
  obtain ⟨γ, r, hrange, havoid⟩ := A.exists_boundaryLoop_of_comap β hβ hb N hN
  have hpre := A.preimage_boundaryComplex_eq K hK hSK hBK
  refine ⟨A.domain, A.map, γ, r, A.isPLBall_domain, A.isPLHomeomorphOn,
    A.mapsTo.mono_right hSK, hpre, ?_, hrange, havoid⟩
  rw [← image_inter_preimage, hpre]

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
