import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.LevelPolygons
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import Mathlib.Topology.Connected.PathConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem pathConnectedSpace_of_strongDeformationRetract
    {X : Type u} [TopologicalSpace X] {A : Set X}
    (r : DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract A)
    [PathConnectedSpace A] : PathConnectedSpace X := by
  let pathToRetraction (x : X) : Path x (r.retraction x : X) :=
    { toFun := fun t => r.homotopy (t, x)
      continuous_toFun := r.homotopy.continuous.comp (continuous_id.prodMk continuous_const)
      source' := r.homotopy.apply_zero x
      target' := r.homotopy.apply_one x }
  refine
    { nonempty := ?_
      joined := fun x y => ?_ }
  · obtain ⟨a⟩ : Nonempty A := inferInstance
    exact ⟨a.1⟩
  · let p := PathConnectedSpace.somePath (r.retraction x) (r.retraction y)
    exact ⟨(pathToRetraction x).trans
      ((p.map continuous_subtype_val).trans (pathToRetraction y).symm)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLBall_disjoint_of_isPLSphere_two_of_isCombinatorialManifold_one
    {B : Set E} (hB : IsPLSphere 2 B) (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hG : IsCombinatorialManifold 1 G) (hGB : G.space ⊆ B) :
    ∃ H : Set E, IsPLBall 2 H ∧ H ⊆ B ∧ Disjoint H G.space := by
  classical
  have hBG : ¬B ⊆ G.space := by
    intro hsub
    have heq : B = G.space := Set.Subset.antisymm hsub hGB
    obtain ⟨x, hxB⟩ := hB.nonempty
    obtain ⟨s, hs, -⟩ := G.mem_space_iff.mp (heq ▸ hxB)
    obtain ⟨t, ht, -, htcard⟩ :=
      exists_face_superset_card_eq_of_isPLSphere G (heq ▸ hB) hs
    have htbound := hG.card_le G ht
    omega
  obtain ⟨x, hxB, hxG⟩ := Set.not_subset.mp hBG
  obtain ⟨K, hKfinite, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfinite.to_subtype
  have hKman : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (hKB.symm ▸ hB)
  obtain ⟨K₀, hK₀, hK₀finite, hxK₀⟩ := exists_isSubdivision_singleton_mem K (hKB.symm ▸ hxB)
  let _ : Finite K₀.faces := hK₀finite.to_subtype
  let U : Bool → Set E := fun b => if b then ({x} : Set E)ᶜ else G.spaceᶜ
  have hU : ∀ b, IsOpen (((↑) : K₀.space → E) ⁻¹' U b) := by
    intro b
    cases b with
    | false =>
        exact (isPolyhedron_space G).isClosed.isOpen_compl.preimage continuous_subtype_val
    | true =>
        exact isOpen_compl_singleton.preimage continuous_subtype_val
  have hcover : K₀.space ⊆ ⋃ b, U b := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      exact mem_iUnion.mpr ⟨false, hxG⟩
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
  have hstarG : closedStar R x ⊆ G.spaceᶜ := by
    rw [hbfalse] at hstarU
    change closedStar R x ⊆ G.spaceᶜ at hstarU
    exact hstarU
  have hRman : IsCombinatorialManifold 2 R :=
    (hKman.of_isSubdivision hK₀).of_isSubdivision hR
  refine ⟨closedStar R x, hRman.isPLBall_closedStar hxR, ?_, ?_⟩
  · intro y hy
    have hyR := closedStar_subset_space R x hy
    rw [hR.space_eq, hK₀.space_eq, hKB] at hyR
    exact hyR
  · exact Set.disjoint_left.mpr fun y hyH hyG => hstarG hyH hyG

open Classical in
theorem exists_finite_isPLSphere_decomposition_of_isPLSphere_two
    {B : Set E} (hB : IsPLSphere 2 B) (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hG : IsCombinatorialManifold 1 G) (hGB : G.space ⊆ B) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ S ∈ C, IsPLSphere 1 S) ∧
      C.PairwiseDisjoint id ∧ G.space = ⋃₀ C := by
  classical
  obtain ⟨H, hH, hHB, hHG⟩ :=
    exists_isPLBall_disjoint_of_isPLSphere_two_of_isCombinatorialManifold_one hB G hG hGB
  let R := closure (B \ H)
  have hR : IsPLBall 2 R := hB.isPLBall_closure_sdiff hH hHB
  have hRB : R ⊆ B := closure_minimal sdiff_subset hB.isPolyhedron.isClosed
  have hGR : G.space ⊆ R := by
    intro x hxG
    exact subset_closure ⟨hGB hxG, fun hxH => Set.disjoint_left.mp hHG hxH hxG⟩
  obtain ⟨q, hq⟩ := hR
  let g := Function.invFunOn q (stdSimplex ℝ (Fin 3))
  have hg : IsPLHomeomorphOn g R (stdSimplex ℝ (Fin 3)) := hq.symm
  have hgG : IsPLHomeomorphOn g G.space (g '' G.space) :=
    hg.restrict (isPolyhedron_space G) hGR
  obtain ⟨L, hLfinite, hLspace, hLmap⟩ :=
    exists_isPLHomeomorphOn_image G hgG.isPiecewiseAffineOn hgG.bijOn.injOn
  let _ : Finite L.faces := hLfinite.to_subtype
  have hL : IsCombinatorialManifold 1 L := hG.of_isPLHomeomorphOn hLmap
  let ℓ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, x i
      map_add' := fun x y => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  have hℓ : ℓ ≠ 0 := by
    intro hzero
    have h := LinearMap.congr_fun hzero (fun _ => (1 : ℝ))
    norm_num [ℓ] at h
  have hLfiber : L.space ⊆ {x | ℓ x = 1} := by
    intro x hxL
    obtain ⟨y, hyG, rfl⟩ := hLspace ▸ hxL
    have hsimplex : g y ∈ stdSimplex ℝ (Fin 3) := hg.bijOn.mapsTo (hGR hyG)
    exact hsimplex.2
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    exists_finite_isPLSphere_decomposition_of_subset_fiber L hL (by simp) ℓ hℓ hLfiber
  have hback : q '' L.space = G.space := by
    rw [hLspace]
    ext x
    constructor
    · rintro ⟨-, ⟨y, hyG, rfl⟩, rfl⟩
      rw [show q (g y) = y from hq.bijOn.invOn_invFunOn.2 (hGR hyG)]
      exact hyG
    · intro hxG
      refine ⟨g x, ⟨x, hxG, rfl⟩, ?_⟩
      simpa only [g] using hq.bijOn.invOn_invFunOn.2 (hGR hxG)
  refine ⟨(fun S => q '' S) '' C, hCfinite.image _, ?_, ?_, ?_⟩
  · rintro S ⟨D, hDC, rfl⟩
    have hDL : D ⊆ L.space := (subset_sUnion_of_mem hDC).trans_eq hCcover.symm
    have hDsimplex : D ⊆ stdSimplex ℝ (Fin 3) := hDL.trans fun x hx => by
      rw [hLspace] at hx
      obtain ⟨y, hyG, rfl⟩ := hx
      exact hg.bijOn.mapsTo (hGR hyG)
    exact (hCsphere D hDC).of_isPLHomeomorphOn
      (hq.restrict (hCsphere D hDC).isPolyhedron hDsimplex)
  · rintro S ⟨D, hDC, rfl⟩ T ⟨F, hFC, rfl⟩ hDF
    have hne : D ≠ F := fun h => hDF (congrArg (fun A => q '' A) h)
    have hDL : D ⊆ L.space := (subset_sUnion_of_mem hDC).trans_eq hCcover.symm
    have hFL : F ⊆ L.space := (subset_sUnion_of_mem hFC).trans_eq hCcover.symm
    have hDsimplex : D ⊆ stdSimplex ℝ (Fin 3) := hDL.trans fun x hx => by
      rw [hLspace] at hx
      obtain ⟨y, hyG, rfl⟩ := hx
      exact hg.bijOn.mapsTo (hGR hyG)
    have hFsimplex : F ⊆ stdSimplex ℝ (Fin 3) := hFL.trans fun x hx => by
      rw [hLspace] at hx
      obtain ⟨y, hyG, rfl⟩ := hx
      exact hg.bijOn.mapsTo (hGR hyG)
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hyD, rfl⟩ ⟨z, hzF, hzy⟩
    have hzy' : z = y := hq.bijOn.injOn (hFsimplex hzF) (hDsimplex hyD) hzy
    subst z
    exact Set.disjoint_left.mp (hCdisjoint hDC hFC hne) hyD hzF
  · rw [← hback, hCcover, image_sUnion]

namespace NormalSystem

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem boundaryComplex_isCombinatorialManifold (S : NormalSystem E) :
    IsCombinatorialManifold 2 S.boundaryComplex := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact isCombinatorialManifold_boundaryComplex S.manifoldComplex S.isManifold

open Classical in
theorem boundaryNeighborhood_isCombinatorialManifoldWithBoundary (S : NormalSystem E) :
    IsCombinatorialManifoldWithBoundary 2 S.boundaryNeighborhood := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact S.boundaryComplex_isCombinatorialManifold.isCombinatorialManifoldWithBoundary
    |>.derivedNeighborhood S.loopComplex

open Classical in
theorem boundaryNeighborhoodBoundary_isCombinatorialManifold (S : NormalSystem E) :
    IsCombinatorialManifold 1 (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood) := by
  let _ : Finite S.boundaryNeighborhood.faces := S.boundaryNeighborhood_faces_finite.to_subtype
  exact isCombinatorialManifold_boundaryComplex S.boundaryNeighborhood
    S.boundaryNeighborhood_isCombinatorialManifoldWithBoundary

open Classical in
omit [FiniteDimensional ℝ E] in
theorem boundaryNeighborhoodBoundary_faces_finite (S : NormalSystem E) :
    (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).faces.Finite := by
  let _ : Finite S.boundaryNeighborhood.faces := S.boundaryNeighborhood_faces_finite.to_subtype
  exact PiecewiseLinear.boundaryComplex_faces_finite 2 S.boundaryNeighborhood

open Classical in
theorem exists_boundaryNeighborhoodBoundary_decomposition (S : NormalSystem E)
    (hB : IsPLSphere 2 S.boundaryComplex.space) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
      C.PairwiseDisjoint id ∧
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space = ⋃₀ C := by
  let G := PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood
  let _ : Finite G.faces := S.boundaryNeighborhoodBoundary_faces_finite.to_subtype
  have hGB : G.space ⊆ S.boundaryComplex.space :=
    (boundaryComplex_space_subset 2 S.boundaryNeighborhood).trans
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex)
  exact exists_finite_isPLSphere_decomposition_of_isPLSphere_two hB G
    S.boundaryNeighborhoodBoundary_isCombinatorialManifold hGB

open Classical in
theorem exists_boundaryNeighborhoodBoundary_ball_pairs (S : NormalSystem E)
    (hB : IsPLSphere 2 S.boundaryComplex.space) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
      C.PairwiseDisjoint id ∧
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space = ⋃₀ C ∧
          ∀ J ∈ C, ∃ (D₀ D₁ : Set E) (q₀ q₁ : (Fin 3 → ℝ) → E),
            IsPLHomeomorphOn q₀ (stdSimplex ℝ (Fin 3)) D₀ ∧
            IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
            q₀ '' stdSimplexBoundary 2 = J ∧ q₁ '' stdSimplexBoundary 2 = J ∧
            D₀ ∪ D₁ = S.boundaryComplex.space ∧ D₀ ∩ D₁ = J := by
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    S.exists_boundaryNeighborhoodBoundary_decomposition hB
  refine ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover, ?_⟩
  intro J hJC
  exact exists_isPLBall_pair_of_isPLSphere_two hB (hCsphere J hJC)
    ((subset_sUnion_of_mem hJC).trans_eq hCcover.symm |>.trans
      (boundaryComplex_space_subset 2 S.boundaryNeighborhood) |>.trans
        (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex))

open Classical in
noncomputable instance boundaryNeighborhoodPathConnectedSpace (S : NormalSystem E) :
    PathConnectedSpace S.boundaryNeighborhoodSpace := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  let A := derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex
  let f : loopCircle → A := fun θ =>
    ⟨⟨(S.boundaryLoop θ : E), (S.boundaryLoop θ).2⟩, by
      change (S.boundaryLoop θ : E) ∈ S.loopComplex.space
      rw [← S.boundaryLoop_range]
      exact ⟨θ, rfl⟩⟩
  have hf : Continuous f := by
    exact S.boundaryLoop.continuous.subtype_mk _
  have hfsurj : Function.Surjective f := by
    intro x
    have hx : (x.1.1 : E) ∈ Set.range (fun θ => (S.boundaryLoop θ : E)) := by
      rw [S.boundaryLoop_range]
      exact x.2
    obtain ⟨θ, hθ⟩ := hx
    refine ⟨θ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hθ
  have hA : PathConnectedSpace
      (derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) := by
    simpa only [A] using hfsurj.pathConnectedSpace hf
  exact @pathConnectedSpace_of_strongDeformationRetract _ _ _
    S.loopStrongDeformationRetract hA

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
