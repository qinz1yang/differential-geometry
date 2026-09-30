/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.PiecewiseLinear.CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CellGluingSphere
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.StarSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSimplyConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsConeBase.exists_isPLHomeomorphOn_of_isPLSphere [FiniteDimensional ℝ E]
    [DecidableEq E] {p : E} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsConeBase p L) {n : ℕ} (hsph : IsPLSphere n L.space) :
    ∃ g : (Fin (n + 2) → ℝ) → E,
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) (coneComplex hL).space ∧
        g '' stdSimplexBoundary (n + 1) = L.space := by
  obtain ⟨f, hf⟩ := hsph
  obtain ⟨f₀, hf₀⟩ := isPLSphere_simplexBoundary_std n
  have hfin : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hhomeo := hf₀.symm.trans hf
  obtain ⟨g, hg, hgeq, -, -⟩ := exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) hL hhomeo
  rw [coneComplex_std_space] at hg
  refine ⟨g, hg, ?_⟩
  rw [← simplexBoundary_stdVertices_space, hgeq.image_eq, hhomeo.image_eq]

theorem IsTopologicalCellWithInterior.image_of_injOn {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {C I : Set X}
    (hC : IsTopologicalCellWithInterior n C I) {φ : X → Y} (hφ : ContinuousOn φ C)
    (hinj : InjOn φ C) : IsTopologicalCellWithInterior n (φ '' C) (φ '' I) := by
  obtain ⟨θ, rfl⟩ := hC
  have : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let F : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → φ '' C :=
    fun q => ⟨φ (θ q), mem_image_of_mem φ (θ q).2⟩
  have hF : Continuous F :=
    (hφ.comp_continuous (continuous_subtype_val.comp θ.continuous) fun q => (θ q).2).subtype_mk _
  have hFinj : Function.Injective F := fun q q' h =>
    θ.injective (Subtype.ext (hinj (θ q).2 (θ q').2 (congrArg Subtype.val h)))
  have hFsurj : Function.Surjective F := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨q, hq⟩ := θ.surjective ⟨x, hx⟩
    refine ⟨q, Subtype.ext ?_⟩
    change φ (θ q : X) = φ x
    rw [hq]
  let ψ := (show Continuous (Equiv.ofBijective F ⟨hFinj, hFsurj⟩) from hF).homeoOfEquivCompactToT2
  refine ⟨ψ, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    exact ⟨ψ q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨θ q, ⟨θ q, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩

theorem IsTopologicalCellWithInterior.subset_closure {n : ℕ} {X : Type*} [TopologicalSpace X]
    {C I : Set X} (hC : IsTopologicalCellWithInterior (n + 1) C I) : C ⊆ closure I := by
  obtain ⟨θ, rfl⟩ := hC
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  let O : Set B := {q | ‖(q : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1}
  have hO : closure O = univ := by
    apply eq_univ_of_forall
    intro q
    rw [closure_subtype]
    have himg : ((↑) : B → EuclideanSpace ℝ (Fin (n + 1))) '' O = Metric.ball 0 1 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact mem_ball_zero_iff.mpr hw
      · intro hz
        exact ⟨⟨z, Metric.ball_subset_closedBall hz⟩, mem_ball_zero_iff.mp hz, rfl⟩
    rw [himg, closure_ball (0 : EuclideanSpace ℝ (Fin (n + 1))) one_ne_zero]
    exact q.2
  intro x hx
  have hθ : (⟨x, hx⟩ : C) ∈ closure (θ '' O) := by
    rw [← θ.image_closure, hO, image_univ]
    exact θ.surjective.range_eq ▸ mem_univ _
  exact image_closure_subset_closure_image continuous_subtype_val ⟨_, hθ, rfl⟩

open Classical in
theorem IsTopologicalCellWithInterior.exists_isPLHomeomorphOn_of_isPolyhedron {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D Dint : Set E} (hD : IsTopologicalCellWithInterior 2 D Dint)
    (hDp : IsPolyhedron D) (hJ : IsPLSphere 1 (D \ Dint)) :
    ∃ r : (Fin 3 → ℝ) → E, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      r '' stdSimplexBoundary 2 = D \ Dint := by
  have hDintD : Dint ⊆ D := by
    obtain ⟨θ, hθ⟩ := id hD
    rw [hθ]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hJD : D \ Dint ⊆ D := sdiff_subset
  let ι : E →ₗ[ℝ] E × ℝ := LinearMap.inl ℝ E ℝ
  have hιinj : Function.Injective ι := LinearMap.inl_injective
  have hιpa : ∀ P : Set E, IsPolyhedron P → IsPiecewiseAffineOn ι P := fun P hP =>
    (isPiecewiseAffineOn_of_affine ι.toAffineMap isOpen_univ).mono_of_isPolyhedron hP
      (subset_univ _)
  have hιpl : ∀ P : Set E, IsPolyhedron P → IsPLHomeomorphOn ι P (ι '' P) := fun P hP =>
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP (hιpa P hP) hιinj.injOn.bijOn_image
  have hJp : IsPolyhedron (D \ Dint) := hJ.isPolyhedron
  have hD'p : IsPolyhedron (ι '' D) := hDp.image_of_isPiecewiseAffineOn (hιpa D hDp) hιinj.injOn
  have hJ'p : IsPolyhedron (ι '' (D \ Dint)) :=
    hJp.image_of_isPiecewiseAffineOn (hιpa _ hJp) hιinj.injOn
  obtain ⟨K₀, hK₀fin, hK₀⟩ := hD'p.exists_simplicialComplex
  have : Finite K₀.faces := hK₀fin.to_subtype
  obtain ⟨A, hAK₀, hAfin, hAJ, -⟩ := exists_isSubdivision_subcomplexes_closedStars_subset_openStar
    K₀ (fun _ : Unit => ι '' (D \ Dint)) (fun _ => hJ'p) (fun _ => hK₀ ▸ image_mono hJD)
  have : Finite A.faces := hAfin.to_subtype
  have hAspace : A.space = ι '' D := hAK₀.space_eq.trans hK₀
  let L := restrict A (ι '' (D \ Dint))
  have hLfin : L.faces.Finite := restrict_faces_finite A _
  have : Finite L.faces := hLfin.to_subtype
  have hLspace : L.space = ι '' (D \ Dint) := hAJ ()
  have hLA : L.faces ⊆ A.faces := restrict_faces_subset A _
  have hA0 : ∀ q ∈ A.space, (q : E × ℝ).2 = 0 := by
    rw [hAspace]
    rintro _ ⟨x, -, rfl⟩
    rfl
  have hL0 : ∀ q ∈ L.space, (q : E × ℝ).2 = 0 :=
    fun q hq => hA0 q (space_mono_of_faces_subset hLA hq)
  have hcb : IsConeBase (((0 : E), (1 : ℝ)) : E × ℝ) L := isConeBase_of_snd_eq_zero L hL0 0
  have hLsph : IsPLSphere 1 L.space := hLspace ▸ hJ.of_isPLHomeomorphOn (hιpl _ hJp)
  obtain ⟨g, hg, hgb⟩ : ∃ g : (Fin 3 → ℝ) → E × ℝ,
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (coneComplex hcb).space ∧
        g '' stdSimplexBoundary 2 = L.space :=
    hcb.exists_isPLHomeomorphOn_of_isPLSphere (n := 1) hLsph
  have hinter : ι '' D ∩ (coneComplex hcb).space = ι '' (D \ Dint) := by
    rw [← hAspace, space_inter_coneComplex_space A L hcb hA0 hLA, hLspace]
  have hS : (capComplex A L hcb hA0 hLA).space = ι '' D ∪ (coneComplex hcb).space := by
    rw [capComplex_space, hAspace]
  have hJ'eq : ι '' D \ ι '' Dint = ι '' (D \ Dint) := (image_sdiff hιinj D Dint).symm
  have hJcone : ι '' (D \ Dint) ⊆ (coneComplex hcb).space :=
    hLspace ▸ space_subset_coneComplex_space hcb
  have hD' : IsTopologicalCellWithInterior 2 (ι '' D) (ι '' Dint) :=
    hD.image_of_injOn ι.continuous_of_finiteDimensional.continuousOn hιinj.injOn
  have hCone : IsTopologicalCellWithInterior 2 (coneComplex hcb).space
      ((coneComplex hcb).space \ g '' stdSimplexBoundary 2) :=
    hg.isTopologicalCellWithInterior
  have hsph : IsTopologicalSphere 2 (capComplex A L hcb hA0 hLA).space := by
    rw [hS]
    refine hD'.isTopologicalSphere_union hCone ?_ ?_
    · rw [hinter, hJ'eq]
    · rw [hgb, hLspace, hJ'eq, sdiff_sdiff_cancel_left hJcone]
  have : Finite (capComplex A L hcb hA0 hLA).faces :=
    (capComplex_faces_finite A L hcb hA0 hLA hAfin hLfin).to_subtype
  have hM := IsTopologicalSphere.isCombinatorialManifold (capComplex A L hcb hA0 hLA) hsph
  have : SimplyConnectedSpace (capComplex A L hcb hA0 hLA).space := by
    obtain ⟨θ⟩ := hsph
    have : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1) :=
      sphereTwoSimplyConnectedSpace
    exact θ.toHomotopyEquiv.simplyConnectedSpace
  have hSpl : IsPLSphere 2 (capComplex A L hcb hA0 hLA).space :=
    IsCombinatorialManifold.isPLSphere_two_of_simplyConnectedSpace _ hM
  have hdense : A.space ⊆ closure (A.space \ L.space) := by
    rw [hAspace, hLspace, ← hJ'eq, sdiff_sdiff_cancel_left (image_mono hDintD)]
    exact hD'.subset_closure
  have hD'ball : IsPLBall 2 (ι '' D) :=
    hAspace ▸ isPLBall_space_of_isPLSphere_capComplex A L hcb hA0 hLA hLsph hSpl hdense
  obtain ⟨q', hq'⟩ := hD'ball
  have hD'S : ι '' D ⊆ (capComplex A L hcb hA0 hLA).space := hS ▸ subset_union_left
  have hbd := hSpl.inter_closure_sdiff_eq_image_stdSimplexBoundary hq' hD'S
  have hsd : (capComplex A L hcb hA0 hLA).space \ ι '' D =
      (coneComplex hcb).space \ ι '' (D \ Dint) := by
    rw [hS, union_sdiff_left, ← hinter, sdiff_inter_self_eq_sdiff]
  have hgc := hg.isPiecewiseAffineOn.continuousOn
  have hconec : IsClosed (coneComplex hcb).space := by
    rw [← hg.image_eq]
    exact ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).image_of_continuousOn hgc).isClosed
  have hcl : closure ((coneComplex hcb).space \ ι '' (D \ Dint)) = (coneComplex hcb).space := by
    refine Subset.antisymm (closure_minimal sdiff_subset hconec) ?_
    rw [← hg.image_eq]
    rintro _ ⟨x, hx, rfl⟩
    have hsub : openSimplex (stdVertices 1) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      openSimplex_stdVertices_subset_stdSimplex (n := 1)
    refine closure_mono ?_ (((hgc x hx).mono hsub).mem_closure_image
      (stdSimplex_subset_closure_openSimplex 1 hx))
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨mem_image_of_mem g (hsub hw), ?_⟩
    rw [← hLspace, ← hgb]
    rintro ⟨w', hw', hww⟩
    have heq : w' = w := hg.bijOn.injOn hw'.1 (hsub hw) hww
    obtain ⟨-, i, hi⟩ := heq ▸ hw'
    exact (((mem_openSimplex_stdVertices_iff 1).mp hw).1 i).ne' hi
  rw [hsd, hcl, hinter] at hbd
  have hπ : IsPLHomeomorphOn (Prod.fst : E × ℝ → E) (ι '' D) D := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD'p
      ((isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E ℝ).toAffineMap
        isOpen_univ).mono_of_isPolyhedron hD'p (subset_univ _)) ?_
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
      change x = y at hxy
      rw [hxy]
    · intro x hx
      exact ⟨ι x, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨Prod.fst ∘ q', hq'.trans hπ, ?_⟩
  rw [image_comp, ← hbd, image_image]
  simp [ι]

end DifferentialGeometry.Topology.PiecewiseLinear
