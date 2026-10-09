/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLBall_inter_eq_of_isPLSphere_subset_boundaryComplex
    {B J : Set E} (hB : IsPLSphere 2 B)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsPreconnected K.space)
    (hKB : K.space ⊆ B) (hJ : IsPLSphere 1 J)
    (hJboundary : J ⊆ (boundaryComplex 2 K).space) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ B ∧ q '' stdSimplexBoundary 2 = J ∧ D ∩ K.space = J := by
  have hJK : J ⊆ K.space := hJboundary.trans (boundaryComplex_space_subset 2 K)
  obtain ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hJ₀, hJ₁, hcover, hinter⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two hB hJ (hJK.trans hKB)
  have hD₀ : IsPLBall 2 D₀ := ⟨q₀, hq₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨q₁, hq₁⟩
  have hsplit : K.space \ (boundaryComplex 2 K).space ⊆ D₀ ∨
      K.space \ (boundaryComplex 2 K).space ⊆ D₁ := by
    by_cases hleft : K.space \ (boundaryComplex 2 K).space ⊆ D₀
    · exact Or.inl hleft
    by_cases hright : K.space \ (boundaryComplex 2 K).space ⊆ D₁
    · exact Or.inr hright
    obtain ⟨x, hx, hxD⟩ := Set.not_subset.mp hleft
    obtain ⟨y, hy, hyD⟩ := Set.not_subset.mp hright
    have hcover' : K.space \ (boundaryComplex 2 K).space ⊆ D₀ ∪ D₁ :=
      sdiff_subset.trans (hKB.trans hcover.symm.subset)
    obtain ⟨z, hz, hzD₀, hzD₁⟩ := isPreconnected_closed_iff.mp
      (hK.isPreconnected_sdiff_boundaryComplex_space hconn) D₀ D₁
      hD₀.isPolyhedron.isClosed hD₁.isPolyhedron.isClosed hcover'
      ⟨y, hy, (hcover' hy).resolve_right hyD⟩
      ⟨x, hx, (hcover' hx).resolve_left hxD⟩
    exact (hz.2 (hJboundary (hinter.subset ⟨hzD₀, hzD₁⟩))).elim
  have hclose := hK.space_subset_closure_sdiff_boundaryComplex_space
  rcases hsplit with hleft | hright
  · have hsub : K.space ⊆ D₀ := hclose.trans (closure_minimal hleft hD₀.isPolyhedron.isClosed)
    refine ⟨D₁, q₁, hq₁, subset_union_right.trans hcover.subset, hJ₁, ?_⟩
    apply Subset.antisymm
    · rintro x ⟨hxD, hxK⟩
      exact hinter.subset ⟨hsub hxK, hxD⟩
    · intro x hx
      exact ⟨(hinter.symm.subset hx).2, hJK hx⟩
  · have hsub : K.space ⊆ D₁ := hclose.trans (closure_minimal hright hD₁.isPolyhedron.isClosed)
    refine ⟨D₀, q₀, hq₀, subset_union_left.trans hcover.subset, hJ₀, ?_⟩
    apply Subset.antisymm
    · rintro x ⟨hxD, hxK⟩
      exact hinter.subset ⟨hxD, hsub hxK⟩
    · intro x hx
      exact ⟨(hinter.symm.subset hx).1, hJK hx⟩

open Classical in
theorem disjoint_isPLBall_of_inter_eq_boundary
    {B M D D' : Set E} (hB : IsPLSphere 2 B)
    {q q' : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hq' : IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D')
    (hDB : D ⊆ B) (hD'B : D' ⊆ B)
    (hDM : D ∩ M = q '' stdSimplexBoundary 2)
    (hD'M : D' ∩ M = q' '' stdSimplexBoundary 2)
    (hdis : Disjoint (q '' stdSimplexBoundary 2) (q' '' stdSimplexBoundary 2)) :
    Disjoint D D' := by
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hD' : IsPLBall 2 D' := ⟨q', hq'⟩
  let R := closure (B \ D)
  have hR := hB.isPLBall_closure_sdiff hD hDB
  have hinter : D ∩ R = q '' stdSimplexBoundary 2 :=
    hB.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDB
  have hcover : B ⊆ D ∪ R := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have havoid : Disjoint D' (q '' stdSimplexBoundary 2) := by
    apply disjoint_left.mpr
    intro x hxD' hxJ
    have hxM := (hDM.symm.subset hxJ).2
    exact disjoint_left.mp hdis hxJ (hD'M.subset ⟨hxD', hxM⟩)
  obtain ⟨z, hz⟩ := (isConnected_stdSimplexBoundary 0).nonempty
  have hzJ' : q' z ∈ q' '' stdSimplexBoundary 2 := ⟨z, hz, rfl⟩
  have hzM := hD'M.symm.subset hzJ'
  have hznot : q' z ∉ D := fun hzD =>
    disjoint_left.mp hdis (hDM.subset ⟨hzD, hzM.2⟩) hzJ'
  have hsub : D' ⊆ R := by
    intro x hxD'
    by_contra hxR
    obtain ⟨w, hwD', hwD, hwR⟩ := isPreconnected_closed_iff.mp
      hD'.isConnected.isPreconnected D R hD.isPolyhedron.isClosed hR.isPolyhedron.isClosed
      (hD'B.trans hcover) ⟨x, hxD', (hcover (hD'B hxD')).resolve_right hxR⟩
      ⟨q' z, hzM.1, (hcover (hD'B hzM.1)).resolve_left hznot⟩
    exact disjoint_left.mp havoid hwD' (hinter.subset ⟨hwD, hwR⟩)
  apply disjoint_left.mpr
  intro x hxD hxD'
  exact disjoint_left.mp havoid hxD' (hinter.subset ⟨hxD, hsub hxD'⟩)

open Classical in
theorem isPolyhedron_sphereWithDiskInteriorsRemoved
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E) (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) : IsPolyhedron (sphereWithDiskInteriorsRemoved B D) := by
  have hpoly (s : Finset (Fin k)) : IsPolyhedron (B ∩ ⋂ i ∈ s, closure (B \ D i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using hB.isPolyhedron
    | @insert i s hi ih =>
        have hD : IsPLBall 2 (D i) := ⟨q i, hq i⟩
        convert ih.inter (hB.isPLBall_closure_sdiff hD (hDB i)).isPolyhedron using 1
        ext x
        simp only [mem_inter_iff, mem_iInter, Finset.mem_insert, forall_eq_or_imp]
        tauto
  simpa only [Finset.mem_univ, iInter_true, sphereWithDiskInteriorsRemoved] using
    hpoly Finset.univ

open Classical in
theorem isPreconnected_sphereWithDiskInteriorsRemoved
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E) (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) (hdisj : Pairwise (Function.onFun Disjoint D)) :
    IsPreconnected (sphereWithDiskInteriorsRemoved B D) := by
  have hdesc : ∀ l : List (Fin k), l.Nodup →
      IsPreconnected (diskAttachmentStage B D l) →
      IsPreconnected (sphereWithDiskInteriorsRemoved B D) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons i l ih =>
        intro hnodup hconn
        have hi := (List.nodup_cons.mp hnodup).1
        have hD : IsPLBall 2 (D i) := ⟨q i, hq i⟩
        have hinter : IsPreconnected (diskAttachmentStage B D l ∩ D i) := by
          rw [inter_comm, disk_inter_diskAttachmentStage q hB hq hDB hdisj hi]
          exact (isConnected_stdSimplexBoundary 0).isPreconnected.image (q i)
            ((hq i).isPiecewiseAffineOn.continuousOn.mono fun _ hx => hx.1)
        apply ih (List.nodup_cons.mp hnodup).2
        exact isPreconnected_left_of_isClosed_union
          (isClosed_diskAttachmentStage hB q hq l) hD.isPolyhedron.isClosed hconn hinter
  apply hdesc (List.finRange k) (List.nodup_finRange k)
  rw [diskAttachmentStage_finRange_eq_sphere hDB]
  exact hB.isConnected.isPreconnected

open Classical in
theorem inter_closure_sdiff_sphereWithDiskInteriorsRemoved
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E) (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) (hdisj : Pairwise (Function.onFun Disjoint D)) :
    sphereWithDiskInteriorsRemoved B D ∩ closure (B \ sphereWithDiskInteriorsRemoved B D) =
      ⋃ i, q i '' stdSimplexBoundary 2 := by
  let C := sphereWithDiskInteriorsRemoved B D
  have hout : B \ C ⊆ ⋃ i, D i := by
    rintro x ⟨hxB, hxC⟩
    by_contra hnot
    apply hxC
    refine ⟨hxB, mem_iInter.mpr fun i => subset_closure ⟨hxB, ?_⟩⟩
    exact fun hxi => hnot (mem_iUnion.mpr ⟨i, hxi⟩)
  have hclosed : IsClosed (⋃ i, D i) :=
    isClosed_iUnion_of_finite fun i =>
      (show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed
  have hclosure : closure (B \ C) ⊆ ⋃ i, D i := closure_minimal hout hclosed
  have hdisk (i : Fin k) : D i ⊆ closure (B \ C) := by
    have hcore : D i \ q i '' stdSimplexBoundary 2 ⊆ B \ C := by
      rintro x ⟨hxD, hxJ⟩
      exact ⟨hDB i hxD, fun hxC => hxJ
        ((disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i).subset ⟨hxD, hxC⟩)⟩
    have h := closure_mono hcore
    rwa [(hq i).closure_sdiff_image_stdSimplexBoundary] at h
  apply Subset.antisymm
  · rintro x ⟨hxC, hxcl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hclosure hxcl)
    exact mem_iUnion.mpr ⟨i,
      (disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i).subset ⟨hxi, hxC⟩⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have h := (disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i).symm.subset hxi
    exact ⟨h.2, hdisk i h.1⟩

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_sphereWithDiskInteriorsRemoved
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E) (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) (hdisj : Pairwise (Function.onFun Disjoint D)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = sphereWithDiskInteriorsRemoved B D ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧
      (boundaryComplex 2 R).space = ⋃ i, q i '' stdSimplexBoundary 2 := by
  let C := sphereWithDiskInteriorsRemoved B D
  have hCB : C ⊆ B := inter_subset_left
  obtain ⟨K, hKfin, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 2 K :=
    (show IsPLSphere 2 K.space from hKB.symm ▸ hB).isCombinatorialManifold
  have hlocal (p : E) (hp : p ∈ C) :
      ∃ W : Set E, IsPLBall 2 W ∧ W ⊆ C ∧ W ∈ 𝓝[C] p := by
    by_cases hmem : ∃ i, p ∈ D i
    · obtain ⟨i, hpi⟩ := hmem
      let Rᵢ := closure (B \ D i)
      have hRi : IsPLBall 2 Rᵢ := hB.isPLBall_closure_sdiff ⟨q i, hq i⟩ (hDB i)
      obtain ⟨L, hLfin, hLR⟩ := hRi.isPolyhedron.exists_simplicialComplex
      let _ : Finite L.faces := hLfin.to_subtype
      have hLball : IsPLBall 2 L.space := hLR.symm ▸ hRi
      let O := (⋃ j : {j : Fin k // j ≠ i}, D j.val)ᶜ
      have hO : IsOpen O :=
        (isClosed_iUnion_of_finite fun j : {j : Fin k // j ≠ i} =>
          (show IsPLBall 2 (D j.val) from ⟨q j.val, hq j.val⟩).isPolyhedron.isClosed).isOpen_compl
      have hpO : p ∈ O := by
        intro hpU
        obtain ⟨j, hpj⟩ := mem_iUnion.mp hpU
        exact disjoint_left.mp (hdisj j.property) hpj hpi
      have hCL : C ⊆ L.space := by
        rw [hLR]
        exact fun x hx => mem_iInter.mp hx.2 i
      obtain ⟨W, hWball, hWsub, hWnhds⟩ :=
        hLball.isCombinatorialManifoldWithBoundary.exists_isPLBall_subset_of_mem_nhdsWithin
          (hCL hp) (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hpO))
      refine ⟨W, hWball, ?_, (nhdsWithin_mono p hCL) hWnhds⟩
      intro x hxW
      have hxRi : x ∈ Rᵢ := hLR ▸ (hWsub hxW).1
      have hxB : x ∈ B := closure_minimal sdiff_subset hB.isPolyhedron.isClosed hxRi
      refine ⟨hxB, mem_iInter.mpr fun j => ?_⟩
      by_cases hji : j = i
      · simpa only [hji] using hxRi
      · exact subset_closure ⟨hxB, fun hxj => (hWsub hxW).2
          (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)⟩
    · let O := (⋃ i, D i)ᶜ
      have hO : IsOpen O :=
        (isClosed_iUnion_of_finite fun i =>
          (show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed).isOpen_compl
      have hpO : p ∈ O := fun hpU => hmem (mem_iUnion.mp hpU)
      obtain ⟨W, hWball, hWsub, hWnhds⟩ :=
        hK.exists_isPLBall_subset_of_mem_nhds (hKB.symm ▸ hCB hp) (hO.mem_nhds hpO)
      have hCK : C ⊆ K.space := hCB.trans_eq hKB.symm
      refine ⟨W, hWball, ?_, (nhdsWithin_mono p hCK) hWnhds⟩
      intro x hxW
      have hxB : x ∈ B := hKB ▸ (hWsub hxW).1
      exact ⟨hxB, mem_iInter.mpr fun i => subset_closure
        ⟨hxB, fun hxi => (hWsub hxW).2 (mem_iUnion.mpr ⟨i, hxi⟩)⟩⟩
  obtain ⟨R, hRfin, hRC⟩ :=
    (isPolyhedron_sphereWithDiskInteriorsRemoved q hB hq hDB).exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsCombinatorialManifoldWithBoundary 2 R := by
    apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods
    simpa only [hRC] using hlocal
  refine ⟨R, hRfin, hRC, hR, ?_⟩
  have hempty : (boundaryComplex 2 K).space = ∅ := by
    change (⋃ s ∈ (boundaryComplex 2 K).faces, convexHull ℝ (s : Set E)) = ∅
    rw [hK.boundaryComplex_faces_eq_empty K]
    simp
  have htrace := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K R
    hK.isCombinatorialManifoldWithBoundary hR
    (hRC.subset.trans (hCB.trans_eq hKB.symm)) (by rw [hempty]; exact disjoint_empty _)
  rw [hRC, hKB] at htrace
  exact htrace.symm.trans (inter_closure_sdiff_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj)

open Classical in
theorem sphereWithDiskInteriorsRemoved_eq_of_boundaryComplex
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E) (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B) (hdisj : Pairwise (Function.onFun Disjoint D))
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 2 M) (hconn : IsConnected M.space)
    (hMB : M.space ⊆ B)
    (hboundary : (⋃ i, q i '' stdSimplexBoundary 2) = (boundaryComplex 2 M).space)
    (hDM : ∀ i, D i ∩ M.space = q i '' stdSimplexBoundary 2) :
    sphereWithDiskInteriorsRemoved B D = M.space := by
  let C := sphereWithDiskInteriorsRemoved B D
  have hMC : M.space ⊆ C := by
    intro x hxM
    refine ⟨hMB hxM, mem_iInter.mpr fun i => ?_⟩
    rw [hB.closure_sdiff_eq_sdiff_image_stdSimplexBoundary (hq i) (hDB i)]
    exact ⟨hMB hxM, fun hx => hx.2 ((hDM i).subset ⟨hx.1, hxM⟩)⟩
  obtain ⟨R, hRfin, hRC, hR, hRboundary⟩ :=
    exists_isCombinatorialManifoldWithBoundary_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj
  let _ : Finite R.faces := hRfin.to_subtype
  have hMR : M.space ⊆ R.space := hMC.trans_eq hRC.symm
  have hbd : (boundaryComplex 2 R).space = (boundaryComplex 2 M).space :=
    hRboundary.trans hboundary
  have hRconn : IsPreconnected R.space := by
    rw [hRC]
    exact isPreconnected_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj
  have hinter := inter_closure_sdiff_subset_boundaryComplex R M hR hM hMR
  have hsub : R.space \ (boundaryComplex 2 R).space ⊆ M.space := by
    obtain ⟨x, hxM, hxnot⟩ := (hM.isConnected_sdiff_boundaryComplex_space hconn).nonempty
    intro y hy
    by_contra hyM
    have hcover : R.space \ (boundaryComplex 2 R).space ⊆
        M.space ∪ closure (R.space \ M.space) := by
      intro z hz
      by_cases hzM : z ∈ M.space
      · exact Or.inl hzM
      · exact Or.inr (subset_closure ⟨hz.1, hzM⟩)
    obtain ⟨z, hz, hzM, hzcl⟩ := isPreconnected_closed_iff.mp
      (hR.isPreconnected_sdiff_boundaryComplex_space hRconn) M.space
      (closure (R.space \ M.space)) (isPolyhedron_space M).isClosed isClosed_closure hcover
      ⟨x, ⟨hMR hxM, by simpa only [hbd] using hxnot⟩, hxM⟩
      ⟨y, hy, subset_closure ⟨hy.1, hyM⟩⟩
    exact hz.2 (hbd.symm ▸ hinter ⟨hzM, hzcl⟩)
  have hRM : R.space ⊆ M.space :=
    hR.space_subset_closure_sdiff_boundaryComplex_space.trans
      (closure_minimal hsub (isPolyhedron_space M).isClosed)
  exact Subset.antisymm (hRC.symm.subset.trans hRM) hMC

namespace NormalSystem

open Classical in
theorem boundaryNeighborhood_space_subset_boundaryComponent (S : NormalSystem E) :
    S.boundaryNeighborhood.space ⊆ S.boundaryComponent := by
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  have hconn : IsPreconnected S.boundaryNeighborhood.space := by
    simpa only [Subtype.range_coe, boundaryNeighborhoodSpace,
      normalSystemBoundaryNeighborhoodSpace, boundaryNeighborhood] using
      (isPreconnected_range (continuous_subtype_val :
        Continuous ((↑) : S.boundaryNeighborhoodSpace → E)))
  exact hconn.subset_connectedComponentIn (S.boundaryLoop 0).property
    (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex)

open Classical in
theorem exists_boundaryNeighborhoodBoundary_decomposition_of_boundaryComponent
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
      C.PairwiseDisjoint id ∧
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space = ⋃₀ C := by
  let G := PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood
  let _ : Finite G.faces := S.boundaryNeighborhoodBoundary_faces_finite.to_subtype
  exact exists_finite_isPLSphere_decomposition_of_isPLSphere_two hB G
    S.boundaryNeighborhoodBoundary_isCombinatorialManifold
    ((boundaryComplex_space_subset 2 S.boundaryNeighborhood).trans
      S.boundaryNeighborhood_space_subset_boundaryComponent)

open Classical in
theorem exists_boundaryNeighborhoodBoundary_disk_sides
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ J ∈ C, IsPLSphere 1 J) ∧
      C.PairwiseDisjoint id ∧
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space = ⋃₀ C ∧
          ∀ J ∈ C, ∃ (D : Set E) (q : (Fin 3 → ℝ) → E),
            IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
            D ⊆ S.boundaryComponent ∧ q '' stdSimplexBoundary 2 = J ∧
            D ∩ S.boundaryNeighborhood.space = J := by
  let _ : Finite S.boundaryNeighborhood.faces := S.boundaryNeighborhood_faces_finite.to_subtype
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  have hconn : IsPreconnected S.boundaryNeighborhood.space := by
    simpa only [Subtype.range_coe, boundaryNeighborhoodSpace,
      normalSystemBoundaryNeighborhoodSpace, boundaryNeighborhood] using
      (isPreconnected_range (continuous_subtype_val :
        Continuous ((↑) : S.boundaryNeighborhoodSpace → E)))
  obtain ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover⟩ :=
    S.exists_boundaryNeighborhoodBoundary_decomposition_of_boundaryComponent hB
  refine ⟨C, hCfinite, hCsphere, hCdisjoint, hCcover, ?_⟩
  intro J hJC
  exact exists_isPLBall_inter_eq_of_isPLSphere_subset_boundaryComplex hB S.boundaryNeighborhood
    S.boundaryNeighborhood_isCombinatorialManifoldWithBoundary hconn
    S.boundaryNeighborhood_space_subset_boundaryComponent (hCsphere J hJC)
    ((subset_sUnion_of_mem hJC).trans_eq hCcover.symm)

open Classical in
theorem exists_pairwiseDisjoint_boundaryNeighborhood_disks
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) :
    ∃ (k : ℕ) (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E),
      (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i)) ∧
      (∀ i, D i ⊆ S.boundaryComponent) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ i, q i '' stdSimplexBoundary 2) =
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space ∧
      ∀ i, D i ∩ S.boundaryNeighborhood.space = q i '' stdSimplexBoundary 2 := by
  obtain ⟨C, hCfinite, -, hCdisjoint, hCcover, hdisks⟩ :=
    S.exists_boundaryNeighborhoodBoundary_disk_sides hB
  let _ : Fintype C := hCfinite.fintype
  choose D q hq hDB hqJ hDM using fun J : C => hdisks J J.property
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, D ∘ e, q ∘ e, fun i => hq (e i), fun i => hDB (e i), ?_, ?_, ?_⟩
  · intro i j hij
    apply disjoint_isPLBall_of_inter_eq_boundary hB (hq (e i)) (hq (e j))
      (hDB (e i)) (hDB (e j))
      ((hDM (e i)).trans (hqJ (e i)).symm) ((hDM (e j)).trans (hqJ (e j)).symm)
    rw [hqJ, hqJ]
    exact hCdisjoint (e i).property (e j).property
      (fun h => hij (e.injective (Subtype.ext h)))
  · rw [hCcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_sUnion.mpr ⟨e i, (e i).property, (hqJ (e i)).subset hi⟩
    · rintro ⟨J, hJC, hxJ⟩
      obtain ⟨i, hi⟩ := e.surjective ⟨J, hJC⟩
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change x ∈ q (e i) '' stdSimplexBoundary 2
      rw [hqJ, hi]
      exact hxJ
  · intro i
    exact (hDM (e i)).trans (hqJ (e i)).symm

end NormalSystem

open Classical in
theorem NormalSystem.exists_sphereWithDiskInteriorsRemoved_eq_boundaryNeighborhood
    (S : NormalSystem E) (hB : IsPLSphere 2 S.boundaryComponent) :
    ∃ (k : ℕ) (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E),
      (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i)) ∧
      (∀ i, D i ⊆ S.boundaryComponent) ∧ Pairwise (Function.onFun Disjoint D) ∧
      sphereWithDiskInteriorsRemoved S.boundaryComponent D = S.boundaryNeighborhood.space ∧
      (⋃ i, q i '' stdSimplexBoundary 2) =
        (PiecewiseLinear.boundaryComplex 2 S.boundaryNeighborhood).space ∧
      ∀ i, D i ∩ S.boundaryNeighborhood.space = q i '' stdSimplexBoundary 2 := by
  let _ : Finite S.boundaryNeighborhood.faces := S.boundaryNeighborhood_faces_finite.to_subtype
  obtain ⟨k, D, q, hq, hDB, hdisj, hboundary, hDM⟩ :=
    S.exists_pairwiseDisjoint_boundaryNeighborhood_disks hB
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  have hconn : IsConnected S.boundaryNeighborhood.space := by
    simpa only [Subtype.range_coe, NormalSystem.boundaryNeighborhoodSpace,
      normalSystemBoundaryNeighborhoodSpace, NormalSystem.boundaryNeighborhood] using
      (isConnected_range (continuous_subtype_val :
        Continuous ((↑) : S.boundaryNeighborhoodSpace → E)))
  exact ⟨k, D, q, hq, hDB, hdisj,
    sphereWithDiskInteriorsRemoved_eq_of_boundaryComplex q hB hq hDB hdisj
      S.boundaryNeighborhood S.boundaryNeighborhood_isCombinatorialManifoldWithBoundary
      hconn S.boundaryNeighborhood_space_subset_boundaryComponent hboundary hDM,
    hboundary, hDM⟩

end DifferentialGeometry.Topology.PiecewiseLinear
