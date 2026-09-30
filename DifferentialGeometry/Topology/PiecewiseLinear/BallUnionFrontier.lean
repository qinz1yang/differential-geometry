/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Topological

variable {X : Type*} [TopologicalSpace X]

theorem IsPreconnected.subset_of_disjoint_frontier {Y T : Set X} (hY : IsPreconnected Y)
    (hYT : (Y ∩ T).Nonempty) (hfr : Disjoint Y (frontier T)) : Y ⊆ T := by
  have hsub : Y ⊆ interior T ∪ (closure T)ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure T
    · refine Or.inl ?_
      by_contra hyi
      exact Set.disjoint_left.mp hfr hy ⟨hyc, hyi⟩
    · exact Or.inr hyc
  have hdis : Disjoint (interior T) (closure T)ᶜ :=
    Set.disjoint_left.mpr fun _ hy hyc => hyc (interior_subset_closure hy)
  obtain ⟨y, hyY, hyT⟩ := hYT
  have hyi : y ∈ interior T := by
    rcases hsub hyY with h | h
    · exact h
    · exact absurd (subset_closure hyT) h
  exact (IsPreconnected.subset_left_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl hdis hsub ⟨y, hyY, hyi⟩ hY).trans interior_subset

theorem exists_isOpen_inter_homeomorph_of_inter_eq {S T O : Set X} (hO : IsOpen O)
    (hST : O ∩ S = O ∩ T) {x : X} (hxO : x ∈ O)
    (hT : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ Nonempty (↥(W ∩ T) ≃ₜ U)) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ Nonempty (↥(W ∩ S) ≃ₜ U) := by
  obtain ⟨W, hW, hxW, U, hU, ⟨e⟩⟩ := hT
  have hsub : (W ∩ O) ∩ S ⊆ W ∩ T := by
    rintro y ⟨⟨hyW, hyO⟩, hyS⟩
    have hy : y ∈ O ∩ T := by
      rw [← hST]
      exact ⟨hyO, hyS⟩
    exact ⟨hyW, hy.2⟩
  have hrange : {z : ↥(W ∩ T) | (z : X) ∈ (W ∩ O) ∩ S} = Subtype.val ⁻¹' O := by
    ext z
    constructor
    · rintro ⟨⟨-, hzO⟩, -⟩
      exact hzO
    · intro hzO
      have hz : (z : X) ∈ O ∩ S := by
        rw [hST]
        exact ⟨hzO, z.2.2⟩
      exact ⟨⟨z.2.1, hzO⟩, hz.2⟩
  have hincl : IsOpenEmbedding (inclusion hsub) := by
    refine ⟨IsEmbedding.inclusion hsub, ?_⟩
    rw [range_inclusion, hrange]
    exact hO.preimage continuous_subtype_val
  have hF := (hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding).comp hincl
  exact ⟨W ∩ O, hW.inter hO, ⟨hxW, hxO⟩, _, hF.isOpen_range, ⟨hF.toIsEmbedding.toHomeomorph⟩⟩

theorem mem_frontier_iUnion_of_mem_frontier {ι : Type*} [Finite ι] {B : ι → Set X}
    (hB : ∀ i, IsClosed (B i)) {i : ι} {z : X} (hz : z ∈ frontier (B i))
    (hzB : ∀ k, k ≠ i → z ∉ B k) : z ∈ frontier (⋃ k, B k) := by
  rw [(hB i).frontier_eq] at hz
  rw [(isClosed_iUnion_of_finite hB).frontier_eq]
  refine ⟨mem_iUnion.mpr ⟨i, hz.1⟩, fun hzi => hz.2 ?_⟩
  have hcl : IsClosed (⋃ k ∈ {k | k ≠ i}, B k) :=
    (Set.toFinite _).isClosed_biUnion fun k _ => hB k
  refine interior_maximal (t := interior (⋃ k, B k) ∩ (⋃ k ∈ {k | k ≠ i}, B k)ᶜ) ?_
    (isOpen_interior.inter hcl.isOpen_compl) ⟨hzi, ?_⟩
  · rintro y ⟨hy, hyn⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (interior_subset hy)
    by_cases hki : k = i
    · rw [← hki]
      exact hk
    · exact absurd (mem_biUnion (show k ∈ {k | k ≠ i} from hki) hk) hyn
  · intro hz'
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz'
    exact hzB k hk hzk

theorem finite_image_connectedComponentIn_of_eq_iUnion {S : Set X} {ι : Type*} [Finite ι]
    {Y : ι → Set X} (hY : ∀ i, IsPreconnected (Y i)) (hS : S = ⋃ i, Y i) :
    ((fun y => connectedComponentIn S y) '' S).Finite := by
  have hfin : (⋃ i, (fun y => connectedComponentIn S y) '' Y i).Finite := by
    refine Set.finite_iUnion fun i => Set.Subsingleton.finite ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    have hYS : Y i ⊆ S := by
      rw [hS]
      exact subset_iUnion Y i
    exact connectedComponentIn_eq ((hY i).subset_connectedComponentIn hy hYS hy')
  refine hfin.subset ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [hS] at hy
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨i, y, hyi, rfl⟩

end Topological

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsLocallyPolyhedral.of_forall_isOpen_inter_eq {S : Set E}
    (h : ∀ x ∈ S, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∃ T : Set E, IsPolyhedron T ∧ O ∩ S = O ∩ T) :
    IsLocallyPolyhedral S := fun x hx => by
  obtain ⟨O, hO, hxO, T, hT, hST⟩ := h x hx
  have hTO : T ∩ O = S ∩ O := by rw [inter_comm T, ← hST, inter_comm]
  have hxT : x ∈ T ∩ O := by
    rw [hTO]
    exact ⟨hx, hxO⟩
  obtain ⟨P, hP, hPTO, hPx⟩ := (hT.isLocallyPolyhedral.inter_isOpen hO) x hxT
  refine ⟨P, hP, fun y hy => ?_, ?_⟩
  · have hy' := hPTO hy
    rw [hTO] at hy'
    exact hy'.1
  · rw [nhdsWithin_restrict S hxO hO, ← hTO]
    exact hPx

omit [FiniteDimensional ℝ E] in
theorem restrict_space_eq_inter_of_openSimplex (K : Geometry.SimplicialComplex ℝ E) {Z : Set E}
    (hZ : ∀ σ ∈ K.faces, (openSimplex σ ∩ Z).Nonempty → convexHull ℝ (σ : Set E) ⊆ Z) :
    (restrict K Z).space = K.space ∩ Z := by
  apply Subset.antisymm
  · exact subset_inter (space_mono_of_faces_subset (restrict_faces_subset K Z))
      (restrict_space_subset K Z)
  · rintro x ⟨hxK, hxZ⟩
    obtain ⟨σ, hσ, hxσ⟩ := exists_face_mem_openSimplex K hxK
    exact (restrict K Z).mem_space_iff.mpr
      ⟨σ, ⟨hσ, hZ σ hσ ⟨x, hxσ, hxZ⟩⟩, openSimplex_subset_convexHull σ hxσ⟩

theorem exists_simplicialComplex_iUnion_isPLSphere_one {ι : Type*} [Finite ι] {J : ι → Set E}
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hdisj : Pairwise fun i j => Disjoint (J i) (J j)) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧ (∀ t ∈ G.faces, t.card ≤ 2) ∧
      G.space = ⋃ i, J i := by
  obtain ⟨G, hGfin, hGsp⟩ :=
    (IsPolyhedron.iUnion fun i => (hJ i).isPolyhedron).exists_simplicialComplex
  have : Finite G.faces := hGfin.to_subtype
  have hJc : ∀ i, IsClosed (J i) := fun i => (hJ i).isPolyhedron.isClosed
  have hone : ∀ t ∈ G.faces, ∃ i, convexHull ℝ (t : Set E) ⊆ J i := by
    intro t ht
    obtain ⟨p, hp⟩ := G.nonempty_of_mem_faces ht
    have hpt : p ∈ convexHull ℝ (t : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)
    have hsp : convexHull ℝ (t : Set E) ⊆ ⋃ i, J i := by
      rw [← hGsp]
      exact G.convexHull_subset_space ht
    obtain ⟨i, hpi⟩ := mem_iUnion.mp (hsp hpt)
    refine ⟨i, ?_⟩
    have hcl : IsClosed (⋃ k ∈ {k | k ≠ i}, J k) :=
      (Set.toFinite _).isClosed_biUnion fun k _ => hJc k
    have hcover : convexHull ℝ (t : Set E) ⊆ J i ∪ ⋃ k ∈ {k | k ≠ i}, J k := by
      intro y hy
      obtain ⟨k, hyk⟩ := mem_iUnion.mp (hsp hy)
      by_cases hki : k = i
      · rw [hki] at hyk
        exact Or.inl hyk
      · exact Or.inr (mem_biUnion (show k ∈ {k | k ≠ i} from hki) hyk)
    have hdis : convexHull ℝ (t : Set E) ∩ (J i ∩ ⋃ k ∈ {k | k ≠ i}, J k) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy.2.2
      exact Set.disjoint_left.mp (hdisj (Ne.symm hk)) hy.2.1 hyk
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (convex_convexHull ℝ (t : Set E)).isPreconnected (J i) _ (hJc i) hcl hcover hdis with h | h
    · exact h
    · obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp (h hpt)
      exact absurd hpk (Set.disjoint_left.mp (hdisj (Ne.symm hk)) hpi)
  refine ⟨G, hGfin, fun t ht => ?_, hGsp⟩
  obtain ⟨i, hti⟩ := hone t ht
  have hRsp : (restrict G (J i)).space = J i := by
    refine Subset.antisymm (restrict_space_subset G (J i)) fun y hy => ?_
    have hyG : y ∈ G.space := by
      rw [hGsp]
      exact mem_iUnion.mpr ⟨i, hy⟩
    obtain ⟨σ, hσ, hyσ⟩ := G.mem_space_iff.mp hyG
    obtain ⟨k, hσk⟩ := hone σ hσ
    have hki : k = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (hσk hyσ) hy
    rw [hki] at hσk
    exact (restrict G (J i)).mem_space_iff.mpr ⟨σ, ⟨hσ, hσk⟩, hyσ⟩
  have : Finite (restrict G (J i)).faces := (restrict_faces_finite G (J i)).to_subtype
  have hsph : IsPLSphere 1 (restrict G (J i)).space := by
    rw [hRsp]
    exact hJ i
  exact hsph.isCombinatorialManifold.card_le _ ⟨ht, hti⟩

end Polyhedral

section Chart

theorem exists_isOpen_inter_frontier_iUnion_eq_isPLSphere {ι : Type*} [Finite ι]
    {B : ι → Set (EuclideanSpace ℝ (Fin 3))} (hB : ∀ i, IsPLBall 3 (B i))
    (hD : ∀ i j, i ≠ j → (B i ∩ B j).Nonempty →
      IsPLBall 2 (B i ∩ B j) ∧ B i ∩ B j ⊆ frontier (B i))
    (h3 : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → Disjoint (B i ∩ B j) (B k))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ frontier (⋃ i, B i)) :
    ∃ O : Set (EuclideanSpace ℝ (Fin 3)), IsOpen O ∧ x ∈ O ∧
      ∃ T : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 2 T ∧
        O ∩ frontier (⋃ i, B i) = O ∩ T := by
  have hBc : ∀ i, IsClosed (B i) := fun i => (hB i).isPolyhedron.isClosed
  obtain ⟨i, hxi⟩ := mem_iUnion.mp ((isClosed_iUnion_of_finite hBc).frontier_subset hx)
  have hO : IsOpen (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ :=
    ((Set.toFinite _).isClosed_biUnion fun k _ => hBc k).isOpen_compl
  have hxO : x ∈ (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ := by
    intro hx'
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx'
    exact hk hxk
  have hreduce : ∀ Y : Set (EuclideanSpace ℝ (Fin 3)), (∀ k, x ∈ B k → B k ⊆ Y) →
      Y ⊆ ⋃ k, B k → (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ ∩ frontier (⋃ k, B k) =
        (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ ∩ frontier Y := by
    intro Y hY hYU
    have h1 : (⋃ k, B k) ∩ (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ = Y ∩ (⋃ k ∈ {k | x ∉ B k}, B k)ᶜ := by
      apply Subset.antisymm
      · rintro y ⟨hy, hyO⟩
        obtain ⟨k, hk⟩ := mem_iUnion.mp hy
        by_cases hxk : x ∈ B k
        · exact ⟨hY k hxk hk, hyO⟩
        · exact absurd (mem_biUnion (show k ∈ {k | x ∉ B k} from hxk) hk) hyO
      · exact inter_subset_inter_left _ hYU
    rw [inter_comm _ (frontier (⋃ k, B k)), inter_comm _ (frontier Y),
      ← frontier_inter_open_inter hO, h1, frontier_inter_open_inter hO]
  by_cases hj : ∃ j, j ≠ i ∧ x ∈ B j
  · obtain ⟨j, hji, hxj⟩ := hj
    have hij : i ≠ j := fun h => hji h.symm
    have hne : (B i ∩ B j).Nonempty := ⟨x, hxi, hxj⟩
    have hDij := hD i j hij hne
    have hDji := hD j i hji ⟨x, hxj, hxi⟩
    have hY : IsPLBall 3 (B i ∪ B j) := isPLBall_union_of_inter_isPLBall_two (hB i) (hB j)
      hDij.1 hDij.2 (by rw [inter_comm]; exact hDji.2)
    refine ⟨_, hO, hxO, frontier (B i ∪ B j), hY.isPLSphere_frontier, hreduce _ ?_ ?_⟩
    · intro k hxk
      by_cases hki : k = i
      · rw [hki]
        exact subset_union_left
      by_cases hkj : k = j
      · rw [hkj]
        exact subset_union_right
      exact absurd hxk (Set.disjoint_left.mp (h3 i j k hij hki hkj) ⟨hxi, hxj⟩)
    · exact union_subset (subset_iUnion B i) (subset_iUnion B j)
  · simp only [not_exists, not_and] at hj
    refine ⟨_, hO, hxO, frontier (B i), (hB i).isPLSphere_frontier,
      hreduce _ (fun k hxk => ?_) (subset_iUnion B i)⟩
    by_cases hki : k = i
    · subst hki
      exact Subset.rfl
    · exact absurd hxk (hj k hki)

theorem image_stdSimplexBoundary_subset_frontier_iUnion {ι : Type*} [Finite ι]
    {B : ι → Set (EuclideanSpace ℝ (Fin 3))} (hB : ∀ i, IsPLBall 3 (B i))
    (h3 : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → Disjoint (B i ∩ B j) (B k)) {i j : ι} (hij : i ≠ j)
    {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (B i ∩ B j))
    (hDi : B i ∩ B j ⊆ frontier (B i)) :
    q '' stdSimplexBoundary 2 ⊆ frontier (⋃ k, B k) := by
  have hBc : ∀ k, IsClosed (B k) := fun k => (hB k).isPolyhedron.isClosed
  intro x hx
  rw [← (hB i).isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDi] at hx
  obtain ⟨⟨hxi, hxj⟩, hxcl⟩ := hx
  have hV : IsOpen (⋃ k ∈ {k | k ≠ i ∧ k ≠ j}, B k)ᶜ :=
    ((Set.toFinite _).isClosed_biUnion fun k _ => hBc k).isOpen_compl
  have hxV : x ∈ (⋃ k ∈ {k | k ≠ i ∧ k ≠ j}, B k)ᶜ := by
    intro hx'
    obtain ⟨k, ⟨hki, hkj⟩, hxk⟩ := mem_iUnion₂.mp hx'
    exact Set.disjoint_left.mp (h3 i j k hij hki hkj) ⟨hxi, hxj⟩ hxk
  have hsub : (⋃ k ∈ {k | k ≠ i ∧ k ≠ j}, B k)ᶜ ∩ (frontier (B i) \ (B i ∩ B j)) ⊆
      frontier (⋃ k, B k) := by
    rintro z ⟨hzV, hzfr, hzD⟩
    refine mem_frontier_iUnion_of_mem_frontier hBc hzfr fun k hki hzk => ?_
    by_cases hkj : k = j
    · rw [hkj] at hzk
      exact hzD ⟨(hBc i).frontier_subset hzfr, hzk⟩
    · exact hzV (mem_biUnion (show k ∈ {k | k ≠ i ∧ k ≠ j} from ⟨hki, hkj⟩) hzk)
  have hmem := closure_mono hsub (hV.inter_closure ⟨hxV, hxcl⟩)
  rwa [isClosed_frontier.closure_eq] at hmem

end Chart

end DifferentialGeometry.Topology.PiecewiseLinear
