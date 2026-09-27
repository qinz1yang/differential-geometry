/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodSurgery
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.exists_collarTriangulation {C V : Set E3} (hC : IsPLBall 3 C) (hV : IsOpen V)
    (hCV : C ⊆ V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : Geometry.SimplicialComplex ℝ E3, M.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 M ∧ M.space ⊆ V ∧ C ⊆ interior M.space ∧
      (restrict M C).space = C ∧ ∀ s ∈ M.faces, Metric.diam (convexHull ℝ (s : Set E3)) < δ := by
  obtain ⟨B, hB, hCB, hBV⟩ := hC.exists_isPLBall_subset_interior_of_isOpen hV hCV
  obtain ⟨M₀, hM₀fin, hM₀⟩ := hB.isPolyhedron.exists_simplicialComplex
  have : Finite M₀.faces := hM₀fin.to_subtype
  have hCM₀ : C ⊆ M₀.space := by
    rw [hM₀]
    exact hCB.trans interior_subset
  obtain ⟨M, hM, hMfin, hMC, -, hdiam⟩ :=
    exists_isSubdivision_restrict_space_diam_lt M₀ hC.isPolyhedron hCM₀ hC.isPolyhedron hCM₀ hδ
  have : Finite M.faces := hMfin.to_subtype
  have hMsp : M.space = B := hM.space_eq.trans hM₀
  have hB' : IsPLBall (2 + 1) M.space := by
    rw [hMsp]
    exact hB
  refine ⟨M, hMfin, hB'.isCombinatorialManifoldWithBoundary, ?_, ?_, hMC, hdiam⟩
  · rw [hMsp]
    exact hBV
  · rw [hMsp]
    exact hCB

theorem exists_subset_of_convexHull_subset_section34CompactGraphSkeleton
    {K : Geometry.SimplicialComplex ℝ E3} {s : Finset E3} (hs : s ∈ K.faces)
    (hsΓ : convexHull ℝ (s : Set E3) ⊆ section34CompactGraphSkeleton K) :
    ∃ e ∈ K.faces, e.card ≤ 2 ∧ s ⊆ e := by
  have hne := K.nonempty_of_mem_faces hs
  have hx := hsΓ (openSimplex_subset_convexHull s (centroid_mem_openSimplex hne))
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  exact ⟨e, he.1, he.2,
    face_subset_of_mem_openSimplex_of_mem_convexHull K hs he.1 (centroid_mem_openSimplex hne) hxe⟩

theorem card_le_two_of_mem_restrict_section34CompactGraphSkeleton
    {K : Geometry.SimplicialComplex ℝ E3} {s : Finset E3}
    (hs : s ∈ (restrict K (section34CompactGraphSkeleton K)).faces) : s.card ≤ 2 := by
  obtain ⟨e, -, he, hse⟩ :=
    exists_subset_of_convexHull_subset_section34CompactGraphSkeleton hs.1 hs.2
  exact (Finset.card_le_card hse).trans he

theorem convexHull_subset_section34CompactGraphSkeleton {K : Geometry.SimplicialComplex ℝ E3}
    {e : Finset E3} (he : e ∈ K.faces) (hcard : e.card ≤ 2) :
    convexHull ℝ (e : Set E3) ⊆ section34CompactGraphSkeleton K :=
  subset_biUnion_of_mem (u := fun t : Finset E3 => convexHull ℝ (t : Set E3))
    (show e ∈ {t : Finset E3 | t ∈ K.faces ∧ t.card ≤ 2} from ⟨he, hcard⟩)

theorem restrict_section34CompactGraphSkeleton_space (K : Geometry.SimplicialComplex ℝ E3) :
    (restrict K (section34CompactGraphSkeleton K)).space = section34CompactGraphSkeleton K := by
  refine Subset.antisymm (restrict_space_subset _ _) fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  exact (restrict K _).convexHull_subset_space
    ⟨he.1, convexHull_subset_section34CompactGraphSkeleton he.1 he.2⟩ hxe

theorem isConnected_section34CompactGraphSkeleton {K : Geometry.SimplicialComplex ℝ E3}
    [Finite K.faces] (hK : IsConnected K.space) :
    IsConnected (section34CompactGraphSkeleton K) := by
  classical
  set L := restrict K (section34CompactGraphSkeleton K)
  have hvert : ∀ v : K.vertices, (v : E3) ∈ L.vertices := fun v =>
    ⟨v.2, convexHull_subset_section34CompactGraphSkeleton v.2 (by simp)⟩
  let φ : SimplicialComplex.edgeGraph K →g SimplicialComplex.edgeGraph L :=
    { toFun := fun v => ⟨v, hvert v⟩
      map_rel' := fun {u v} huv => by
        refine ⟨fun h => huv.1 (Subtype.ext (congrArg (fun w : L.vertices => (w : E3)) h)),
          huv.2, convexHull_subset_section34CompactGraphSkeleton huv.2 ?_⟩
        convert Finset.card_le_two }
  have hsurj : Function.Surjective φ := fun w => ⟨⟨w, (w.2 : {(w : E3)} ∈ L.faces).1⟩, rfl⟩
  have hG := (edgeGraph_connected_of_isConnected_space K hK).map φ hsurj
  have h := isConnected_space_of_edgeGraph_connected L hG
  rwa [restrict_section34CompactGraphSkeleton_space] at h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_two_neighbors
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {v : E} (hv : {v} ∈ K.faces) :
    ∃ a b : E, a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ ∃ t ∈ K.faces, v ∈ t ∧ a ∈ t ∧ b ∈ t := by
  have hvertex : ∀ (A : Geometry.SimplicialComplex ℝ E), A.space.Nonempty →
      ∃ a, {a} ∈ A.faces := by
    intro A ⟨x, hx⟩
    obtain ⟨t, ht, -⟩ := A.mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := A.nonempty_of_mem_faces ht
    exact ⟨a, A.down_closed ht (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)⟩
  have hLk : IsCombinatorialManifoldWithBoundary (n + 1)
      (SimplicialComplex.geometricLink K {v}) ∧
      (SimplicialComplex.geometricLink K {v}).space.Nonempty := by
    rcases hK v hv with hS | hB
    · exact ⟨hS.isCombinatorialManifold.isCombinatorialManifoldWithBoundary, hS.nonempty⟩
    · exact ⟨hB.isCombinatorialManifoldWithBoundary, hB.nonempty⟩
  obtain ⟨a, ha⟩ := hvertex _ hLk.2
  have hne : (SimplicialComplex.geometricLink (SimplicialComplex.geometricLink K {v})
      {a}).space.Nonempty := by
    rcases hLk.1 a ha with hS | hB
    · exact hS.nonempty
    · exact hB.nonempty
  obtain ⟨b, hb⟩ := hvertex _ hne
  obtain ⟨-, hab, habLk⟩ := (SimplicialComplex.mem_geometricLink_singleton _ a {b}).mp hb
  obtain ⟨-, hvab, hvabK⟩ := (SimplicialComplex.mem_geometricLink_singleton K v _).mp habLk
  obtain ⟨-, hva, -⟩ := (SimplicialComplex.mem_geometricLink_singleton K v {a}).mp ha
  exact ⟨a, b, fun h => hab (by simp [h]), fun h => hva (by simp [h]),
    fun h => hvab (by simp [h]), _, hvabK, by simp, by simp, by simp⟩

theorem ncard_neighborSet_restrict_section34CompactGraphSkeleton_ne_one
    {K : Geometry.SimplicialComplex ℝ E3} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (v : (restrict K (section34CompactGraphSkeleton K)).vertices) :
    ((SimplicialComplex.edgeGraph (restrict K (section34CompactGraphSkeleton K))).neighborSet
      v).ncard ≠ 1 := by
  classical
  revert v
  set L := restrict K (section34CompactGraphSkeleton K)
  intro v
  have hvK : {(v : E3)} ∈ K.faces := (v.2 : {(v : E3)} ∈ L.faces).1
  obtain ⟨a, b, hab, hav, hbv, t, ht, hvt, hat, hbt⟩ := hK.exists_two_neighbors (n := 1) hvK
  have hedge : ∀ c : E3, c ∈ t → c ≠ (v : E3) → {(v : E3), c} ∈ L.faces := by
    intro c hc hcv
    have hK2 : {(v : E3), c} ∈ K.faces := K.down_closed ht
      (Finset.insert_subset hvt (Finset.singleton_subset_iff.mpr hc)) (Finset.insert_nonempty _ _)
    exact ⟨hK2, convexHull_subset_section34CompactGraphSkeleton hK2 Finset.card_le_two⟩
  have hvertL : ∀ c : E3, c ∈ t → c ≠ (v : E3) → c ∈ L.vertices := fun c hc hcv =>
    L.down_closed (hedge c hc hcv) (Finset.singleton_subset_iff.mpr (by simp))
      (Finset.singleton_nonempty c)
  let a' : L.vertices := ⟨a, hvertL a hat hav⟩
  let b' : L.vertices := ⟨b, hvertL b hbt hbv⟩
  have hadj : ∀ (c : L.vertices), (c : E3) ∈ t → (c : E3) ≠ (v : E3) →
      c ∈ (SimplicialComplex.edgeGraph L).neighborSet v := fun c hc hcv =>
    ⟨fun h => hcv (congrArg Subtype.val h).symm, by convert hedge c hc hcv⟩
  have : Finite L.faces := (restrict_faces_finite K _).to_subtype
  have : Finite L.vertices := (SimplicialComplex.finite_vertices L).to_subtype
  have hfin : ((SimplicialComplex.edgeGraph L).neighborSet v).Finite := Set.toFinite _
  have h2 : ({a', b'} : Set L.vertices).ncard = 2 :=
    Set.ncard_pair fun h => hab (congrArg Subtype.val h)
  have hle := Set.ncard_le_ncard (insert_subset (hadj a' hat hav)
    (singleton_subset_iff.mpr (hadj b' hbt hbv))) hfin
  omega

open Classical in
theorem exists_compactGraphApproximation (h331 : Moise331OnTube) {C V : Set E3}
    {h : E3 → E3} (hC : IsPLBall 3 C) (hV : IsOpen V) (hCV : C ⊆ V)
    (hh : Topology.IsEmbedding (V.domRestrict h)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : Geometry.SimplicialComplex ℝ E3, M.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 M ∧ M.space ⊆ V ∧ C ⊆ interior M.space ∧
      (restrict M C).space = C ∧
      (∀ s ∈ M.faces, Metric.diam (convexHull ℝ (s : Set E3)) < δ) ∧
      ∀ W : E3 → Set E3, (∀ v ∈ (restrict M C).vertices,
        W v ∈ nhdsSet (h '' (graphDualCell M (restrict (restrict M C)
          (section34CompactGraphSkeleton (restrict M C))) v).space)) →
      ∃ f₁ : E3 → E3,
        IsPLHomeomorphOn f₁ (⋃ v ∈ (restrict M C).vertices, (graphDualCell M (restrict
          (restrict M C) (section34CompactGraphSkeleton (restrict M C))) v).space)
          (f₁ '' ⋃ v ∈ (restrict M C).vertices, (graphDualCell M (restrict (restrict M C)
            (section34CompactGraphSkeleton (restrict M C))) v).space) ∧
        f₁ '' (⋃ v ∈ (restrict M C).vertices, (graphDualCell M (restrict (restrict M C)
          (section34CompactGraphSkeleton (restrict M C))) v).space) ∈
            nhdsSet (h '' section34CompactGraphSkeleton (restrict M C)) ∧
        ∀ v ∈ (restrict M C).vertices, f₁ '' (graphDualCell M (restrict (restrict M C)
          (section34CompactGraphSkeleton (restrict M C))) v).space ⊆ W v := by
  obtain ⟨M, hMfin, hM, hMV, hCM, hMC, hdiam⟩ := hC.exists_collarTriangulation hV hCV hδ
  refine ⟨M, hMfin, hM, hMV, hCM, hMC, hdiam, fun W hW => ?_⟩
  have : Finite M.faces := hMfin.to_subtype
  set K := restrict M C with hKdef
  set L := restrict K (section34CompactGraphSkeleton K) with hLdef
  have : Finite K.faces := (restrict_faces_finite M C).to_subtype
  have hKM : K.faces ⊆ M.faces := restrict_faces_subset M C
  have hLK : L.faces ⊆ K.faces := restrict_faces_subset K _
  have hKball : IsPLBall (2 + 1) K.space := by
    rw [hMC]
    exact hC
  have hKm : IsCombinatorialManifoldWithBoundary 3 K := hKball.isCombinatorialManifoldWithBoundary
  have hvertLK : L.vertices = K.vertices := by
    ext v
    exact ⟨fun hv => hLK hv, fun hv =>
      ⟨hv, convexHull_subset_section34CompactGraphSkeleton hv (by simp)⟩⟩
  have hLsp : L.space ⊆ C := by
    rw [hLdef, restrict_section34CompactGraphSkeleton_space]
    refine iUnion₂_subset fun e he => ?_
    rw [← hMC]
    exact K.convexHull_subset_space he.1
  have hedge : ∃ e ∈ L.faces, e.card = 2 := by
    obtain ⟨v, hv⟩ : ∃ v, {v} ∈ K.faces := by
      obtain ⟨x, hx⟩ := hKball.nonempty
      obtain ⟨t, ht, -⟩ := K.mem_space_iff.mp hx
      obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces ht
      exact ⟨a, K.down_closed ht (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)⟩
    obtain ⟨a, -, -, hav, -, t, ht, hvt, hat, -⟩ := hKm.exists_two_neighbors (n := 1) hv
    have hK2 : {v, a} ∈ K.faces := K.down_closed ht
      (Finset.insert_subset hvt (Finset.singleton_subset_iff.mpr hat)) (Finset.insert_nonempty _ _)
    exact ⟨{v, a}, ⟨hK2, convexHull_subset_section34CompactGraphSkeleton hK2 Finset.card_le_two⟩,
      Finset.card_pair (Ne.symm hav)⟩
  have hint : ∀ v ∈ L.vertices, v ∈ interior M.space := fun v hv =>
    hCM (hLsp (L.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))))
  have htube₀ := isTube_graphDualCell hMfin hM (hLK.trans hKM)
    (fun s hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs) hedge hint
  set N := ⋃ v ∈ L.vertices, (graphDualCell M L v).space with hNdef
  have hNM : N ⊆ M.space := by
    refine iUnion₂_subset fun v _ x hx => ?_
    have hx' := graphDualCell_space_subset M L v hx
    exact derivedNeighborhood_space_subset M L (by convert hx')
  have hh' : IsEmbedding (N.domRestrict h) := hh.comp (IsEmbedding.inclusion (hNM.trans hMV))
  have htube := htube₀.of_isEmbedding hh'
  have hconn : IsConnected L.space := by
    rw [hLdef, restrict_section34CompactGraphSkeleton_space]
    refine isConnected_section34CompactGraphSkeleton ?_
    rw [hMC]
    exact hC.isConnected
  have hend : ∀ v : L.vertices,
      ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1 :=
    ncard_neighborSet_restrict_section34CompactGraphSkeleton_ne_one hKm
  obtain ⟨f₁, hf₁, hf₁N, hf₁W⟩ :=
    h331 L _ _ _ _ _ h htube hconn hend W fun v hv => hW v (hvertLK ▸ hv)
  have hNK : (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = N := by
    rw [hNdef, hvertLK]
  rw [hNK]
  refine ⟨f₁, hf₁, ?_, fun v hv => hf₁W v (hvertLK.symm ▸ hv)⟩
  have hsp := restrict_section34CompactGraphSkeleton_space K
  rw [← hLdef] at hsp
  rw [← hsp]
  exact hf₁N

end DifferentialGeometry.Topology.PiecewiseLinear
