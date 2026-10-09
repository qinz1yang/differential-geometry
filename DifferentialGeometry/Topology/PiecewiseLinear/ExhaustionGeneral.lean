/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.LocalManifold

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem PLPieceIn.isPLSphere_geometricLink_of_image_mem_nhds [FiniteDimensional ℝ E] {m : ℕ}
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]
    {Y : Set X} (T : PLPieceIn E (m + 1) X Y) {v : E} (hv : {v} ∈ T.complex.faces)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1))))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin (m + 1))) X)
    (hstar : closedStar T.complex v ⊆ T.map ⁻¹' e.source)
    (hnhds : T.map '' closedStar T.complex v ∈ 𝓝 (T.map v)) :
    IsPLSphere m (SimplicialComplex.geometricLink T.complex {v}).space := by
  have hfin := T.finite_faces.to_subtype
  have hfinSt := (starComplex_faces_finite T.complex v).to_subtype
  have hStspace := starComplex_space T.complex v hv
  have hvSt := singleton_mem_starComplex T.complex v hv
  have hplSt : IsPiecewiseAffineOn (e ∘ T.map) (starComplex T.complex v).space := by
    refine (T.isPiecewiseAffineOn_chart e he).mono_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space (starComplex T.complex v)) ?_
    rw [hStspace]
    intro x hx
    exact ⟨closedStar_subset_space _ _ hx, hstar hx⟩
  have hinjSt : InjOn (e ∘ T.map) (starComplex T.complex v).space := by
    rw [hStspace]
    exact e.injOn.comp (T.bijOn.injOn.mono (closedStar_subset_space _ _)) hstar
  obtain ⟨St', hSt', hfinSt', hAff⟩ := hplSt.exists_isSubdivision_affineOn_faces _
  have hfinSt'' := hfinSt'.to_subtype
  have hsimp : EqOn (simplicialMap St' (e ∘ T.map)) (e ∘ T.map) St'.space :=
    simplicialMap_eq_of_forall_affineOn St' _ hAff
  have hinjSt' : InjOn (e ∘ T.map) St'.space := by
    rw [hSt'.space_eq]
    exact hinjSt
  have hinj' : InjOn (simplicialMap St' (e ∘ T.map)) St'.space :=
    fun x hx y hy hxy => hinjSt' hx hy (by rw [← hsimp hx, ← hsimp hy]; exact hxy)
  have hind : ∀ s ∈ St'.faces, AffineIndependent ℝ
      ((↑) : {u // u ∈ s.image (e ∘ T.map)} → EuclideanSpace ℝ (Fin (m + 1))) := fun s hs => by
    obtain ⟨Af, hAf⟩ := hAff s hs
    have himgs : s.image (e ∘ T.map) = s.image Af :=
      Finset.image_congr fun w hw => hAf (subset_convexHull ℝ _ hw)
    rw [himgs]
    refine affineIndependent_image_of_injOn_convexHull Af (St'.indep hs) fun x hx y hy hxy =>
      hinjSt' (St'.convexHull_subset_space hs hx) (St'.convexHull_subset_space hs hy) ?_
    rw [hAf hx, hAf hy]
    exact hxy
  obtain ⟨φ', hφ'⟩ := exists_isGlueIso_simplicialImage St' (e ∘ T.map) hind hinj'
  have hfinL := (simplicialImage_faces_finite St' (e ∘ T.map) hind hinj').to_subtype
  have hvSt' : {v} ∈ St'.faces := hSt'.singleton_mem hvSt
  have hgv : T.map v ∈ e.source := hstar (mem_closedStar_self T.complex hv)
  have hLnhds : (simplicialImage St' (e ∘ T.map) hind hinj').space ∈ 𝓝 ((e ∘ T.map) v) := by
    rw [simplicialImage_space, hsimp.image_eq, hSt'.space_eq, hStspace]
    have hpre : e.symm ⁻¹' (T.map '' closedStar T.complex v) ∈ 𝓝 (e (T.map v)) :=
      (e.symm.continuousAt (e.map_source hgv)).preimage_mem_nhds
        (by simpa only [e.left_inv hgv] using hnhds)
    apply Filter.mem_of_superset (Filter.inter_mem (e.open_target.mem_nhds (e.map_source hgv)) hpre)
    rintro y ⟨hy, x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    change e (T.map x) = y
    rw [hxy, e.right_inv hy]
  have hL := isPLSphere_geometricLink_of_mem_nhds finrank_euclideanSpace_fin
    (simplicialImage St' (e ∘ T.map) hind hinj') (hφ'.singleton_mem hvSt') hLnhds
  have hSt'sphere := hφ'.isPLSphere_geometricLink hvSt' hL
  rw [isPLSphere_geometricLink_iff_of_isSubdivision hSt' hvSt, geometricLink_starComplex]
    at hSt'sphere
  exact hSt'sphere

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.image_mem_nhds_of_mem_nhds [FiniteDimensional ℝ E] [T2Space X]
    {Y : Set X} (T : PLPieceIn E n X Y) {x : E} (hx : x ∈ T.complex.space)
    (hY : Y ∈ 𝓝 (T.map x)) {A : Set E} (hA : A ∈ 𝓝[T.complex.space] x) :
    T.map '' A ∈ 𝓝 (T.map x) := by
  have := T.finite_faces.to_subtype
  obtain ⟨O, hO, hxO, hOA⟩ := mem_nhdsWithin.mp hA
  have hcompact := (PiecewiseLinear.isPolyhedron_space T.complex).isCompact.diff hO
  have hclosed := (hcompact.image_of_continuousOn (T.continuousOn.mono sdiff_subset)).isClosed
  have hxnot : T.map x ∉ T.map '' (T.complex.space \ O) := by
    rintro ⟨y, ⟨hy, hyO⟩, hxy⟩
    exact hyO ((T.bijOn.injOn hy hx hxy).symm ▸ hxO)
  apply Filter.mem_of_superset (Filter.inter_mem hY (hclosed.isOpen_compl.mem_nhds hxnot))
  rintro y ⟨hyY, hy⟩
  obtain ⟨z, hz, rfl⟩ := T.bijOn.surjOn hyY
  have hzO : z ∈ O := by
    by_contra hzO
    exact hy ⟨z, ⟨hz, hzO⟩, rfl⟩
  exact mem_image_of_mem _ (hOA ⟨hzO, hz⟩)

theorem exists_isHPolytope_image_symm_mem_nhds_subset {U : Set X} (hU : IsOpen U)
    {x : X} (hxU : x ∈ U) :
    ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope C ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C ∈ 𝓝 x ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C ⊆ U := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have htarget : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e x) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hx))
      ((e.symm.continuousAt (e.map_source hx)).preimage_mem_nhds
        (by simpa only [e.left_inv hx] using hU.mem_nhds hxU))
  obtain ⟨C, hC, hCt, hCnhds⟩ := exists_isHPolytope_subset_mem_nhds htarget
  have hCe : C ⊆ e.target := hCt.trans inter_subset_left
  refine ⟨C, hC, hCe, ?_, ?_⟩
  · change e.symm '' C ∈ 𝓝 x
    rw [e.symm_image_eq_source_inter_preimage hCe]
    exact Filter.inter_mem (e.open_source.mem_nhds hx) ((e.continuousAt hx).preimage_mem_nhds
        hCnhds)
  · rintro y ⟨z, hz, rfl⟩
    exact (hCt hz).2

theorem exists_pLPiece_of_isCompact [T2Space X] [Nonempty X] [HasGroupoid X (plGroupoid n)]
    {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ Q : Set X, IsCompact Q ∧ Nonempty (PLPiece n X Q) ∧ C ⊆ interior Q ∧ Q ⊆ U := by
  classical
  have hlocal : ∀ x : X, ∃ B : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope B ∧
      B ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' B ∈ 𝓝 x ∧
      (x ∈ U → (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' B ⊆ U) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨B, hB, hBe, hBx, hBU⟩ := exists_isHPolytope_image_symm_mem_nhds_subset (n := n) hU hx
      exact ⟨B, hB, hBe, hBx, fun _ => hBU⟩
    · obtain ⟨B, hB, hBe, hBx⟩ := exists_isHPolytope_image_symm_mem_nhds (n := n) x
      exact ⟨B, hB, hBe, hBx, fun h => (hx h).elim⟩
  choose B hB hBe hBx hBU using hlocal
  let V : X → Set X := fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' B x
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover (fun x => interior (V x))
    fun x _ => isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (hBx x))
  obtain ⟨T⟩ := exists_pLPiece_biUnion V (fun x => ⟨B x, hB x, hBe x, rfl⟩) t
  refine ⟨⋃ x ∈ t, V x, T.piece.isCompact, ⟨T⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (hcover hy)
    exact interior_mono (fun z hz => mem_iUnion₂.mpr ⟨x, hx, hz⟩) hyV
  · intro y hy
    obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp hy
    exact hBU x (hCU (htC x hx)) hyV

open Classical in
theorem PLPieceIn.exists_isPolyhedralManifoldWithBoundary_neighborhood_of_subset_interior
    [FiniteDimensional ℝ E] {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] {Q : Set X}
    (T : PLPieceIn E (m + 1) X Q) {C : Set X} (hC : IsCompact C) (hCQ : C ⊆ interior Q) :
    ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
      C ⊆ interior P ∧ P ⊆ interior Q := by
  have := T.finite_faces.to_subtype
  have hcompact := (PiecewiseLinear.isPolyhedron_space T.complex).isCompact
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp T.continuousOn (interior Q) isOpen_interior
  have hpreC : IsCompact (T.complex.space ∩ T.map ⁻¹' C) :=
    hcompact.of_isClosed_subset
      (T.continuousOn.preimage_isClosed_of_isClosed hcompact.isClosed hC.isClosed) inter_subset_left
  have hCO : T.complex.space ∩ T.map ⁻¹' C ⊆ O := by
    intro z hz
    have hzQ : z ∈ T.map ⁻¹' interior Q ∩ T.complex.space := ⟨hCQ hz.2, hz.1⟩
    rw [hpre] at hzQ
    exact hzQ.1
  obtain ⟨δ, hδ, hthick⟩ := hpreC.exists_cthickening_subset_open hO hCO
  obtain ⟨J, hJ, hJfin, -, hJdiam⟩ := exists_isSubdivision_diam_lt T.complex
    (fun s hs => card_le_finrank_succ_of_mem_faces T.complex hs) (half_pos hδ)
  have : Finite J.faces := hJfin.to_subtype
  obtain ⟨K', hK'J, hK'fin, hstar⟩ := exists_isSubdivision_closedStar_subset (n := m + 1) J
    (T.subdivide J hJ hJfin).continuousOn
  have : Finite K'.faces := hK'fin.to_subtype
  have hK' := hK'J.trans hJ
  let T' := T.subdivide K' hK' hK'fin
  have hdiam : ∀ s ∈ K'.faces, diam (convexHull ℝ (s : Set E)) < δ / 2 := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hK'J.exists_face_subset hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans_lt (hJdiam t ht)
  let A : Set E := {x | ∀ t ∈ K'.faces, x ∈ convexHull ℝ (t : Set E) →
    convexHull ℝ (t : Set E) ⊆ O}
  let L := PiecewiseLinear.restrict K' A
  have hCL : T.complex.space ∩ T.map ⁻¹' C ⊆ L.space := by
    intro x hx
    have hxK' : x ∈ K'.space := hK'.space_eq.symm ▸ hx.1
    obtain ⟨s, hs, hxs⟩ := K'.mem_space_iff.mp hxK'
    refine L.convexHull_subset_space ⟨hs, ?_⟩ hxs
    intro y hys t ht hyt z hzt
    apply hthick
    apply mem_cthickening_of_dist_le z x δ (T.complex.space ∩ T.map ⁻¹' C) hx
    have hzy : dist z y < δ / 2 :=
      (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hzt hyt).trans_lt
        (hdiam t ht)
    have hyx : dist y x < δ / 2 :=
      (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hys hxs).trans_lt
        (hdiam s hs)
    have hzx := dist_triangle z y x
    linarith
  have hlocal : IsLocallyCombinatorialManifoldWithBoundary m K' L.space := by
    rintro v hv ⟨s, hs, hvs, x, hxs, hxL⟩
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
    have hvO : v ∈ O := ht.2 hxt s hs hxs (subset_convexHull ℝ _ hvs)
    have hvK' : v ∈ K'.space := K'.convexHull_subset_space hv (by simp)
    have hvK : v ∈ T.complex.space := hK'.space_eq ▸ hvK'
    have hTvQ : T.map v ∈ interior Q := by
      have hm : v ∈ O ∩ T.complex.space := ⟨hvO, hvK⟩
      rw [← hpre] at hm
      exact hm.1
    obtain ⟨e, he, hstarv⟩ := hstar v hv
    exact Or.inl (T'.isPLSphere_geometricLink_of_image_mem_nhds hv e he hstarv
      (T'.image_mem_nhds_of_mem_nhds hvK' (mem_interior_iff_mem_nhds.mp hTvQ)
        (closedStar_mem_nhdsWithin K' v)))
  let N := PiecewiseLinear.derivedNeighborhood K' L
  have hman : IsCombinatorialManifoldWithBoundary (m + 1) N := hlocal.derivedNeighborhood L
  have hNO : N.space ⊆ O := by
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst
    exact hs.2 (s.centroid_mem_convexHull (K'.nonempty_of_mem_faces hs.1)) t ht hst
  have hNK : N.space ⊆ T.complex.space :=
    (derivedNeighborhood_space_subset K' L).trans hK'.space_eq.subset
  have hnhds : ∀ x ∈ T.complex.space ∩ T.map ⁻¹' C, N.space ∈ 𝓝[T.complex.space] x := by
    intro x hx
    rw [← hK'.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset K' A) (hCL hx)
  let P := (T.subdivide (secondDerived K') ((secondDerived_isSubdivision K').trans hK')
    (Set.toFinite _)).restrict N (derivedNeighborhood_faces_subset K' L)
  refine ⟨T.map '' N.space, P.isCompact,
    isPolyhedralManifoldWithBoundary_of_pieceIn P hman, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (interior_subset (hCQ hy))
    exact mem_interior_iff_mem_nhds.mpr (T.image_mem_nhds_of_mem_nhds hx
      (mem_interior_iff_mem_nhds.mp (hCQ hy)) (hnhds x ⟨hx, hy⟩))
  · rintro y ⟨x, hx, rfl⟩
    have hxO : x ∈ O ∩ T.complex.space := ⟨hNO hx, hNK hx⟩
    rw [← hpre] at hxO
    exact hxO.1

theorem exists_isPolyhedralManifoldWithBoundary_neighborhood {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X]
    [Nonempty X] [HasGroupoid X (plGroupoid (m + 1))]
    {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
      C ⊆ interior P ∧ P ⊆ U := by
  obtain ⟨Q, _, ⟨T⟩, hCQ, hQU⟩ := exists_pLPiece_of_isCompact (n := m + 1) hC hU hCU
  obtain ⟨P, hPc, hPm, hCP, hPQ⟩ :=
    T.piece.exists_isPolyhedralManifoldWithBoundary_neighborhood_of_subset_interior hC hCQ
  exact ⟨P, hPc, hPm, hCP, hPQ.trans (interior_subset.trans hQU)⟩

theorem exists_exhaustion_of_isOpen {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [HasGroupoid X (plGroupoid (m + 1))] {U : Set X} (hU : IsOpen U) :
    ∃ N : ℕ → Set X, (∀ i, IsCompact (N i) ∧
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) (N i) ∧
      N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U := by
  classical
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (m + 1)))
      X
  have := hU.locallyCompactSpace
  let C : ℕ → Set X := fun i => ((↑) : U → X) '' compactCovering U i
  have hC : ∀ i, IsCompact (C i) := fun i =>
    (isCompact_compactCovering U i).image continuous_subtype_val
  have hCU : ∀ i, C i ⊆ U := by
    rintro i x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ x ∈ U, ∃ i, x ∈ C i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩
  have hbetween : ∀ {B : Set X}, IsCompact B → B ⊆ U →
      ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
        B ⊆ interior P ∧ P ⊆ U := by
    intro B hB hBU
    exact exists_isPolyhedralManifoldWithBoundary_neighborhood hB hU hBU
  let S := {P : Set X // IsCompact P ∧
    IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ U}
  obtain ⟨P₀, hP₀c, hP₀m, _, hP₀U⟩ := hbetween isCompact_empty (empty_subset U)
  let start : S := ⟨P₀, hP₀c, hP₀m, hP₀U⟩
  have hstep : ∀ i (P : S), ∃ Q : S, P.val ∪ C i ⊆ interior Q.val := by
    intro i P
    obtain ⟨Q, hQc, hQm, hPQ, hQU⟩ := hbetween (P.property.1.union (hC i))
      (union_subset P.property.2.2 (hCU i))
    exact ⟨⟨Q, hQc, hQm, hQU⟩, hPQ⟩
  choose f hf using hstep
  let seq : ℕ → S := Nat.rec start (fun i P => f i P)
  refine ⟨fun i => (seq i).val, fun i =>
    ⟨(seq i).property.1, (seq i).property.2.1, ?_⟩, ?_⟩
  · intro x hx
    exact hf i (seq i) (Or.inl hx)
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (seq i).property.2.2 hi
    · intro x hx
      obtain ⟨i, hi⟩ := hcover x hx
      exact mem_iUnion.mpr ⟨i + 1, interior_subset (hf i (seq i) (Or.inr hi))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
