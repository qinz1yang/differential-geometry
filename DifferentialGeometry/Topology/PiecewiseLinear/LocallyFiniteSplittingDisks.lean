/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocallyFiniteSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

open Set Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem LocallyFinitePLPieceIn.cofaces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    {e : Finset E} (he : e ∈ T.complex.faces) :
    {s : T.complex.faces | e ⊆ (s : Finset E)}.Finite := by
  classical
  let C : Set T.complex.space :=
    (Subtype.val : T.complex.space → E) ⁻¹' convexHull ℝ (e : Set E)
  have hCcompact : IsCompact C := by
    rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
    · exact e.finite_toSet.isCompact_convexHull ℝ
    · intro x hx
      exact ⟨⟨x, T.complex.convexHull_subset_space he hx⟩, rfl⟩
  have hmeet := T.locallyFinite.finite_nonempty_inter_compact hCcompact
  apply hmeet.subset
  intro s hes
  let x : T.complex.space :=
    ⟨e.centroid ℝ id, T.complex.convexHull_subset_space he
      (e.centroid_mem_convexHull (T.complex.nonempty_of_mem_faces he))⟩
  refine ⟨x, ?_, ?_⟩
  · exact convexHull_mono (Finset.coe_subset.mpr hes)
      (e.centroid_mem_convexHull (T.complex.nonempty_of_mem_faces he))
  · exact e.centroid_mem_convexHull (T.complex.nonempty_of_mem_faces he)

open Classical in
theorem LocallyFinitePLPieceIn.geometricLink_faces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    {e : Finset E} (he : e ∈ T.complex.faces) :
    (SimplicialComplex.geometricLink T.complex e).faces.Finite := by
  classical
  let _ : Finite {s : T.complex.faces // e ⊆ (s : Finset E)} :=
    (T.cofaces_finite he).to_subtype
  let f : (SimplicialComplex.geometricLink T.complex e).faces →
      {s : T.complex.faces // e ⊆ (s : Finset E)} := fun s =>
    ⟨⟨e ∪ (s : Finset E), ((mem_geometricLink_faces_iff T.complex).mp s.property).2.2⟩,
      Finset.subset_union_left⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have hs := (mem_geometricLink_faces_iff T.complex).mp s.property
    have ht := (mem_geometricLink_faces_iff T.complex).mp t.property
    have hraw : e ∪ (s : Finset E) = e ∪ (t : Finset E) :=
      congrArg (fun u => (u.1 : Finset E)) hst
    apply Finset.ext
    intro x
    by_cases hxe : x ∈ e
    · have hxs : x ∉ (s : Finset E) := fun hxs => Finset.disjoint_left.mp hs.2.1 hxe hxs
      have hxt : x ∉ (t : Finset E) := fun hxt => Finset.disjoint_left.mp ht.2.1 hxe hxt
      simp [hxs, hxt]
    · have hxmem : x ∈ e ∪ (s : Finset E) ↔ x ∈ e ∪ (t : Finset E) :=
        Finset.ext_iff.mp hraw x
      simpa [hxe] using hxmem
  let _ : Finite (SimplicialComplex.geometricLink T.complex e).faces :=
    Finite.of_injective f hf
  exact Set.toFinite _

open Classical in
theorem LocallyFinitePLPieceIn.isPLSphere_geometricLink
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E d X Y)
    (hK : IsCombinatorialManifold (n + 1) T.complex)
    {e : Finset E} (he : e ∈ T.complex.faces) {k : ℕ}
    (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (SimplicialComplex.geometricLink T.complex e).space := by
  classical
  cases k with
  | zero =>
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      rw [Nat.sub_zero]
      exact hK v he
  | succ k =>
      obtain ⟨v, hv⟩ := T.complex.nonempty_of_mem_faces he
      obtain ⟨e', hve', rfl⟩ : ∃ e', v ∉ e' ∧ e = insert v e' :=
        ⟨e.erase v, Finset.notMem_erase v e, (Finset.insert_erase hv).symm⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcard' : e'.card = k + 1 := by
        rw [Finset.card_insert_of_notMem hve'] at hcard
        omega
      have hv' : {v} ∈ T.complex.faces :=
        T.complex.down_closed he (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)
      have heL : e' ∈ (SimplicialComplex.geometricLink T.complex {v}).faces :=
        (SimplicialComplex.mem_geometricLink_singleton T.complex v e').mpr
          ⟨Finset.card_pos.mp (by omega), hve', he⟩
      let _ : Finite (SimplicialComplex.geometricLink T.complex {v}).faces :=
        (T.geometricLink_faces_finite hv').to_subtype
      rw [geometricLink_insert T.complex hve', show m + 1 - (k + 1) = m - k by omega]
      exact isPLSphere_geometricLink_faces_of_isPLSphere _ (hK v hv') heL hcard' (by omega)

open Classical in
theorem LocallyFinitePLPieceIn.dualCell_faces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    {e : Finset E} (he : e ∈ T.complex.faces) :
    (dualCell T.complex e he).faces.Finite := by
  classical
  have hcofaces := T.cofaces_finite he
  let P : Set (Finset E) :=
    {s | s ∈ T.complex.faces ∧ e ⊆ s}
  have hPfinite : P.Finite := by
    apply (Set.Finite.image (fun s : T.complex.faces => (s : Finset E)) hcofaces).subset
    rintro s ⟨hs, hes⟩
    exact ⟨⟨s, hs⟩, hes, rfl⟩
  have hsub : (dualCell T.complex e he).faces ⊆
      (fun d : Finset (Finset E) => d.image fun s => s.centroid ℝ id) ''
        {d | (d : Set (Finset E)) ⊆ P} := by
    intro u hu
    obtain ⟨d, hd, -, hsub, rfl⟩ := (mem_dualCell_faces_iff T.complex he).mp hu
    refine ⟨d, ?_, rfl⟩
    intro s hs
    exact ⟨hd.mem_faces hs, hsub s hs⟩
  refine Set.Finite.subset (Set.Finite.image _ ?_) hsub
  exact hPfinite.finite_subsets.preimage Finset.coe_injective.injOn

open Classical in
theorem LocallyFinitePLPieceIn.splittingDisk_faces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    (e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2}) :
    (splittingDisk T.complex e e.property.1).faces.Finite := by
  classical
  let _ : Finite (dualCell T.complex e e.property.1).faces :=
    (T.dualCell_faces_finite e.property.1).to_subtype
  change (starComplex (barycentricSubdivision
    (dualCell T.complex e e.property.1)) (e.val.centroid ℝ id)).faces.Finite
  exact (Set.toFinite _).subset (starComplex_faces_subset _ _)

open Classical in
theorem LocallyFinitePLPieceIn.isPLBall_splittingDisk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E d X Y)
    (hK : IsCombinatorialManifold (n + 1) T.complex)
    {e : Finset E} (he : e ∈ T.complex.faces) {k : ℕ}
    (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (splittingDisk T.complex e he).space := by
  classical
  have hdual := T.dualCell_faces_finite he
  let _ : Finite (dualCell T.complex e he).faces := hdual.to_subtype
  have hupper : (upperLink T.complex e).faces.Finite := by
    rw [← geometricLink_dualCell T.complex he]
    exact hdual.subset (SimplicialComplex.geometricLink_le _ _)
  obtain ⟨f, hf⟩ :=
    exists_isPLHomeomorphOn_upperLink_of_faces_finite T.complex he hupper
  have hupperSphere : IsPLSphere (n - k) (upperLink T.complex e).space :=
    (T.isPLSphere_geometricLink hK he hcard hk).of_isPLHomeomorphOn hf.symm
  have hvertex := singleton_centroid_mem_dualCell T.complex he
  have hsub := barycentricSubdivision_isSubdivision (dualCell T.complex e he)
  have hlink : IsPLSphere (n - k)
      (SimplicialComplex.geometricLink (dualCell T.complex e he)
        {e.centroid ℝ id}).space := by
    rw [geometricLink_dualCell]
    exact hupperSphere
  rw [splittingDisk_space]
  exact PiecewiseLinear.isPLBall_closedStar _ (hsub.singleton_mem hvertex)
    ((isPLSphere_geometricLink_iff_of_isSubdivision hsub hvertex).mpr hlink)

open Classical in
theorem LocallyFinitePLPieceIn.locallyFinite_splittingDisk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) :
    LocallyFinite fun e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} =>
      (Subtype.val : T.complex.space → E) ⁻¹'
        (splittingDisk T.complex e e.property.1).space := by
  classical
  intro x
  obtain ⟨t, htx, htfinite⟩ := T.locallyFinite x
  have hedgefinite (s : T.complex.faces) :
      {e : {u : Finset E // u ∈ T.complex.faces ∧ u.card = 2} |
        (e : Finset E) ⊆ s}.Finite := by
    have h := Set.Finite.preimage
      (f := fun e : {u : Finset E // u ∈ T.complex.faces ∧ u.card = 2} =>
        (e : Finset E))
      (s := (s.val.powerset : Set (Finset E)))
      Subtype.val_injective.injOn s.val.powerset.finite_toSet
    apply h.subset
    intro e he
    exact Finset.mem_powerset.mpr he
  refine ⟨t, htx, (htfinite.biUnion fun s _ => hedgefinite s).subset ?_⟩
  intro e he
  obtain ⟨y, hyD, hyt⟩ := he
  obtain ⟨s, hs, hys⟩ := T.complex.mem_space_iff.mp y.property
  let s' : T.complex.faces := ⟨s, hs⟩
  have hsfinite : s' ∈ {s : T.complex.faces |
      (((Subtype.val : T.complex.space → E) ⁻¹'
        convexHull ℝ ((s : Finset E) : Set E)) ∩ t).Nonempty} := by
    exact ⟨y, hys, hyt⟩
  have hes : (e : Finset E) ⊆ s :=
    subset_of_mem_dualCell_of_mem_convexHull T.complex e.property.1 hs
      (splittingDisk_space_subset_dualCell T.complex e.property.1 hyD) hys
  exact Set.mem_biUnion hsfinite hes

open Classical in
theorem LocallyFinitePLPieceIn.pairwise_disjoint_splittingDisk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) :
    Pairwise (Disjoint on fun e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} =>
      (Subtype.val : T.complex.space → E) ⁻¹'
        (splittingDisk T.complex e e.property.1).space) := by
  classical
  intro e f hef
  apply Disjoint.preimage
  apply disjoint_splittingDisk_space T.complex e.property.1 f.property.1
  · exact fun h => hef (Subtype.ext h)
  · exact e.property.2.trans f.property.2.symm

open Classical in
theorem LocallyFinitePLPieceIn.isClosed_splittingDisk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    (e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2}) :
    IsClosed ((Subtype.val : T.complex.space → E) ⁻¹'
      (splittingDisk T.complex e e.property.1).space) := by
  classical
  let _ : Finite (splittingDisk T.complex e e.property.1).faces :=
    (T.splittingDisk_faces_finite e).to_subtype
  exact (isPolyhedron_space (splittingDisk T.complex e e.property.1)).isClosed.preimage
    continuous_subtype_val

namespace LocallyFinitePLPieceIn

open Classical in
theorem exists_locallyFinite_pairwise_disjoint_open_splittingDisk_neighborhoods
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) {U : Set T.complex.space}
    (hU : IsOpen U)
    (hDU : ∀ e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2},
      (Subtype.val : T.complex.space → E) ⁻¹'
        (splittingDisk T.complex e e.property.1).space ⊆ U) :
    ∃ V : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} →
        Set T.complex.space,
      (∀ e, IsOpen (V e)) ∧
      (∀ e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2},
        (Subtype.val : T.complex.space → E) ⁻¹'
        (splittingDisk T.complex e e.property.1).space ⊆ V e) ∧
      (∀ e, V e ⊆ U) ∧
      LocallyFinite V ∧
      Pairwise (Disjoint on V) := by
  classical
  exact DifferentialGeometry.Topology.exists_locallyFinite_pairwise_disjoint_open_supersets
    (fun e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2} =>
      (Subtype.val : T.complex.space → E) ⁻¹'
        (splittingDisk T.complex e e.property.1).space)
    T.isClosed_splittingDisk T.locallyFinite_splittingDisk
    T.pairwise_disjoint_splittingDisk hU hDU

end LocallyFinitePLPieceIn

open Classical in
theorem exists_noncompact_splittingDisk_neighborhood_family_three :
    ∃ (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (V : {s : Finset (EuclideanSpace ℝ (Fin 3)) //
        s ∈ J.faces ∧ s.card = 2} → Set J.space),
      LocallyFinite (fun s : J.faces =>
        (Subtype.val : J.space → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          convexHull ℝ ((s : Finset (EuclideanSpace ℝ (Fin 3))) :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      ¬ IsCompact J.space ∧
      Nonempty {s : Finset (EuclideanSpace ℝ (Fin 3)) //
        s ∈ J.faces ∧ s.card = 2} ∧
      (∀ e, IsOpen (V e)) ∧
      (∀ e : {s : Finset (EuclideanSpace ℝ (Fin 3)) //
          s ∈ J.faces ∧ s.card = 2},
        (Subtype.val : J.space → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          (splittingDisk J e e.property.1).space ⊆ V e) ∧
      LocallyFinite V ∧
      Pairwise (Disjoint on V) := by
  classical
  obtain ⟨J, hJlocal, hJnoncompact, e, he, hecard⟩ :=
    exists_noncompact_locallyFinite_simplicialComplex_three_with_edge
  let T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3
      (EuclideanSpace ℝ (Fin 3)) J.space :=
    euclideanLocallyFinitePLPieceIn J hJlocal
  obtain ⟨V, hVopen, hDV, -, hVloc, hVdis⟩ :=
    T.exists_locallyFinite_pairwise_disjoint_open_splittingDisk_neighborhoods
      (U := Set.univ) isOpen_univ fun _ => subset_univ _
  exact ⟨J, V, hJlocal, hJnoncompact, ⟨⟨e, he, hecard⟩⟩,
    hVopen, hDV, hVloc, hVdis⟩

open Classical in
theorem exists_noncompact_locallyFinite_splittingDisk_isPLBall_model :
    ∃ (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 4)))
      (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 4)) 4
        (EuclideanSpace ℝ (Fin 4)) J.space)
      (e : {s : Finset (EuclideanSpace ℝ (Fin 4)) //
        s ∈ T.complex.faces ∧ s.card = 2}),
      T.complex = J ∧ ¬ IsCompact J.space ∧ IsCombinatorialManifold 3 J ∧
      IsPLBall 2 (splittingDisk T.complex e e.property.1).space := by
  obtain ⟨J, hJlocal, hJnoncompact, hJman, e, he, hecard⟩ :=
    exists_noncompact_locallyFinite_combinatorialManifold_three_with_edge
  let T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 4)) 4
      (EuclideanSpace ℝ (Fin 4)) J.space :=
    euclideanLocallyFinitePLPieceIn J hJlocal
  let e' : {s : Finset (EuclideanSpace ℝ (Fin 4)) //
      s ∈ T.complex.faces ∧ s.card = 2} :=
    ⟨e, he, hecard⟩
  have hTJ : T.complex = J := rfl
  have hball : IsPLBall 2 (splittingDisk T.complex e' e'.property.1).space := by
    simpa using T.isPLBall_splittingDisk hJman e'.property.1 e'.property.2 (by omega)
  exact ⟨J, T, e', hTJ, hJnoncompact, hJman, hball⟩

end DifferentialGeometry.Topology.PiecewiseLinear
