/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

/-!
# Locally finite families of splitting disks
-/

open Set Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_locallyFinite_pairwise_disjoint_open_supersets
    {X ι : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i)) (hloc : LocallyFinite F)
    (hdis : Pairwise (Disjoint on F)) {U : Set X} (hU : IsOpen U)
    (hFU : ∀ i, F i ⊆ U) :
    ∃ V : ι → Set X,
      (∀ i, IsOpen (V i)) ∧
      (∀ i, F i ⊆ V i) ∧
      (∀ i, V i ⊆ U) ∧
      LocallyFinite V ∧
      Pairwise (Disjoint on V) := by
  classical
  let S : Set X := ⋃ i, F i
  let A : ι → Set X := fun i => U ∩ (⋃ j : {j // j ≠ i}, F j)ᶜ
  have hSclosed : IsClosed S := hloc.isClosed_iUnion hclosed
  have hAopen (i : ι) : IsOpen (A i) := by
    apply hU.inter
    change IsOpen ((⋃ j : {j // j ≠ i}, (F ∘ Subtype.val) j)ᶜ)
    exact ((hloc.comp_injective Subtype.val_injective).isClosed_iUnion
      fun j => by change IsClosed (F j.val); exact hclosed j.val).isOpen_compl
  have hFA (i : ι) : F i ⊆ A i := by
    intro x hxi
    refine ⟨hFU i hxi, ?_⟩
    rw [mem_compl_iff]
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdis j.property) hxj hxi
  have hSA : S ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hFA i hxi⟩
  obtain ⟨B, hBopen, hSB, hBloc, hBA⟩ :=
    precise_refinement_set hSclosed A hAopen hSA
  obtain ⟨O, hSO, hOopen, hOBclosure⟩ :=
    exists_subset_iUnion_closure_subset hSclosed hBopen
      (fun x _ => hBloc.point_finite x) hSB
  have hOB (i : ι) : O i ⊆ B i := subset_closure.trans (hOBclosure i)
  have hOloc : LocallyFinite O := hBloc.subset hOB
  have hFO (i : ι) : F i ⊆ O i := by
    intro x hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hSO (mem_iUnion.mpr ⟨i, hxi⟩))
    have hji : j = i := by
      by_contra hne
      have hxAj := hBA j (hOB j hxj)
      exact hxAj.2 (mem_iUnion.mpr ⟨⟨i, Ne.symm hne⟩, hxi⟩)
    exact hji ▸ hxj
  let V : ι → Set X := fun i => O i ∩ (⋃ j : {j // j ≠ i}, closure (O j))ᶜ
  have hVopen (i : ι) : IsOpen (V i) := by
    apply (hOopen i).inter
    change IsOpen ((⋃ j : {j // j ≠ i}, ((fun k => closure (O k)) ∘ Subtype.val) j)ᶜ)
    exact ((hOloc.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      fun _ => isClosed_closure).isOpen_compl
  have hFV (i : ι) : F i ⊆ V i := by
    intro x hxi
    refine ⟨hFO i hxi, ?_⟩
    rw [mem_compl_iff]
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    have hxAj := hBA j (hOBclosure j hxj)
    exact hxAj.2 (mem_iUnion.mpr ⟨⟨i, Ne.symm j.property⟩, hxi⟩)
  have hVU (i : ι) : V i ⊆ U :=
    inter_subset_left.trans ((hOB i).trans ((hBA i).trans inter_subset_left))
  have hVloc : LocallyFinite V := hOloc.subset fun _ => inter_subset_left
  have hVdis : Pairwise (Disjoint on V) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxj.2 (mem_iUnion.mpr ⟨⟨i, hij⟩, subset_closure hxi.1⟩)
  exact ⟨V, hVopen, hFV, hVU, hVloc, hVdis⟩

open Classical in
theorem LocallyFinitePLPieceIn.splittingDisk_faces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    (e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2}) :
    (splittingDisk T.complex e e.property.1).faces.Finite := by
  classical
  let C : Set T.complex.space :=
    (Subtype.val : T.complex.space → E) ⁻¹' convexHull ℝ ((e : Finset E) : Set E)
  have hCcompact : IsCompact C := by
    rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
    · exact e.val.finite_toSet.isCompact_convexHull ℝ
    · intro x hx
      exact ⟨⟨x, T.complex.convexHull_subset_space e.property.1 hx⟩, rfl⟩
  have hmeet := T.locallyFinite.finite_nonempty_inter_compact hCcompact
  have hcofaces : {s : T.complex.faces | (e : Finset E) ⊆ s}.Finite := by
    apply hmeet.subset
    intro s hes
    let x : T.complex.space :=
      ⟨e.val.centroid ℝ id, T.complex.convexHull_subset_space e.property.1
        (e.val.centroid_mem_convexHull
          (T.complex.nonempty_of_mem_faces e.property.1))⟩
    refine ⟨x, ?_, ?_⟩
    · exact convexHull_mono (Finset.coe_subset.mpr hes)
        (e.val.centroid_mem_convexHull
          (T.complex.nonempty_of_mem_faces e.property.1))
    · exact e.val.centroid_mem_convexHull
        (T.complex.nonempty_of_mem_faces e.property.1)
  let P : Set (Finset E) :=
    {s | s ∈ T.complex.faces ∧ (e : Finset E) ⊆ s}
  have hPfinite : P.Finite := by
    apply (Set.Finite.image (fun s : T.complex.faces => (s : Finset E)) hcofaces).subset
    rintro s ⟨hs, hes⟩
    exact ⟨⟨s, hs⟩, hes, rfl⟩
  have hdual : (dualCell T.complex e e.property.1).faces.Finite := by
    have hsub : (dualCell T.complex e e.property.1).faces ⊆
        (fun d : Finset (Finset E) => d.image fun s => s.centroid ℝ id) ''
          {d | (d : Set (Finset E)) ⊆ P} := by
      intro u hu
      obtain ⟨d, hd, -, hsub, rfl⟩ :=
        (mem_dualCell_faces_iff T.complex e.property.1).mp hu
      refine ⟨d, ?_, rfl⟩
      intro s hs
      exact ⟨hd.mem_faces hs, hsub s hs⟩
    refine Set.Finite.subset (Set.Finite.image _ ?_) hsub
    exact hPfinite.finite_subsets.preimage Finset.coe_injective.injOn
  let _ : Finite (dualCell T.complex e e.property.1).faces := hdual.to_subtype
  change (starComplex (barycentricSubdivision
    (dualCell T.complex e e.property.1)) (e.val.centroid ℝ id)).faces.Finite
  exact (Set.toFinite _).subset (starComplex_faces_subset _ _)

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
  exact exists_locallyFinite_pairwise_disjoint_open_supersets
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

end DifferentialGeometry.Topology.PiecewiseLinear
