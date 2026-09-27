/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.List.NodupEquivFin

open Set

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}

theorem exists_face_enumeration_monotone_card (K : PreAbstractSimplicialComplex ι)
    [Finite K.faces] :
    ∃ n : ℕ, ∃ e : Fin n ≃ K.faces, Monotone fun i => (e i).val.card := by
  classical
  let _ : Fintype K.faces := Fintype.ofFinite _
  let r : K.faces → K.faces → Prop := fun a b => a.val.card ≤ b.val.card
  let _ : Std.Total r := ⟨fun a b => le_total _ _⟩
  let _ : IsTrans K.faces r := ⟨fun _ _ _ h h' => h.trans h'⟩
  let _ : Std.Refl r := ⟨fun _ => le_rfl⟩
  let l := (Finset.univ : Finset K.faces).toList.mergeSort (r · ·)
  have hnd : l.Nodup := (Finset.nodup_toList _).mergeSort
  have hall (s : K.faces) : s ∈ l :=
    (List.mergeSort_perm _ _).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ s))
  let e := List.Nodup.getEquivOfForallMemList l hnd hall
  have hpair : l.Pairwise r := List.pairwise_mergeSort' r _
  exact ⟨l.length, e, fun _ _ h => hpair.rel_get_of_le h⟩

variable (K : PreAbstractSimplicialComplex ι) {n : ℕ} (e : Fin n ≃ K.faces)
  (he : Monotone fun i => (e i).val.card)

include he in
theorem index_lt_of_face_ssubset {s t : K.faces} (hst : s.val ⊂ t.val) :
    e.symm s < e.symm t := by
  by_contra h
  have hle := he (le_of_not_gt h)
  dsimp only at hle
  rw [e.apply_symm_apply, e.apply_symm_apply] at hle
  exact (Finset.card_lt_card hst).not_ge hle

def facePrefix (m : ℕ) : PreAbstractSimplicialComplex ι where
  faces := {s | ∃ i : Fin n, i.val < m ∧ (e i).val = s}
  isRelLowerSet_faces := by
    rintro s ⟨i, hi, rfl⟩
    refine ⟨(K.isRelLowerSet_faces (e i).property).1, ?_⟩
    intro t hts ht
    have htK : t ∈ K.faces := (K.isRelLowerSet_faces (e i).property).2 hts ht
    by_cases hti : t = (e i).val
    · exact ⟨i, hi, hti.symm⟩
    · have hlt := index_lt_of_face_ssubset K e he
        (s := ⟨t, htK⟩) (t := e i) (Finset.ssubset_iff_subset_ne.mpr ⟨hts, hti⟩)
      rw [e.symm_apply_apply] at hlt
      exact ⟨e.symm ⟨t, htK⟩, Nat.lt_trans hlt hi, congrArg Subtype.val (e.apply_symm_apply _)⟩

@[simp]
theorem mem_facePrefix_iff {m : ℕ} {s : Finset ι} :
    s ∈ (facePrefix K e he m).faces ↔ ∃ i : Fin n, i.val < m ∧ (e i).val = s := Iff.rfl

theorem facePrefix_le (m : ℕ) : facePrefix K e he m ≤ K := by
  rintro s ⟨i, _, rfl⟩
  exact (e i).property

@[simp]
theorem facePrefix_zero : facePrefix K e he 0 = ⊥ := by
  ext s
  simp only [mem_facePrefix_iff, not_lt_zero, false_and, exists_false]
  rfl

@[simp]
theorem facePrefix_last : facePrefix K e he n = K := by
  ext s
  constructor
  · intro hs
    exact facePrefix_le K e he n hs
  · intro hs
    exact ⟨e.symm ⟨s, hs⟩, (e.symm ⟨s, hs⟩).isLt, congrArg Subtype.val (e.apply_symm_apply _)⟩

theorem facePrefix_monotone : Monotone (facePrefix K e he) := by
  rintro i j hij s ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans_le hij, rfl⟩

theorem notMem_facePrefix_self (i : Fin n) : (e i).val ∉ (facePrefix K e he i.val).faces := by
  rintro ⟨j, hj, hji⟩
  have hij := congrArg Fin.val (e.injective (Subtype.ext hji))
  omega

theorem mem_facePrefix_of_ssubset (i : Fin n) {s : Finset ι}
    (hs : s.Nonempty) (hsi : s ⊂ (e i).val) : s ∈ (facePrefix K e he i.val).faces := by
  have hsK := (K.isRelLowerSet_faces (e i).property).2 hsi.le hs
  have hlt := index_lt_of_face_ssubset K e he (s := ⟨s, hsK⟩) (t := e i) hsi
  rw [e.symm_apply_apply] at hlt
  exact ⟨e.symm ⟨s, hsK⟩, hlt, congrArg Subtype.val (e.apply_symm_apply _)⟩

theorem card_le_of_mem_facePrefix (i : Fin n) {s : Finset ι}
    (hs : s ∈ (facePrefix K e he i.val).faces) : s.card ≤ (e i).val.card := by
  obtain ⟨j, hj, rfl⟩ := hs
  exact he hj.le

theorem facePrefix_succ_faces (i : Fin n) :
    (facePrefix K e he (i.val + 1)).faces = insert (e i).val (facePrefix K e he i.val).faces := by
  ext s
  constructor
  · rintro ⟨j, hj, hjs⟩
    by_cases hji : j = i
    · exact Or.inl (hjs.symm.trans (congrArg (fun k => (e k).val) hji))
    · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      exact Or.inr ⟨j, by omega, hjs⟩
  · rintro (rfl | ⟨j, hj, hjs⟩)
    · exact ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, hjs⟩

section Geometry

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  (K : Geometry.SimplicialComplex 𝕜 E) {n : ℕ} (e : Fin n ≃ K.faces)
  (he : Monotone fun i => (e i).val.card)

def geometricFacePrefix (m : ℕ) : Geometry.SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := facePrefix K.toPreAbstractSimplicialComplex e he m
  indep hs := K.indep (facePrefix_le K.toPreAbstractSimplicialComplex e he m hs)
  inter_subset_convexHull hs ht := K.inter_subset_convexHull
    (facePrefix_le K.toPreAbstractSimplicialComplex e he m hs)
    (facePrefix_le K.toPreAbstractSimplicialComplex e he m ht)

theorem geometricFacePrefix_faces (m : ℕ) :
    (geometricFacePrefix K e he m).faces =
      (facePrefix K.toPreAbstractSimplicialComplex e he m).faces :=
  rfl

theorem geometricFacePrefix_le (m : ℕ) : geometricFacePrefix K e he m ≤ K :=
  facePrefix_le K.toPreAbstractSimplicialComplex e he m

@[simp]
theorem geometricFacePrefix_last : geometricFacePrefix K e he n = K := by
  ext s
  change s ∈ (facePrefix K.toPreAbstractSimplicialComplex e he n).faces ↔ s ∈ K.faces
  rw [facePrefix_last]

end Geometry

end DifferentialGeometry.Topology.SimplicialComplex
