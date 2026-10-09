/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTube.isCompact_closure_interior_pair
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {u v : E3}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) :
    IsCompact (closure (interior (h '' C u ∪ h '' C v))) := by
  have hCu := (ht.dualBall u hu).isPolyhedron.isCompact.image_of_continuousOn
    (ht.continuousOn.mono (ht.dualCell_subset hu))
  have hCv := (ht.dualBall v hv).isPolyhedron.isCompact.image_of_continuousOn
    (ht.continuousOn.mono (ht.dualCell_subset hv))
  have hpair := hCu.union hCv
  exact hpair.of_isClosed_subset isClosed_closure
    (closure_minimal interior_subset hpair.isClosed)

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.iInter_closure_upper_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    (⋂ m : ℤ, closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i)) = Dbdimg := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxrim
    have hmem (m : ℤ) : x ∈ ⋃ i, ⋃ (_ : m ≤ i), φ '' S i := by
      have hm := mem_iInter.mp hx m
      rw [htw.closureUpper] at hm
      exact hm.resolve_right hxrim
    obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp (hmem 0)
    obtain ⟨j, hij, hxj⟩ := mem_iUnion₂.mp (hmem (i + 2))
    exact Set.disjoint_left.mp (htw.apart i j (by
      have h := neg_le_abs (i - j)
      omega)) hxi hxj
  · intro x hx
    apply mem_iInter.mpr
    intro m
    rw [htw.closureUpper]
    exact Or.inr hx

theorem IsCanonicalTower.iInter_closure_lower_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    (⋂ m : ℤ, closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i)) = {P'} := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxcenter
    have hmem (m : ℤ) : x ∈ ⋃ i, ⋃ (_ : i ≤ m), φ '' S i := by
      have hm := mem_iInter.mp hx m
      rw [htw.closureLower] at hm
      exact hm.resolve_right hxcenter
    obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp (hmem 0)
    obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp (hmem (i - 2))
    exact Set.disjoint_left.mp (htw.apart i j (by
      have h := le_abs_self (i - j)
      omega)) hxi hxj
  · intro x hx
    apply mem_iInter.mpr
    intro m
    rw [htw.closureLower]
    exact Or.inr hx

theorem IsCanonicalTower.exists_upper_tail_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsCompact (closure I)) {U : Set E3} (hU : IsOpen U) (hrim : Dbdimg ⊆ U) :
    ∃ m : ℤ, ∀ i, m ≤ i → φ '' S i ⊆ U := by
  have hempty : (closure I \ U) ∩
      (⋂ m : ℤ, closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i)) = ∅ := by
    rw [htw.iInter_closure_upper_eq]
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.1.2 (hrim hx.2)
  have hdir : Directed (· ⊇ ·)
      (fun m : ℤ => closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i)) := by
    intro m n
    refine ⟨max m n, closure_mono ?_, closure_mono ?_⟩
    · exact iUnion₂_mono' fun i hi => ⟨i, (le_max_left m n).trans hi, subset_rfl⟩
    · exact iUnion₂_mono' fun i hi => ⟨i, (le_max_right m n).trans hi, subset_rfl⟩
  obtain ⟨m, hm⟩ := (hI.inter_right hU.isClosed_compl).elim_directed_family_closed
    (fun m : ℤ => closure (⋃ i, ⋃ (_ : m ≤ i), φ '' S i))
    (fun _ => isClosed_closure) (Set.disjoint_iff_inter_eq_empty.mpr hempty) hdir
  refine ⟨m, fun i hi x hx => ?_⟩
  by_contra hxU
  have hxmem : x ∈ (closure I \ U) ∩ closure (⋃ j, ⋃ (_ : m ≤ j), φ '' S j) :=
    ⟨⟨subset_closure (htw.subsetInterior i hx), hxU⟩,
      subset_closure (mem_iUnion₂.mpr ⟨i, hi, hx⟩)⟩
  exact Set.disjoint_left.mp hm hxmem.1 hxmem.2

theorem IsCanonicalTower.exists_lower_tail_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsCompact (closure I)) {U : Set E3} (hU : IsOpen U) (hP : P' ∈ U) :
    ∃ m : ℤ, ∀ i, i ≤ m → φ '' S i ⊆ U := by
  have hempty : (closure I \ U) ∩
      (⋂ m : ℤ, closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i)) = ∅ := by
    rw [htw.iInter_closure_lower_eq]
    exact eq_empty_iff_forall_notMem.mpr fun x hx =>
      hx.1.2 (mem_singleton_iff.mp hx.2 ▸ hP)
  have hdir : Directed (· ⊇ ·)
      (fun m : ℤ => closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i)) := by
    intro m n
    refine ⟨min m n, closure_mono ?_, closure_mono ?_⟩
    · exact iUnion₂_mono' fun i hi => ⟨i, hi.trans (min_le_left m n), subset_rfl⟩
    · exact iUnion₂_mono' fun i hi => ⟨i, hi.trans (min_le_right m n), subset_rfl⟩
  obtain ⟨m, hm⟩ := (hI.inter_right hU.isClosed_compl).elim_directed_family_closed
    (fun m : ℤ => closure (⋃ i, ⋃ (_ : i ≤ m), φ '' S i))
    (fun _ => isClosed_closure) (Set.disjoint_iff_inter_eq_empty.mpr hempty) hdir
  refine ⟨m, fun i hi x hx => ?_⟩
  by_contra hxU
  have hxmem : x ∈ (closure I \ U) ∩ closure (⋃ j, ⋃ (_ : j ≤ m), φ '' S j) :=
    ⟨⟨subset_closure (htw.subsetInterior i hx), hxU⟩,
      subset_closure (mem_iUnion₂.mpr ⟨i, hi, hx⟩)⟩
  exact Set.disjoint_left.mp hm hxmem.1 hxmem.2

end DifferentialGeometry.Topology.PiecewiseLinear
