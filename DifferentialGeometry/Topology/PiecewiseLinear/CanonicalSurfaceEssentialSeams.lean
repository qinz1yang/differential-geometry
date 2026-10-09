/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeamGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerNullSeamDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {S' T : ℤ → Set E3} {I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.traceCircles_adjacent_eq
    (h : IsCanonicalSurface X S' T I P' a b) (i : ℤ) :
    traceCircles ((X (i - 1)).space ∪ (X i).space) (T (2 * i)) =
      traceCircles (X (i - 1)).space (T (2 * i)) ∪ traceCircles (X i).space (T (2 * i)) := by
  have hleft : HasFiniteCollaredTrace (X (i - 1)).space (T (2 * i)) := by
    simpa only [sub_add_cancel] using h.upperTrace (i - 1)
  exact traceCircles_eq_union_of_disjoint hleft.finiteTrace (h.lowerTrace i).finiteTrace
    hleft.traceCover (h.lowerTrace i).traceCover (h.piecesDisjoint (by omega))

theorem IsCanonicalSurface.adjacent_trace_subset_evenTorusSeams
    (h : IsCanonicalSurface X S' T I P' a b) (i : ℤ) :
    traceCircles ((X (i - 1)).space ∪ (X i).space) (T (2 * i)) ⊆ evenTorusSeams T i := by
  rw [h.traceCircles_adjacent_eq i]
  intro G hG
  rcases hG with hleft | hright
  · left
    have hG' : G ∈ traceCircles (X (i - 1)).space (T (2 * ((i - 1) + 1))) := by
      simpa only [sub_add_cancel] using hleft
    simpa only [sub_add_cancel, show 2 * (i - 1) + 1 = 2 * i - 1 by omega] using
      h.upperOrigin (i - 1) hG'
  · right
    simpa only [traceCircles, inter_comm] using h.lowerOrigin i hright

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T'' S'' : ℤ → Set E3}
  {Dimg Dbdimg W : Set E3}

theorem IsCanonicalSurface.seam_generators_of_nullTraceCount_eq_zero
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ)
    (hzero : nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)) = 0) :
    ∀ G ∈ traceCircles ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)),
      ∀ hsub : G ⊆ S'' (2 * i), ∀ x : G,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' (2 * i))) x) :=
  htw.traceCircles_generators_of_nullTraceCount_eq_zero h314 i
    (h.adjacentTrace i).finiteTrace (h.adjacent_trace_subset_evenTorusSeams i) hzero

theorem IsCanonicalSurface.lower_seam_not_boundsDiskIn
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ)
    (hzero : nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)) = 0)
    {G : Set E3} (hG : G ∈ traceCircles (X i).space (T'' (2 * i))) :
    ¬ boundsDiskIn G (T'' (2 * i + 1)) := by
  have hnot := (nullTraceCount_eq_zero_iff (h.adjacentTrace i).finiteTrace).mp hzero
  have hGwhole := (h.traceCircles_adjacent_eq i).symm.subset (Or.inr hG)
  have horig : G ∈ traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) := by
    simpa only [traceCircles, inter_comm] using h.lowerOrigin i hG
  intro hbound
  exact hnot G hGwhole ((htw.boundsDiskIn_iff h314 (2 * i) horig).mpr hbound)

theorem IsCanonicalSurface.upper_seam_not_boundsDiskIn
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ)
    (hzero : nullTraceCount ((X i).space ∪ (X (i + 1)).space) (T'' (2 * (i + 1))) = 0)
    {G : Set E3} (hG : G ∈ traceCircles (X i).space (T'' (2 * (i + 1)))) :
    ¬ boundsDiskIn G (T'' (2 * i + 1)) := by
  have hfin : (traceCircles ((X i).space ∪ (X (i + 1)).space)
      (T'' (2 * (i + 1)))).Finite := by
    simpa only [add_sub_cancel_right] using (h.adjacentTrace (i + 1)).finiteTrace
  have hnot := (nullTraceCount_eq_zero_iff hfin).mp hzero
  have hGwhole : G ∈ traceCircles ((X i).space ∪ (X (i + 1)).space)
      (T'' (2 * (i + 1))) := by
    have hleft : G ∈ traceCircles (X ((i + 1) - 1)).space (T'' (2 * (i + 1))) := by
      simpa only [add_sub_cancel_right] using hG
    simpa only [add_sub_cancel_right] using
      (h.traceCircles_adjacent_eq (i + 1)).symm.subset (Or.inl hleft)
  have horig : G ∈ traceCircles (T'' (2 * i + 1)) (T'' ((2 * i + 1) + 1)) := by
    simpa only [show (2 * i + 1) + 1 = 2 * (i + 1) by omega] using h.upperOrigin i hG
  intro hbound
  exact hnot G hGwhole (by
    simpa only [show (2 * i + 1) + 1 = 2 * (i + 1) by omega] using
      (htw.boundsDiskIn_iff h314 (2 * i + 1) horig).mp hbound)

end DifferentialGeometry.Topology.PiecewiseLinear
