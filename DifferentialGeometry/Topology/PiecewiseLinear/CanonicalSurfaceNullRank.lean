/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceTraceLocality

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalSurface.windowNullRank_pos_iff [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (h : IsCanonicalSurface X S' T I P' a b) (window : Finset ℤ) :
    0 < windowNullRank X T window ↔
      ∃ i ∈ window, ∃ G ∈ traceCircles ((X (i - 1)).space ∪ (X i).space) (T (2 * i)),
        boundsDiskIn G (T (2 * i)) := by
  classical
  simp only [Nat.pos_iff_ne_zero, ne_eq, h.windowNullRank_eq_zero_iff window,
    not_forall, not_not, exists_prop]

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.windowNullRank_lt_of_local_replacement
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ} {window : Finset ℤ}
    (hi : i ∈ window)
    (hout : ∀ j, (Y j).space \ interior (φ '' S (2 * i)) =
      (X j).space \ interior (φ '' S (2 * i)))
    (hlt : nullTraceCount ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)) <
      nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i))) :
    windowNullRank Y T'' window < windowNullRank X T'' window := by
  have hother (k : ℤ) (hki : k ≠ i) :
      nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) =
        nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
    apply nullTraceCount_eq_of_inter_eq
    apply htw.inter_even_of_sdiff_eq hki
    rw [union_sdiff_distrib, union_sdiff_distrib, hout (k - 1), hout k]
  unfold windowNullRank
  apply Finset.sum_lt_sum ?_ ⟨i, hi, hlt⟩
  intro k _
  by_cases hki : k = i
  · exact hki ▸ hlt.le
  · exact (hother k hki).le

end DifferentialGeometry.Topology.PiecewiseLinear
