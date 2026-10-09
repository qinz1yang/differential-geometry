/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeNormalization
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalNullSplitLocality
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSingleBridgeRows

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X Y : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I F : Set E3} {P' a b : E3} {rows : Finset ℤ}

theorem IsCanonicalBridgeNormalization.nullTraceCount_le
    (hn : IsCanonicalBridgeNormalization X Y (fun j => φ '' S j) S'' T'' I P' a b rows F)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (k : ℤ) :
    nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) ≤
      nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
  obtain ⟨U, V, Z, hclass, hclosed, hreturn, hbridge⟩ := hn.stages
  have h₀ := htw.nullTraceCount_le_of_null_splits (towerWindowSeams rows) hclass.splits k
  have h₁ := hclosed.nullRankEq {k}
  have h₂ := hreturn.nullRankLE {k}
  have h₃ := hbridge.nullRankLE {k}
  simp only [windowNullRank, Finset.sum_singleton] at h₁ h₂ h₃
  exact h₃.trans (h₂.trans (h₁.le.trans h₀))

theorem IsCanonicalBridgeNormalization.unchanged_of_endpoint_nullTraceCount_eq_zero
    (hn : IsCanonicalBridgeNormalization X Y (fun j => φ '' S j) S'' T'' I P' a b rows F)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (hi : i ∉ rows)
    (hlo : nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)) = 0)
    (hhi : nullTraceCount ((X i).space ∪ (X (i + 1)).space) (T'' (2 * (i + 1))) = 0) :
    Y i = X i := by
  obtain ⟨U, V, Z, hclass, hclosed, hreturn, hbridge⟩ := hn.stages
  exact (hbridge.unchanged i hi).trans ((hreturn.unchanged i hi).trans
    ((hclosed.unchanged i hi).trans
      (htw.unchanged_of_endpoint_nullTraceCount_eq_zero_of_null_splits
        (towerWindowSeams rows) hclass.splits i hlo hhi)))

theorem IsCanonicalBridgeNormalization.exists_row_annulus
    (hn : IsCanonicalBridgeNormalization X Y (fun j => φ '' S j) S'' T'' I P' a b rows F)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) (hi : i ∈ rows) :
    ∃ J₀ J₁ : Set E3, IsPLAnnulusWithEnds (Y i).space J₀ J₁ ∧ Disjoint J₀ J₁ ∧
      J₀ ∈ traceCircles (Y i).space (T'' (2 * i)) ∧
      J₁ ∈ traceCircles (Y i).space (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn J₀ (T'' (2 * i)) ∧ ¬ boundsDiskIn J₁ (T'' (2 * (i + 1))) ∧
      (Y i).space ∩ T'' (2 * i) = J₀ ∧ (Y i).space ∩ T'' (2 * (i + 1)) = J₁ := by
  obtain ⟨U, V, Z, -, -, -, hbridge⟩ := hn.stages
  exact hbridge.exists_row_annulus htw h314 i hi

end DifferentialGeometry.Topology.PiecewiseLinear
