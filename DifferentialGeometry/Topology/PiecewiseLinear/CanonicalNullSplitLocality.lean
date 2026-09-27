/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceNullNormalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalNullSplit.unchanged_of_endpoint_nullTraceCount_eq_zero
    {S' T : ℤ → Set E3} {i j : ℤ}
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hstep : IsCanonicalNullSplit S' T i X Y)
    (hlo : nullTraceCount ((X (j - 1)).space ∪ (X j).space) (T (2 * j)) = 0)
    (hhi : nullTraceCount ((X j).space ∪ (X (j + 1)).space) (T (2 * (j + 1))) = 0) :
    Y j = X j := by
  apply hstep.unchanged
  · intro hji
    have hi : i = j + 1 := by omega
    have hlt := hstep.countLt
    rw [hi, add_sub_cancel_right, hhi] at hlt
    exact Nat.not_lt_zero _ hlt
  · intro hji
    have hlt := hstep.countLt
    rw [← hji, hlo] at hlt
    exact Nat.not_lt_zero _ hlt

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalNullSplit.nullTraceCount_eq_of_ne
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i k : ℤ}
    (hstep : IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y) (hki : k ≠ i) :
    nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) =
      nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
  apply nullTraceCount_eq_of_inter_eq
  apply htw.inter_even_of_sdiff_eq hki
  rw [union_sdiff_distrib, union_sdiff_distrib, hstep.outside (k - 1), hstep.outside k]

theorem IsCanonicalNullSplit.nullTraceCount_le
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}
    (hstep : IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y) (k : ℤ) :
    nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) ≤
      nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
  by_cases hki : k = i
  · exact hki ▸ hstep.countLt.le
  · exact (hstep.nullTraceCount_eq_of_ne htw hki).le

variable [DecidableEq E3] {a b : E3}

theorem IsCanonicalTower.nullTraceCount_le_of_null_splits
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} (window : Finset ℤ)
    (hpath : Relation.ReflTransGen (fun U V =>
      IsCanonicalSurface U (fun j => φ '' S j) T'' I P' a b ∧
      IsCanonicalSurface V (fun j => φ '' S j) T'' I P' a b ∧
      ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y)
    (k : ℤ) :
    nullTraceCount ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) ≤
      nullTraceCount ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) := by
  induction hpath with
  | refl => exact le_refl _
  | tail hpath hlast ih =>
    obtain ⟨-, -, i, -, hstep⟩ := hlast
    exact (hstep.nullTraceCount_le htw k).trans ih

theorem IsCanonicalTower.unchanged_of_endpoint_nullTraceCount_eq_zero_of_null_splits
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} (window : Finset ℤ)
    (hpath : Relation.ReflTransGen (fun U V =>
      IsCanonicalSurface U (fun j => φ '' S j) T'' I P' a b ∧
      IsCanonicalSurface V (fun j => φ '' S j) T'' I P' a b ∧
      ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y)
    (j : ℤ)
    (hlo : nullTraceCount ((X (j - 1)).space ∪ (X j).space) (T'' (2 * j)) = 0)
    (hhi : nullTraceCount ((X j).space ∪ (X (j + 1)).space) (T'' (2 * (j + 1))) = 0) :
    Y j = X j := by
  induction hpath with
  | refl => rfl
  | tail hpath hlast ih =>
    obtain ⟨-, -, i, -, hstep⟩ := hlast
    have hlo' := htw.nullTraceCount_le_of_null_splits window hpath j
    have hhi' := htw.nullTraceCount_le_of_null_splits window hpath (j + 1)
    rw [hlo, Nat.le_zero] at hlo'
    rw [add_sub_cancel_right, hhi, Nat.le_zero] at hhi'
    exact (hstep.unchanged_of_endpoint_nullTraceCount_eq_zero hlo' hhi').trans ih

end DifferentialGeometry.Topology.PiecewiseLinear
