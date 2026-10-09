/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeNormalizationSequence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem mem_neg_natCast_pair_iff (i : ℤ) (n : ℕ) :
    i ∈ ({-(n : ℤ), (n : ℤ)} : Finset ℤ) ↔ i.natAbs = n := by
  simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm] using
    (Int.natAbs_eq_iff (a := i) (n := n)).symm

variable [DecidableEq E3]
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}
  {X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3}

theorem IsCanonicalTower.nullTraceCount_antitone_of_bridge_normalizations
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {rows : ℕ → Finset ℤ} {F : ℕ → Set E3}
    (hstep : ∀ n, IsCanonicalBridgeNormalization (X n) (X (n + 1))
      (fun j => φ '' S j) S'' T'' I P' a b (rows n) (F n)) (k : ℤ) :
    Antitone (fun n =>
      nullTraceCount ((X n (k - 1)).space ∪ (X n k).space) (T'' (2 * k))) :=
  antitone_nat_of_succ_le fun n => (hstep n).nullTraceCount_le htw k

theorem IsCanonicalTower.endpoint_nullTraceCount_eq_zero_of_bridge_normalizations
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {F : ℕ → Set E3}
    (hstep : ∀ n, IsCanonicalBridgeNormalization (X n) (X (n + 1))
      (fun j => φ '' S j) S'' T'' I P' a b {-(n : ℤ), (n : ℤ)} (F n))
    (i : ℤ) {n : ℕ} (hn : i.natAbs + 1 ≤ n) :
    nullTraceCount ((X n (i - 1)).space ∪ (X n i).space) (T'' (2 * i)) = 0 ∧
      nullTraceCount ((X n i).space ∪ (X n (i + 1)).space) (T'' (2 * (i + 1))) = 0 := by
  have hi : i ∈ ({-(i.natAbs : ℤ), (i.natAbs : ℤ)} : Finset ℤ) :=
    (mem_neg_natCast_pair_iff i i.natAbs).mpr rfl
  have hz := (hstep i.natAbs).target.nullRank
  unfold windowNullRank at hz
  have hlo := (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_union_left _ hi)
  have hhi := (Finset.sum_eq_zero_iff.mp hz) (i + 1)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hloLE := htw.nullTraceCount_antitone_of_bridge_normalizations hstep i hn
  have hhiLE := htw.nullTraceCount_antitone_of_bridge_normalizations hstep (i + 1) hn
  refine ⟨Nat.eq_zero_of_le_zero (hloLE.trans_eq hlo), ?_⟩
  simpa only [add_sub_cancel_right] using Nat.eq_zero_of_le_zero (hhiLE.trans_eq hhi)

theorem IsCanonicalTower.row_eq_of_bridge_normalizations
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {F : ℕ → Set E3}
    (hstep : ∀ n, IsCanonicalBridgeNormalization (X n) (X (n + 1))
      (fun j => φ '' S j) S'' T'' I P' a b {-(n : ℤ), (n : ℤ)} (F n))
    (i : ℤ) {n : ℕ} (hn : i.natAbs + 1 ≤ n) :
    X n i = X (i.natAbs + 1) i := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    obtain ⟨hlo, hhi⟩ :=
      htw.endpoint_nullTraceCount_eq_zero_of_bridge_normalizations hstep i hn
    have hi : i ∉ ({-(n : ℤ), (n : ℤ)} : Finset ℤ) := by
      rw [mem_neg_natCast_pair_iff]
      omega
    exact ((hstep n).unchanged_of_endpoint_nullTraceCount_eq_zero htw i hi hlo hhi).trans ih

end DifferentialGeometry.Topology.PiecewiseLinear
