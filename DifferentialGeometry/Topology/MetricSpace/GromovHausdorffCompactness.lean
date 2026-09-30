import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology Cardinal
open Set Filter

namespace GromovHausdorff

universe u

private noncomputable def representativeIsometry (X : Type u) [MetricSpace X]
    [CompactSpace X] [Nonempty X] : X ≃ᵢ (toGHSpace X).Rep :=
  Classical.choice
    (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (GHSpace.toGHSpace_rep (toGHSpace X)).symm)

theorem totallyBounded_range_toGHSpace_of_uniform_finite_nets
    (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, Nonempty (X i)] {D : ℝ}
    (hdiam : ∀ i, Metric.diam (univ : Set (X i)) ≤ D)
    (hnets : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i : ℕ,
      ∃ S : Finset (X i), S.card ≤ N ∧ ∀ x : X i, ∃ y ∈ S, dist x y ≤ ε) :
    TotallyBounded (range fun i => toGHSpace (X i)) := by
  classical
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := by
    intro n
    dsimp [r]
    positivity
  choose K hK using fun n => hnets (r n / 2) (half_pos (hr n))
  apply GromovHausdorff.totallyBounded
    (u := r) (K := K) (C := D) tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro p ⟨i, rfl⟩
    let e := representativeIsometry (X i)
    calc
      Metric.diam (univ : Set (toGHSpace (X i)).Rep) =
          Metric.diam (range e) := congrArg Metric.diam e.range_eq_univ.symm
      _ = Metric.diam (univ : Set (X i)) := e.isometry.diam_range
      _ ≤ D := hdiam i
  · rintro p ⟨i, rfl⟩ n
    obtain ⟨S, hS, hcover⟩ := hK n i
    let e := representativeIsometry (X i)
    refine ⟨↑(S.image e), ?_, ?_⟩
    · rw [Finset.coe_sort_coe, Cardinal.mk_coe_finset, Nat.cast_le]
      exact Finset.card_image_le.trans hS
    · intro y _
      obtain ⟨x, hx, hdist⟩ := hcover (e.symm y)
      refine mem_iUnion.2 ⟨e x, mem_iUnion.2 ⟨Finset.mem_image_of_mem e hx, ?_⟩⟩
      change dist y (e x) < r n
      have heq : dist y (e x) = dist (e.symm y) x := by
        simpa using e.dist_eq (e.symm y) x
      rw [heq]
      exact hdist.trans_lt (half_lt_self (hr n))

theorem exists_subsequence_ghDist_tendsto_zero_of_uniform_finite_nets
    (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, Nonempty (X i)] {D : ℝ}
    (hdiam : ∀ i, Metric.diam (univ : Set (X i)) ≤ D)
    (hnets : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i : ℕ,
      ∃ S : Finset (X i), S.card ≤ N ∧ ∀ x : X i, ∃ y ∈ S, dist x y ≤ ε) :
    ∃ (φ : ℕ → ℕ) (p : GHSpace), StrictMono φ ∧
      Tendsto (fun j => ghDist (X (φ j)) p.Rep) atTop (𝓝 0) := by
  have ht := totallyBounded_range_toGHSpace_of_uniform_finite_nets X hdiam hnets
  have hc := ht.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨p, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun i => subset_closure (mem_range_self i))
  refine ⟨φ, p, hφ, ?_⟩
  have hdist := tendsto_iff_dist_tendsto_zero.mp hlim
  simpa [ghDist, GHSpace.toGHSpace_rep, Function.comp_def] using hdist

end GromovHausdorff
