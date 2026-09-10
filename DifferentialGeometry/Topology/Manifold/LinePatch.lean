import DifferentialGeometry.Topology.Manifold.BumpPartitionDerivative
import DifferentialGeometry.Topology.Combinatorics.LineMultiplicity

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace Poincare.Topology.Manifold

open Poincare.Topology.Combinatorics

open scoped Classical in
theorem mvfderiv_line_bump_partition_sum_pos
    {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    (f : BumpCovering (Fin (n + 1)) M)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)) (u : Fin (n + 1) → M → ℝ)
    (x : M) (hu : ∀ i, x ∈ tsupport (f i) → MDifferentiableAt I 𝓘(ℝ) (u i) x)
    (X : Fin (n + 1) → TangentSpace I x) (D δ κ : ℝ) (hδ : 0 ≤ δ)
    (hline : ∀ i, x ∈ tsupport (f i) → ∀ j, x ∈ tsupport (f j) → i.val ≤ j.val + 1)
    (hagree : ∀ j : Fin n, x ∈ tsupport (f j.castSucc) → x ∈ tsupport (f j.succ) →
      X j.succ = X j.castSucc)
    (hbumps : ∀ i, x ∈ tsupport (f i) → |mvfderiv I (f i) x (X i)| ≤ D)
    (hmain : ∀ i, x ∈ tsupport (f i) → κ ≤ mvfderiv I (u i) x (X i))
    (hoverlap : ∀ j : Fin n, x ∈ tsupport (f j.castSucc) → x ∈ tsupport (f j.succ) →
      |u j.succ x - u j.castSucc x| ≤ δ)
    (hsmall : 4 * D * δ < κ) (i : Fin (n + 1)) (hi : x ∈ tsupport (f i)) :
    0 < mvfderiv I (fun y ↦ ∑ j, f.toSmoothPartitionOfUnity hf j y * u j y) x (X i) := by
  classical
  have hX (j) (hj : x ∈ tsupport (f j)) : X j = X i := by
    rcases eq_or_adjacent_of_val_le_succ i j (hline i hi j hj) (hline j hj i hi) with
      rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · rfl
    · exact hagree k hi hj
    · exact (hagree k hj hi).symm
  apply mvfderiv_bump_partition_sum_pos_of_multiplicity f hf u x hu (X i) 2 D δ (u i x) κ
  · apply card_fin_le_two_of_pairwise_adjacent
    intro j hj k hk
    exact hline j (Finset.mem_filter.mp hj).2 k (Finset.mem_filter.mp hk).2
  · intro j hj
    rw [← hX j hj]
    exact hbumps j hj
  · intro j hj
    rw [← hX j hj]
    exact hmain j hj
  · intro j hj
    rcases eq_or_adjacent_of_val_le_succ i j (hline i hi j hj) (hline j hj i hi) with
      rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · simpa only [sub_self, abs_zero] using hδ
    · exact hoverlap k hi hj
    · rw [abs_sub_comm]
      exact hoverlap k hj hi
  · norm_num only [Nat.cast_ofNat, Nat.reducePow] at *
    exact hsmall

theorem contMDiff_and_mvfderiv_ne_zero_line_bump_partition
    {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    (f : BumpCovering (Fin (n + 1)) M)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)) (u : Fin (n + 1) → M → ℝ)
    (hu : ∀ i, ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ) ∞ (u i) x)
    (X : Fin (n + 1) → ∀ x : M, TangentSpace I x) (D δ κ : M → ℝ)
    (hδ : ∀ x, 0 ≤ δ x)
    (hline : ∀ x i, x ∈ tsupport (f i) → ∀ j, x ∈ tsupport (f j) → i.val ≤ j.val + 1)
    (hagree : ∀ j : Fin n, ∀ x ∈ tsupport (f j.castSucc), x ∈ tsupport (f j.succ) →
      X j.succ x = X j.castSucc x)
    (hbumps : ∀ i, ∀ x ∈ tsupport (f i), |mvfderiv I (f i) x (X i x)| ≤ D x)
    (hmain : ∀ i, ∀ x ∈ tsupport (f i), κ x ≤ mvfderiv I (u i) x (X i x))
    (hoverlap : ∀ j : Fin n, ∀ x ∈ tsupport (f j.castSucc), x ∈ tsupport (f j.succ) →
      |u j.succ x - u j.castSucc x| ≤ δ x)
    (hsmall : ∀ x, 4 * D x * δ x < κ x) :
    let v := fun x ↦ ∑ i, f.toSmoothPartitionOfUnity hf i x * u i x
    ContMDiff I 𝓘(ℝ) ∞ v ∧ ∀ x, mvfderiv I v x ≠ 0 := by
  classical
  let ρ := f.toSmoothPartitionOfUnity hf
  have hsub (i) : tsupport (ρ i) ⊆ tsupport (f i) :=
    closure_mono (f.support_toPartitionOfUnity_subset i)
  refine ⟨?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (fun i x hx ↦ hu i x (hsub i hx))
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using h
  · intro x hz
    let i := f.ind x (mem_univ x)
    have hi : x ∈ tsupport (f i) := subset_tsupport _ (by
      change f i x ≠ 0
      rw [f.ind_apply x (mem_univ x)]
      exact one_ne_zero)
    have hpos := mvfderiv_line_bump_partition_sum_pos f hf u x
      (fun j hj ↦ (hu j x hj).mdifferentiableAt (by decide))
      (fun j ↦ X j x) (D x) (δ x) (κ x) (hδ x) (hline x)
      (fun j ↦ hagree j x) (fun j ↦ hbumps j x) (fun j ↦ hmain j x)
      (fun j ↦ hoverlap j x) (hsmall x) i hi
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos

end Poincare.Topology.Manifold
