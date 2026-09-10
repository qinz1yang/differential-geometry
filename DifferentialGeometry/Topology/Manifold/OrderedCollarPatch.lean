import DifferentialGeometry.Topology.Manifold.CollarPartitionError
import DifferentialGeometry.Topology.Combinatorics.LineMultiplicity

noncomputable section
open Set Topology
open scoped Manifold ContDiff BigOperators

namespace Poincare.Topology.Manifold

theorem contMDiff_and_mvfderiv_ne_zero_ordered_collar_partition
    {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ)
    (hu : ∀ i, ∀ x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i),
      ContMDiffAt I 𝓘(ℝ) ∞ (u i) x)
    (X : Fin (n + 1) → ∀ x : M, TangentSpace I x)
    (K : Fin n → Set M) (hdisjoint : Pairwise (fun i j ↦ Disjoint (K i) (K j)))
    (hnonadjacent : ∀ i j : Fin (n + 1), i.val + 1 < j.val →
      Disjoint (tsupport (orderedStepPartition θ horder hfirst hlast i))
        (tsupport (orderedStepPartition θ horder hfirst hlast j)))
    (hintersection : ∀ j : Fin n,
      tsupport (orderedStepPartition θ horder hfirst hlast j.castSucc) ∩
        tsupport (orderedStepPartition θ horder hfirst hlast j.succ) ⊆ K j)
    (hactive : ∀ j : Fin n, ∀ x ∈ K j, ∀ i : Fin (n + 1),
      orderedStepPartition θ horder hfirst hlast i x ≠ 0 → i = j.castSucc ∨ i = j.succ)
    (hzero : ∀ j x, x ∉ K j → mvfderiv I (θ j.succ.castSucc) x = 0)
    (hagree : ∀ j x, x ∈ K j → X j.succ x = X j.castSucc x)
    (B κ : M → ℝ) (hB : ∀ x, 0 ≤ B x)
    (hproduct : ∀ j x, x ∈ K j →
      |mvfderiv I (θ j.succ.castSucc) x (X j.castSucc x)| *
        |u j.succ x - u j.castSucc x| ≤ B x)
    (hmain : ∀ i, ∀ x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i),
      κ x ≤ mvfderiv I (u i) x (X i x))
    (hsmall : ∀ x, B x < κ x) :
    let v := fun x ↦ ∑ i, orderedStepPartition θ horder hfirst hlast i x * u i x
    ContMDiff I 𝓘(ℝ) ∞ v ∧ ∀ x, mvfderiv I v x ≠ 0 := by
  classical
  let ρ := orderedStepPartition θ horder hfirst hlast
  refine ⟨?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul hu
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using h
  · intro x hz
    obtain ⟨i, hi⟩ := ρ.toPartitionOfUnity.exists_pos (mem_univ x)
    have hi' : ρ i x ≠ 0 := ne_of_gt hi
    have hisupp : x ∈ tsupport (ρ i) := subset_tsupport _ hi'
    have hline (j k : Fin (n + 1)) (hj : x ∈ tsupport (ρ j))
        (hk : x ∈ tsupport (ρ k)) : j.val ≤ k.val + 1 := by
      by_contra h
      exact Set.disjoint_left.mp (hnonadjacent k j (not_le.mp h)) hk hj
    have hX (j : Fin (n + 1)) (hj : x ∈ tsupport (ρ j)) : X j x = X i x := by
      rcases Poincare.Topology.Combinatorics.eq_or_adjacent_of_val_le_succ i j
        (hline i j hisupp hj) (hline j i hj hisupp) with
        rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
      · rfl
      · exact hagree k x (hintersection k ⟨hisupp, hj⟩)
      · exact (hagree k x (hintersection k ⟨hj, hisupp⟩)).symm
    have hpos := mvfderiv_orderedStepPartition_sum_pos_of_local_products
      θ horder hfirst hlast u x
      (fun j hj ↦ (hu j x hj).mdifferentiableAt (by decide)) (X i x)
      K hdisjoint (fun j hj ↦ by rw [hzero j x hj]; rfl) (B x) (κ x) (hB x)
      (fun j hj ↦ by
        have hXi : X i x = X j.castSucc x := by
          rcases hactive j x hj i hi' with rfl | rfl
          · rfl
          · exact hagree j x hj
        rw [hXi]
        exact hproduct j x hj)
      (fun j hj ↦ by
        have hjsupp : x ∈ tsupport (ρ j) := subset_tsupport _ hj
        rw [← hX j hjsupp]
        exact hmain j x hjsupp)
      (hsmall x)
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos

end Poincare.Topology.Manifold
