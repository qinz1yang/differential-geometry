import DifferentialGeometry.Topology.Manifold.CollarPartitionPatch

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators

namespace Poincare.Topology.Manifold

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem abs_mvfderiv_orderedStepPartition_sum_sub_le_of_local_products
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ) (x : M)
    (hu : ∀ i, x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i) →
      MDifferentiableAt I 𝓘(ℝ) (u i) x) (v : TangentSpace I x)
    (K : Fin n → Set M) (hdisjoint : Pairwise (fun i j ↦ Disjoint (K i) (K j)))
    (hzero : ∀ j, x ∉ K j → mvfderiv I (θ j.succ.castSucc) x v = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hproduct : ∀ j, x ∈ K j →
      |mvfderiv I (θ j.succ.castSucc) x v| * |u j.succ x - u j.castSucc x| ≤ B) :
    |mvfderiv I (fun y ↦ ∑ i, orderedStepPartition θ horder hfirst hlast i y * u i y) x v -
      (∑ i, orderedStepPartition θ horder hfirst hlast i x * mvfderiv I (u i) x v)| ≤ B := by
  classical
  rw [mvfderiv_orderedStepPartition_sum θ horder hfirst hlast u x hu v, add_sub_cancel_left]
  by_cases hx : ∃ j, x ∈ K j
  · obtain ⟨j, hj⟩ := hx
    have hnot (k : Fin n) (hk : k ≠ j) : x ∉ K k :=
      fun hxk ↦ Set.disjoint_left.mp (hdisjoint hk) hxk hj
    rw [Finset.sum_eq_single j (by
      intro k _ hk
      rw [hzero k (hnot k hk), zero_mul]) (by simp), abs_mul]
    exact hproduct j hj
  · have hnot : ∀ j, x ∉ K j := by simpa only [not_exists] using hx
    simpa only [hzero _ (hnot _), zero_mul, Finset.sum_const_zero, abs_zero] using hB

theorem mvfderiv_orderedStepPartition_sum_pos_of_local_products
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ) (x : M)
    (hu : ∀ i, x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i) →
      MDifferentiableAt I 𝓘(ℝ) (u i) x) (v : TangentSpace I x)
    (K : Fin n → Set M) (hdisjoint : Pairwise (fun i j ↦ Disjoint (K i) (K j)))
    (hzero : ∀ j, x ∉ K j → mvfderiv I (θ j.succ.castSucc) x v = 0)
    (B κ : ℝ) (hB : 0 ≤ B)
    (hproduct : ∀ j, x ∈ K j →
      |mvfderiv I (θ j.succ.castSucc) x v| * |u j.succ x - u j.castSucc x| ≤ B)
    (hmain : ∀ i, orderedStepPartition θ horder hfirst hlast i x ≠ 0 →
      κ ≤ mvfderiv I (u i) x v) (hsmall : B < κ) :
    0 < mvfderiv I (fun y ↦ ∑ i, orderedStepPartition θ horder hfirst hlast i y * u i y) x v := by
  let ρ := orderedStepPartition θ horder hfirst hlast
  have hsum : ∑ i, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  have hmain' : κ ≤ ∑ i, ρ i x * mvfderiv I (u i) x v := by
    calc
      κ = (∑ i, ρ i x) * κ := by rw [hsum, one_mul]
      _ = ∑ i, ρ i x * κ := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum (by
        intro i _
        by_cases hi : ρ i x = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hmain i hi) (ρ.nonneg i x))
  have herr := abs_mvfderiv_orderedStepPartition_sum_sub_le_of_local_products
    θ horder hfirst hlast u x hu v K hdisjoint hzero B hB hproduct
  have hneg := neg_abs_le (mvfderiv I (fun y ↦ ∑ i, ρ i y * u i y) x v -
    (∑ i, ρ i x * mvfderiv I (u i) x v))
  change |mvfderiv I (fun y ↦ ∑ i, ρ i y * u i y) x v -
    (∑ i, ρ i x * mvfderiv I (u i) x v)| ≤ B at herr
  linarith only [hmain', herr, hneg, hsmall]

end Poincare.Topology.Manifold
