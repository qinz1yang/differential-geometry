import DifferentialGeometry.Topology.Manifold.OrderedStepPartition
import DifferentialGeometry.Topology.Manifold.PartitionDerivative

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators

namespace Poincare.Topology.Manifold

private theorem sum_consecutive_sub_mul {n : ℕ} (a : Fin (n + 2) → ℝ)
    (b : Fin (n + 1) → ℝ) (hfirst : a 0 = 0) (hlast : a (Fin.last (n + 1)) = 0) :
    (∑ i : Fin (n + 1), (a i.castSucc - a i.succ) * b i) =
      ∑ j : Fin n, a j.succ.castSucc * (b j.succ - b j.castSucc) := by
  have hleft := Fin.sum_univ_succ (fun i : Fin (n + 1) ↦ a i.castSucc * b i)
  have hright := Fin.sum_univ_castSucc (fun i : Fin (n + 1) ↦ a i.succ * b i)
  simp only [Fin.castSucc_zero, hfirst, zero_mul, zero_add] at hleft
  simp only [Fin.succ_last, hlast, zero_mul, add_zero] at hright
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hleft, hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.succ_castSucc]
  ring

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mvfderiv_orderedStepPartition_sum
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ) (x : M)
    (hu : ∀ i, x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i) →
      MDifferentiableAt I 𝓘(ℝ) (u i) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ∑ i, orderedStepPartition θ horder hfirst hlast i y * u i y) x v =
      (∑ i, orderedStepPartition θ horder hfirst hlast i x * mvfderiv I (u i) x v) +
      ∑ j : Fin n, mvfderiv I (θ j.succ.castSucc) x v * (u j.succ x - u j.castSucc x) := by
  rw [mvfderiv_partition_sum (orderedStepPartition θ horder hfirst hlast) u x hu v 0]
  simp only [sub_zero]
  congr 1
  have hzero₀ : mvfderiv I (θ 0) x v = 0 := by
    have hfun : (θ 0 : M → ℝ) = fun _ ↦ 1 := funext hfirst
    rw [hfun, mvfderiv_const, zero_apply]
  have hzero₁ : mvfderiv I (θ (Fin.last (n + 1))) x v = 0 := by
    have hfun : (θ (Fin.last (n + 1)) : M → ℝ) = fun _ ↦ 0 := funext hlast
    rw [hfun, mvfderiv_const, zero_apply]
  calc
    _ = ∑ i : Fin (n + 1),
        (mvfderiv I (θ i.castSucc) x v - mvfderiv I (θ i.succ) x v) * u i x := by
      apply Finset.sum_congr rfl
      intro i _
      change mvfderiv I (fun y ↦ θ i.castSucc y - θ i.succ y) x v * u i x = _
      rw [mvfderiv_fun_sub ((θ i.castSucc).contMDiff.mdifferentiable (by decide) x)
        ((θ i.succ).contMDiff.mdifferentiable (by decide) x), sub_apply]
    _ = _ := sum_consecutive_sub_mul (fun j ↦ mvfderiv I (θ j) x v)
      (fun i ↦ u i x) hzero₀ hzero₁

theorem abs_mvfderiv_orderedStepPartition_sum_sub_le_of_pairwiseDisjoint
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ) (x : M)
    (hu : ∀ i, x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i) →
      MDifferentiableAt I 𝓘(ℝ) (u i) x) (v : TangentSpace I x)
    (K : Fin n → Set M) (hdisjoint : Pairwise (fun i j ↦ Disjoint (K i) (K j)))
    (hzero : ∀ j, x ∉ K j → mvfderiv I (θ j.succ.castSucc) x v = 0)
    (D δ : ℝ) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hstep : ∀ j, x ∈ K j → |mvfderiv I (θ j.succ.castSucc) x v| ≤ D)
    (hclose : ∀ j, x ∈ K j → |u j.succ x - u j.castSucc x| ≤ δ) :
    |mvfderiv I (fun y ↦ ∑ i, orderedStepPartition θ horder hfirst hlast i y * u i y) x v -
      (∑ i, orderedStepPartition θ horder hfirst hlast i x * mvfderiv I (u i) x v)| ≤ D * δ := by
  classical
  rw [mvfderiv_orderedStepPartition_sum θ horder hfirst hlast u x hu v, add_sub_cancel_left]
  by_cases hx : ∃ j, x ∈ K j
  · obtain ⟨j, hj⟩ := hx
    have hnot (k : Fin n) (hk : k ≠ j) : x ∉ K k := by
      intro hxk
      exact Set.disjoint_left.mp (hdisjoint hk) hxk hj
    rw [Finset.sum_eq_single j (by
      intro k _ hk
      rw [hzero k (hnot k hk), zero_mul]) (by simp), abs_mul]
    exact mul_le_mul (hstep j hj) (hclose j hj) (abs_nonneg _) hD
  · have hnot : ∀ j, x ∉ K j := by simpa only [not_exists] using hx
    simp only [hzero _ (hnot _), zero_mul, Finset.sum_const_zero, abs_zero]
    exact mul_nonneg hD hδ

theorem mvfderiv_orderedStepPartition_sum_pos_of_pairwiseDisjoint
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (u : Fin (n + 1) → M → ℝ) (x : M)
    (hu : ∀ i, x ∈ tsupport (orderedStepPartition θ horder hfirst hlast i) →
      MDifferentiableAt I 𝓘(ℝ) (u i) x) (v : TangentSpace I x)
    (K : Fin n → Set M) (hdisjoint : Pairwise (fun i j ↦ Disjoint (K i) (K j)))
    (hzero : ∀ j, x ∉ K j → mvfderiv I (θ j.succ.castSucc) x v = 0)
    (D δ κ : ℝ) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hstep : ∀ j, x ∈ K j → |mvfderiv I (θ j.succ.castSucc) x v| ≤ D)
    (hclose : ∀ j, x ∈ K j → |u j.succ x - u j.castSucc x| ≤ δ)
    (hmain : ∀ i, orderedStepPartition θ horder hfirst hlast i x ≠ 0 →
      κ ≤ mvfderiv I (u i) x v) (hsmall : D * δ < κ) :
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
  have herr := abs_mvfderiv_orderedStepPartition_sum_sub_le_of_pairwiseDisjoint
    θ horder hfirst hlast u x hu v K hdisjoint hzero D δ hD hδ hstep hclose
  have hneg := neg_abs_le (mvfderiv I (fun y ↦ ∑ i, ρ i y * u i y) x v -
    (∑ i, ρ i x * mvfderiv I (u i) x v))
  change |mvfderiv I (fun y ↦ ∑ i, ρ i y * u i y) x v -
    (∑ i, ρ i x * mvfderiv I (u i) x v)| ≤ D * δ at herr
  linarith only [hmain', herr, hneg, hsmall]

end Poincare.Topology.Manifold
