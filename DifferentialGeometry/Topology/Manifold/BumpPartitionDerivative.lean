import DifferentialGeometry.Topology.Manifold.PartitionWeightEstimate
import DifferentialGeometry.Topology.Manifold.PartitionDerivative

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace DifferentialGeometry.Topology.Manifold

open scoped Classical in
theorem mvfderiv_bump_partition_sum_pos_of_multiplicity
    {ι : Type} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [Fintype ι]
    (f : BumpCovering ι M) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i))
    (g : ι → M → ℝ) (x : M)
    (hg : ∀ i, x ∈ tsupport (f i) → MDifferentiableAt I 𝓘(ℝ) (g i) x)
    (v : TangentSpace I x) (N : ℕ) (D δ c κ : ℝ)
    (hcard : (Finset.univ.filter (fun i ↦ x ∈ tsupport (f i))).card ≤ N)
    (hbumps : ∀ i, x ∈ tsupport (f i) → |mvfderiv I (f i) x v| ≤ D)
    (hmain : ∀ i, x ∈ tsupport (f i) → κ ≤ mvfderiv I (g i) x v)
    (hoverlap : ∀ i, x ∈ tsupport (f i) → |g i x - c| ≤ δ)
    (hsmall : (N : ℝ) ^ 2 * D * δ < κ) :
    0 < mvfderiv I (fun y ↦ ∑ i, f.toSmoothPartitionOfUnity hf i y * g i y) x v := by
  classical
  let ρ := f.toSmoothPartitionOfUnity hf
  have hsub (i : ι) : tsupport (ρ i) ⊆ tsupport (f i) :=
    closure_mono (f.support_toPartitionOfUnity_subset i)
  have hδ : 0 ≤ δ := by
    let i := f.ind x (mem_univ x)
    have hi : x ∈ tsupport (f i) := subset_tsupport _ (by
      change f i x ≠ 0
      rw [f.ind_apply x (mem_univ x)]
      exact one_ne_zero)
    exact (abs_nonneg _).trans (hoverlap i hi)
  have hsum : (∑ i, |mvfderiv I (ρ i) x v|) ≤ (N : ℝ) ^ 2 * D :=
    sum_abs_mvfderiv_bump_partition_le_multiplicity f x
      (fun i ↦ (hf i).mdifferentiable (by simp) x) v N D hcard hbumps
  apply mvfderiv_partition_sum_pos_of_error_lt ρ g x (fun i hi ↦ hg i (hsub i hi)) v c κ
    (fun i hi ↦ hmain i (hsub i (subset_tsupport _ hi)))
  calc
    _ ≤ ∑ i, |mvfderiv I (ρ i) x v| * δ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x ∈ tsupport (f i)
      · exact mul_le_mul_of_nonneg_left (hoverlap i hi) (abs_nonneg _)
      · have hnot : x ∉ tsupport (ρ i) := fun h ↦ hi (hsub i h)
        have hz : (ρ i : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ 0 :=
          notMem_tsupport_iff_eventuallyEq.mp hnot
        have hd : mvfderiv I (ρ i) x v = 0 := by
          change (mfderiv I 𝓘(ℝ) (ρ i) x v : ℝ) = 0
          rw [hz.mfderiv_eq, mfderiv_const]
          rfl
        simp only [hd, abs_zero, zero_mul, le_refl]
    _ = (∑ i, |mvfderiv I (ρ i) x v|) * δ := (Finset.sum_mul ..).symm
    _ ≤ (N : ℝ) ^ 2 * D * δ := mul_le_mul_of_nonneg_right hsum hδ
    _ < κ := hsmall

end DifferentialGeometry.Topology.Manifold
