import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace Poincare.Topology.Manifold

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem sum_differentiable_derivative (s : Finset ι) {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ∑ i ∈ s, f i y) x ∧
      mvfderiv I (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, mvfderiv I (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using And.intro mdifferentiableAt_const (mvfderiv_const (I := I) (0 : ℝ))
  | insert i s hi ih =>
    obtain ⟨hd, he⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hi' := hf i (Finset.mem_insert_self i s)
    constructor
    · convert! hi'.add hd using 1
      funext y
      simp only [Finset.sum_insert hi, Pi.add_apply]
    · simp only [Finset.sum_insert hi]
      rw [mvfderiv_fun_add hi' hd, he]

private theorem mvfderiv_eq_zero_of_eventually_zero {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] fun _ ↦ 0) : mvfderiv I f x = 0 := by
  ext v
  change (show ℝ from mfderiv I 𝓘(ℝ) f x v) = 0
  rw [hf.mfderiv_eq, mfderiv_const]
  rfl

private theorem weighted_differentiable_derivative
    (ρ : SmoothPartitionOfUnity ι I M) (g : ι → M → ℝ) (i : ι) (x : M)
    (hg : x ∈ tsupport (ρ i) → MDifferentiableAt I 𝓘(ℝ) (g i) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ρ i y * g i y) x ∧
    ∀ v : TangentSpace I x,
      mvfderiv I (fun y ↦ ρ i y * g i y) x v =
        ρ i x * mvfderiv I (g i) x v + g i x * mvfderiv I (ρ i) x v := by
  by_cases hx : x ∈ tsupport (ρ i)
  · have hρ := (ρ i).contMDiff.mdifferentiable (by simp) x
    refine ⟨hρ.mul (hg hx), ?_⟩
    intro v
    rw [mvfderiv_fun_mul hρ (hg hx)]
    simp
  · have hρzero := notMem_tsupport_iff_eventuallyEq.mp hx
    have hprod : (fun y ↦ ρ i y * g i y) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hρzero] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    refine ⟨mdifferentiableAt_const.congr_of_eventuallyEq hprod, ?_⟩
    intro v
    rw [mvfderiv_eq_zero_of_eventually_zero hprod,
      mvfderiv_eq_zero_of_eventually_zero hρzero, image_eq_zero_of_notMem_tsupport hx]
    simp

theorem mvfderiv_partition_sum [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι I M) (g : ι → M → ℝ) (x : M)
    (hg : ∀ i, x ∈ tsupport (ρ i) → MDifferentiableAt I 𝓘(ℝ) (g i) x)
    (v : TangentSpace I x) (c : ℝ) :
    mvfderiv I (fun y ↦ ∑ i, ρ i y * g i y) x v =
      (∑ i, ρ i x * mvfderiv I (g i) x v) +
      ∑ i, mvfderiv I (ρ i) x v * (g i x - c) := by
  have hweights : (fun y ↦ ∑ i, ρ i y) = fun _ ↦ (1 : ℝ) := by
    funext y
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ y)
  have hsum := (sum_differentiable_derivative Finset.univ
    (fun i _ ↦ (ρ i).contMDiff.mdifferentiable (by simp) x)).2
  have hcancel : ∑ i, mvfderiv I (ρ i) x v = 0 := by
    have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L v) hsum
    simpa only [hweights, mvfderiv_const, zero_apply,
      sum_apply] using h.symm
  rw [(sum_differentiable_derivative Finset.univ
    (fun i _ ↦ (weighted_differentiable_derivative ρ g i x (hg i)).1)).2,
    sum_apply]
  simp_rw [(weighted_differentiable_derivative ρ g _ x (hg _)).2 v]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcancel, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mvfderiv_partition_sum_pos_of_error_lt [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι I M) (g : ι → M → ℝ) (x : M)
    (hg : ∀ i, x ∈ tsupport (ρ i) → MDifferentiableAt I 𝓘(ℝ) (g i) x)
    (v : TangentSpace I x) (c κ : ℝ)
    (hmain : ∀ i, ρ i x ≠ 0 → κ ≤ mvfderiv I (g i) x v)
    (herror : (∑ i, |mvfderiv I (ρ i) x v| * |g i x - c|) < κ) :
    0 < mvfderiv I (fun y ↦ ∑ i, ρ i y * g i y) x v := by
  have hsum : ∑ i, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  have hmain' : κ ≤ ∑ i, ρ i x * mvfderiv I (g i) x v := by
    calc
      κ = (∑ i, ρ i x) * κ := by rw [hsum, one_mul]
      _ = ∑ i, ρ i x * κ := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum (by
        intro i _
        by_cases hi : ρ i x = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hmain i hi) (ρ.nonneg i x))
  have herr : |∑ i, mvfderiv I (ρ i) x v * (g i x - c)| ≤
      ∑ i, |mvfderiv I (ρ i) x v| * |g i x - c| := by
    simpa only [abs_mul] using
      Finset.abs_sum_le_sum_abs (fun i ↦ mvfderiv I (ρ i) x v * (g i x - c)) Finset.univ
  rw [mvfderiv_partition_sum ρ g x hg v c]
  have h := neg_abs_le (∑ i, mvfderiv I (ρ i) x v * (g i x - c))
  linarith

theorem mfderiv_partition_sum_ne_zero_of_error_lt [Fintype ι]
    (ρ : SmoothPartitionOfUnity ι I M) (g : ι → M → ℝ) (x : M)
    (hg : ∀ i, x ∈ tsupport (ρ i) → MDifferentiableAt I 𝓘(ℝ) (g i) x)
    (v : TangentSpace I x) (c κ : ℝ)
    (hmain : ∀ i, ρ i x ≠ 0 → κ ≤ mvfderiv I (g i) x v)
    (herror : (∑ i, |mvfderiv I (ρ i) x v| * |g i x - c|) < κ) :
    mfderiv I 𝓘(ℝ) (fun y ↦ ∑ i, ρ i y * g i y) x ≠ 0 := by
  intro hzero
  have hpos := mvfderiv_partition_sum_pos_of_error_lt ρ g x hg v c κ hmain herror
  simp [mvfderiv, hzero] at hpos

end Poincare.Topology.Manifold
