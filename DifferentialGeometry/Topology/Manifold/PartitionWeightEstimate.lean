import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace Poincare.Topology.Manifold

variable {ι : Type} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem abs_mvfderiv_prod_le_sum (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (hbound : ∀ i ∈ s, |f i x| ≤ 1) (v : TangentSpace I x) :
    |mvfderiv I (fun y ↦ ∏ i ∈ s, f i y) x v| ≤
      ∑ i ∈ s, |mvfderiv I (f i) x v| := by
  classical
  have hd : mvfderiv I (fun y ↦ ∏ i ∈ s, f i y) x =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • mvfderiv I (f i) x := by
    convert! (HasMFDerivAt.prod (fun i hi ↦ (hf i hi).hasMFDerivAt)).mfderiv using 1
    change mfderiv I 𝓘(ℝ) (fun y ↦ ∏ i ∈ s, f i y) x =
      mfderiv I 𝓘(ℝ) (∏ i ∈ s, f i) x
    congr 1
    funext y
    simp only [Finset.prod_apply]
  have heq : mvfderiv I (fun y ↦ ∏ i ∈ s, f i y) x v =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * mvfderiv I (f i) x v := by
    rw [hd]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  have hp : |∏ j ∈ s.erase i, f j x| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ ↦ abs_nonneg _)
      (fun j hj ↦ hbound j (Finset.mem_of_mem_erase hj))
  exact mul_le_of_le_one_left (abs_nonneg _) hp

theorem abs_mvfderiv_bump_partition_le_sum [Fintype ι]
    (f : BumpCovering ι M) (x : M)
    (hf : ∀ i, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (i : ι) (v : TangentSpace I x) :
    |mvfderiv I (f.toPartitionOfUnity i) x v| ≤
      ∑ j, |mvfderiv I (f j) x v| := by
  classical
  let s := Finset.univ.filter (fun j ↦ WellOrderingRel j i)
  let g : M → ℝ := fun y ↦ ∏ j ∈ s, (1 - f j y)
  have hform : (f.toPartitionOfUnity i : M → ℝ) = fun y ↦ f i y * g y := by
    funext y
    exact f.toPartitionOfUnity_eq_mul_prod i y Finset.univ (fun _ _ _ ↦ Finset.mem_univ _)
  have hg : MDifferentiableAt I 𝓘(ℝ) g x := by
    convert MDifferentiableAt.prod (fun j (_ : j ∈ s) ↦
      (show MDifferentiableAt I 𝓘(ℝ) (fun _ : M ↦ (1 : ℝ)) x from
        mdifferentiableAt_const).sub (hf j)) using 1 <;>
      first | rfl | (funext y; simp only [g, Finset.prod_apply, Pi.sub_apply])
  have hgb : |g x| ≤ 1 := by
    change |∏ j ∈ s, (1 - f j x)| ≤ 1
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ ↦ abs_nonneg _)
    intro j _
    rw [abs_of_nonneg (sub_nonneg.mpr (f.le_one j x))]
    linarith [f.nonneg j x]
  have hd : |mvfderiv I g x v| ≤ ∑ j ∈ s, |mvfderiv I (f j) x v| := by
    have hh := abs_mvfderiv_prod_le_sum s (fun j y ↦ 1 - f j y) x
      (fun j _ ↦ mdifferentiableAt_const.sub (hf j))
      (fun j _ ↦ by
        rw [abs_of_nonneg (sub_nonneg.mpr (f.le_one j x))]
        linarith [f.nonneg j x]) v
    simpa only [g, mvfderiv_fun_sub mdifferentiableAt_const (hf _),
      mvfderiv_const, sub_apply, zero_apply, zero_sub, neg_apply, abs_neg] using hh
  have hi : i ∉ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact irrefl i
  have hsum : |mvfderiv I (f i) x v| + (∑ j ∈ s, |mvfderiv I (f j) x v|) ≤
      ∑ j, |mvfderiv I (f j) x v| := by
    rw [← Finset.sum_insert hi (f := fun j ↦ |mvfderiv I (f j) x v|)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ abs_nonneg _)
  rw [hform, mvfderiv_fun_mul (hf i) hg]
  change |f i x * mvfderiv I g x v + g x * mvfderiv I (f i) x v| ≤ _
  calc
    _ ≤ |f i x| * |mvfderiv I g x v| + |g x| * |mvfderiv I (f i) x v| := by
      simpa only [abs_mul] using abs_add_le (f i x * mvfderiv I g x v)
        (g x * mvfderiv I (f i) x v)
    _ ≤ |mvfderiv I g x v| + |mvfderiv I (f i) x v| := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) (by
        rw [abs_of_nonneg (f.nonneg i x)]; exact f.le_one i x))
      (mul_le_of_le_one_left (abs_nonneg _) hgb)
    _ ≤ (∑ j ∈ s, |mvfderiv I (f j) x v|) + |mvfderiv I (f i) x v| :=
      add_le_add hd le_rfl
    _ ≤ _ := by linarith [hsum]

open scoped Classical in
theorem sum_abs_mvfderiv_bump_partition_le_multiplicity [Fintype ι]
    (f : BumpCovering ι M) (x : M)
    (hf : ∀ i, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (v : TangentSpace I x) (N : ℕ) (D : ℝ)
    (hcard : (Finset.univ.filter (fun i ↦ x ∈ tsupport (f i))).card ≤ N)
    (hbound : ∀ i, x ∈ tsupport (f i) → |mvfderiv I (f i) x v| ≤ D) :
    (∑ i, |mvfderiv I (f.toPartitionOfUnity i) x v|) ≤ (N : ℝ) ^ 2 * D := by
  classical
  let s := Finset.univ.filter (fun i ↦ x ∈ tsupport (f i))
  have hzero {g : M → ℝ} (hg : g =ᶠ[𝓝 x] fun _ ↦ 0) : mvfderiv I g x v = 0 := by
    change (mfderiv I 𝓘(ℝ) g x v : ℝ) = 0
    rw [hg.mfderiv_eq, mfderiv_const]
    rfl
  have hout (i : ι) (hi : i ∉ s) :
      mvfderiv I (f i) x v = 0 ∧ mvfderiv I (f.toPartitionOfUnity i) x v = 0 := by
    have hnot : x ∉ tsupport (f i) := by simpa only [s, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    have hz := notMem_tsupport_iff_eventuallyEq.mp hnot
    refine ⟨hzero hz, hzero ?_⟩
    filter_upwards [hz] with y hy
    exact f.toPartitionOfUnity_zero_of_zero hy
  have hbump : (∑ i, |mvfderiv I (f i) x v|) = ∑ i ∈ s, |mvfderiv I (f i) x v| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    simp only [(hout i hi).1, abs_zero]
  have hpart : (∑ i, |mvfderiv I (f.toPartitionOfUnity i) x v|) =
      ∑ i ∈ s, |mvfderiv I (f.toPartitionOfUnity i) x v| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    simp only [(hout i hi).2, abs_zero]
  have hD : 0 ≤ D := by
    let i := f.ind x (mem_univ x)
    have hi : x ∈ tsupport (f i) := subset_tsupport _ (by
      change f i x ≠ 0
      rw [f.ind_apply x (mem_univ x)]
      exact one_ne_zero)
    exact (abs_nonneg _).trans (hbound i hi)
  have hb : (∑ i, |mvfderiv I (f i) x v|) ≤ (s.card : ℝ) * D := by
    rw [hbump]
    calc
      _ ≤ ∑ _i ∈ s, D := Finset.sum_le_sum (fun i hi ↦ hbound i (Finset.mem_filter.mp hi).2)
      _ = _ := by simp
  have hc : (s.card : ℝ) ≤ N := by exact_mod_cast hcard
  rw [hpart]
  calc
    _ ≤ ∑ _i ∈ s, (∑ j, |mvfderiv I (f j) x v|) :=
      Finset.sum_le_sum (fun i _ ↦ abs_mvfderiv_bump_partition_le_sum f x hf i v)
    _ = (s.card : ℝ) * (∑ j, |mvfderiv I (f j) x v|) := by simp
    _ ≤ (s.card : ℝ) * ((s.card : ℝ) * D) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (s.card : ℝ) ^ 2 * D := by ring
    _ ≤ (N : ℝ) ^ 2 * D := mul_le_mul_of_nonneg_right
      (by nlinarith [Nat.cast_nonneg (α := ℝ) s.card, Nat.cast_nonneg (α := ℝ) N]) hD

end Poincare.Topology.Manifold
