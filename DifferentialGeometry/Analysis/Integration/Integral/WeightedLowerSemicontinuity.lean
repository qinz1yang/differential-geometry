import DifferentialGeometry.Topology.Order.LiminfSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.PartitionOfUnity
import DifferentialGeometry.Topology.PartitionOfUnity.FiniteSum

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

theorem sum_le_liminf_integral_of_subordinate_weighted_liminf
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ℕ → α → ℝ) (w : ι → ℕ → α → ℝ)
    (hf : ∀ n, Integrable (f n) μ) (hf0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hw : ∀ i ∈ s, ∀ n, AEStronglyMeasurable (w i n) μ)
    (hw0 : ∀ i ∈ s, ∀ n, ∀ᵐ x ∂μ, 0 ≤ w i n x)
    (hwsum : ∀ n, ∀ᵐ x ∂μ, ∑ i ∈ s, w i n x ≤ 1)
    {C : ℝ} (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ C)
    (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≤ liminf (fun n => ∫ x, w i n x * f n x ∂μ) atTop) :
    (∑ i ∈ s, a i) ≤ liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  classical
  have hw1 (i : ι) (hi : i ∈ s) (n : ℕ) : ∀ᵐ x ∂μ, w i n x ≤ 1 := by
    have hpos : ∀ᵐ x ∂μ, ∀ j ∈ s, 0 ≤ w j n x := by
      exact (s.eventually_all).mpr fun j hj => hw0 j hj n
    filter_upwards [hpos, hwsum n] with x hx hsx
    exact (Finset.single_le_sum (fun j hj => hx j hj) hi).trans hsx
  have hint (i : ι) (hi : i ∈ s) (n : ℕ) : Integrable (fun x => w i n x * f n x) μ := by
    apply (hf n).bdd_mul (c := (1 : ℝ)) (hw i hi n)
    filter_upwards [hw0 i hi n, hw1 i hi n] with x hx hx1
    rwa [Real.norm_eq_abs, abs_of_nonneg hx]
  let q : ι → ℕ → ℝ := fun i n => ∫ x, w i n x * f n x ∂μ
  have hq0 (i : ι) (hi : i ∈ s) (n : ℕ) : 0 ≤ q i n :=
    integral_nonneg_of_ae ((hw0 i hi n).and (hf0 n) |>.mono
      fun _ h => mul_nonneg h.1 h.2)
  have hqE (i : ι) (hi : i ∈ s) (n : ℕ) : q i n ≤ ∫ x, f n x ∂μ := by
    apply integral_mono_ae (hint i hi n) (hf n)
    filter_upwards [hw1 i hi n, hf0 n] with x hx hf0x
    exact mul_le_of_le_one_left hf0x hx
  have hlo (i : ι) (hi : i ∈ s) : IsBoundedUnder (· ≥ ·) atTop (q i) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q i n
    exact Eventually.of_forall (hq0 i hi)
  have hhi (i : ι) (hi : i ∈ s) : IsBoundedUnder (· ≤ ·) atTop (q i) := by
    refine ⟨C, ?_⟩
    change ∀ᶠ n in atTop, q i n ≤ C
    exact Eventually.of_forall fun n => (hqE i hi n).trans (hbound n)
  have hsumE (n : ℕ) : (∑ i ∈ s, q i n) ≤ ∫ x, f n x ∂μ := by
    rw [show (∑ i ∈ s, q i n) = ∫ x, (∑ i ∈ s, w i n x) * f n x ∂μ by
      simp only [Finset.sum_mul]
      exact (integral_finsetSum s (fun i hi => hint i hi n)).symm]
    have hsumint : Integrable (fun x => (∑ i ∈ s, w i n x) * f n x) μ := by
      simpa only [Finset.sum_mul] using integrable_finsetSum s (fun i hi => hint i hi n)
    apply integral_mono_ae hsumint (hf n)
    filter_upwards [hwsum n, hf0 n] with x hx hfx
    exact mul_le_of_le_one_left hfx hx
  have hsum := sum_liminf_le s q hlo hhi
  have hsumlo : IsBoundedUnder (· ≥ ·) atTop (fun n => ∑ i ∈ s, q i n) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ ∑ i ∈ s, q i n
    exact Eventually.of_forall fun n => Finset.sum_nonneg (fun i hi => hq0 i hi n)
  have hEhi : IsCoboundedUnder (· ≥ ·) atTop (fun n => ∫ x, f n x ∂μ) :=
    isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hbound)
  have hsumle := liminf_le_liminf (Eventually.of_forall hsumE) hsumlo hEhi
  have heq : (∑ i ∈ s, q i) = (fun n => ∑ i ∈ s, q i n) := by
    funext n
    exact Finset.sum_apply n s q
  rw [heq] at hsum
  exact (Finset.sum_le_sum ha).trans (hsum.trans hsumle)

end MeasureTheory

end

end

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

theorem sum_le_liminf_integral_of_weighted_liminf
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [MeasurableSpace M] [BorelSpace M]
    {s₀ : Set M} (ρ : PartitionOfUnity ι M s₀) (s : Finset ι)
    (U : ℕ → α → M) (hU : ∀ n, AEMeasurable (U n) μ)
    (f : ℕ → α → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hf0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    {C : ℝ} (hbound : ∀ n, (∫ x, f n x ∂μ) ≤ C)
    (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≤ liminf (fun n => ∫ x, ρ i (U n x) * f n x ∂μ) atTop) :
    (∑ i ∈ s, a i) ≤ liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  apply MeasureTheory.sum_le_liminf_integral_of_subordinate_weighted_liminf
    s f (fun i n x => ρ i (U n x)) hf hf0
  · intro i _ n
    exact ((ρ i).continuous.measurable.comp_aemeasurable (hU n)).aestronglyMeasurable
  · exact fun i _ n => Eventually.of_forall fun x => ρ.nonneg i (U n x)
  · exact fun n => Eventually.of_forall fun x => ρ.sum_finset_le_one s (U n x)
  · exact hbound
  · exact ha

end PartitionOfUnity

end

end
