import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

theorem tsum_mul_eq_of_eq_on_support (ρ : PartitionOfUnity ι M univ)
    (x : M) (d : ι → ℝ) (a : ℝ) (hd : ∀ i, ρ i x ≠ 0 → d i = a) :
    (∑' i, ρ i x * d i) = a := by
  have hfin : (Function.support fun i => ρ i x * d i).Finite :=
    (ρ.locallyFinite.point_finite x).subset (Function.support_mul_subset_left _ _)
  rw [tsum_eq_finsum hfin]
  calc
    (∑ᶠ i, ρ i x * d i) = ∑ᶠ i, ρ i x * a := by
      apply finsum_congr
      intro i
      by_cases hi : ρ i x = 0
      · simp only [hi, zero_mul]
      · rw [hd i hi]
    _ = (∑ᶠ i, ρ i x) * a := (finsum_mul _ _).symm
    _ = a := by rw [ρ.sum_eq_one (mem_univ x), one_mul]

theorem tsum_mul_ae_eq_of_compatible
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    (ρ : PartitionOfUnity ι M univ) (v : α → M) (d : ι → α → ℝ)
    (hd : ∀ i j, ∀ᵐ x ∂μ, ρ i (v x) ≠ 0 → ρ j (v x) ≠ 0 → d i x = d j x) :
    ∀ᵐ x ∂μ, ∀ i, ρ i (v x) ≠ 0 → (∑' j, ρ j (v x) * d j x) = d i x := by
  have hall : ∀ᵐ x ∂μ, ∀ i j, ρ i (v x) ≠ 0 → ρ j (v x) ≠ 0 → d i x = d j x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hd i)
  filter_upwards [hall] with x hx i hi
  exact ρ.tsum_mul_eq_of_eq_on_support (v x) (fun j => d j x) (d i x)
    (fun j hj => hx j i hj hi)

theorem tsum_mul_ae_eq_of_cross_compatible
    {α κ : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι] [Countable κ]
    (ρ : PartitionOfUnity ι M univ) (σ : PartitionOfUnity κ M univ)
    (v : α → M) (d : ι → α → ℝ) (e : κ → α → ℝ)
    (hde : ∀ i j, ∀ᵐ x ∂μ, ρ i (v x) ≠ 0 → σ j (v x) ≠ 0 → d i x = e j x) :
    (fun x => ∑' i, ρ i (v x) * d i x) =ᵐ[μ] (fun x => ∑' j, σ j (v x) * e j x) := by
  have hall : ∀ᵐ x ∂μ, ∀ i j, ρ i (v x) ≠ 0 → σ j (v x) ≠ 0 → d i x = e j x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hde i)
  filter_upwards [hall] with x hx
  obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ (v x))
  obtain ⟨j, hj⟩ := σ.exists_pos (mem_univ (v x))
  have hleft := ρ.tsum_mul_eq_of_eq_on_support (v x) (fun k => d k x) (e j x)
    (fun k hk => hx k j hk hj.ne')
  have hright := σ.tsum_mul_eq_of_eq_on_support (v x) (fun k => e k x) (d i x)
    (fun k hk => (hx i k hi.ne' hk).symm)
  exact hleft.trans ((hx i j hi.ne' hj.ne').symm.trans hright.symm)

end PartitionOfUnity

namespace MeasureTheory

theorem integrable_tsum_of_summable_integral_norm
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  let F : ι → Lp ℝ 1 μ := fun i => (hf i).toL1 (f i)
  have hnorm (i : ι) : ‖F i‖ = ∫ x, ‖f i x‖ ∂μ := by
    rw [show F i = (hf i).toL1 (f i) from rfl,
      Integrable.norm_toL1_eq_lintegral_enorm,
      integral_norm_eq_lintegral_enorm (hf i).aestronglyMeasurable]
  have hsum : ∑' i, ‖F i‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (by simpa only [hnorm] using hs)
  have heq : (fun x => (∑' i, F i) x) =ᵐ[μ] (fun x => ∑' i, f i x) := by
    filter_upwards [Lp.coeFn_tsum hsum, ae_all_iff.mpr (fun i => (hf i).coeFn_toL1)] with x hx hi
    rw [hx]
    exact tsum_congr fun i => hi i
  exact (memLp_one_iff_integrable.mp (Lp.memLp (∑' i, F i))).congr heq

end MeasureTheory

end

end
