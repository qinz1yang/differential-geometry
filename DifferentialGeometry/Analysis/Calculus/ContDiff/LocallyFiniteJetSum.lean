import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.Monoid

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_finset_support_on_open
    {ι X Y : Type*} [TopologicalSpace X] [Zero Y]
    {U : Set X} (hU : IsOpen U) {f : ι → X → Y}
    (hloc : LocallyFinite fun i => support (fun x : U => f i x))
    {x : X} (hx : x ∈ U) :
    ∃ S : Finset ι, ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ S := by
  obtain ⟨S, hS⟩ := hloc.exists_finset_support (⟨x, hx⟩ : U)
  refine ⟨S, ?_⟩
  have hmap := hU.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hx⟩ : U)
  rw [← hmap]
  exact Filter.eventually_map.mpr hS

theorem contDiffOn_finsum_of_locallyFinite_restrict
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ι → E → F}
    (hloc : LocallyFinite fun i => support (fun x : U => f i x))
    (n : ℕ∞ω) (hf : ∀ i, ContDiffOn ℝ n (f i) U) :
    ContDiffOn ℝ n (fun x => ∑ᶠ i, f i x) U := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := exists_finset_support_on_open hU hloc hx
  have heq : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ S, f i y) := by
    filter_upwards [hS] with y hy
    exact finsum_eq_sum_of_support_subset _ hy
  exact ((ContDiffAt.sum (fun i _ =>
    (hf i).contDiffAt (hU.mem_nhds hx))).congr_of_eventuallyEq heq).contDiffWithinAt

theorem iteratedFDeriv_finsum_of_locallyFinite_restrict
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ι → E → F}
    (hloc : LocallyFinite fun i => support (fun x : U => f i x))
    (k : ℕ) {x : E} (hx : x ∈ U) (hf : ∀ i, ContDiffAt ℝ k (f i) x) :
    iteratedFDeriv ℝ k (fun y => ∑ᶠ i, f i y) x =
      ∑ᶠ i, iteratedFDeriv ℝ k (f i) x := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_support_on_open hU hloc hx
  have hlocal : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ S, f i y) := by
    filter_upwards [hS] with y hy
    exact finsum_eq_sum_of_support_subset _ hy
  have hzero (i : ι) (hi : i ∉ S) : iteratedFDeriv ℝ k (f i) x = 0 := by
    have hz : f i =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hS] with y hy
      by_contra hiy
      exact hi (hy hiy)
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (hz.iteratedFDeriv ℝ k).eq_of_nhds
  have hsupp : support (fun i => iteratedFDeriv ℝ k (f i) x) ⊆ S := by
    intro i hi
    by_contra hiS
    exact hi (hzero i hiS)
  rw [(hlocal.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun i _ => hf i),
    finsum_eq_sum_of_support_subset _ hsupp]

theorem norm_iteratedFDeriv_finsum_le_of_locallyFinite_restrict
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ι → E → F}
    (hloc : LocallyFinite fun i => support (fun x : U => f i x))
    (k : ℕ) {x : E} (hx : x ∈ U) (hf : ∀ i, ContDiffAt ℝ k (f i) x)
    {a : ι → ℝ} (ha : Summable a)
    (hbound : ∀ i, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ a i) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ᶠ i, f i y) x‖ ≤ ∑' i, a i := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_support_on_open hU hloc hx
  have hlocal : (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ S, f i y) := by
    filter_upwards [hS] with y hy
    exact finsum_eq_sum_of_support_subset _ hy
  rw [(hlocal.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun i _ => hf i)]
  calc
    ‖∑ i ∈ S, iteratedFDeriv ℝ k (f i) x‖
        ≤ ∑ i ∈ S, ‖iteratedFDeriv ℝ k (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, a i := Finset.sum_le_sum (fun i _ => hbound i)
    _ ≤ ∑' i, a i := ha.sum_le_tsum _ (fun i _ => (norm_nonneg _).trans (hbound i))

end DifferentialGeometry.Analysis
