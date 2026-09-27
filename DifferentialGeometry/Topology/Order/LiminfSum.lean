import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set

namespace Filter

theorem sum_liminf_le
    {ι α : Type*} {l : Filter α} [NeBot l] (s : Finset ι) (q : ι → α → ℝ)
    (hlo : ∀ i ∈ s, IsBoundedUnder (· ≥ ·) l (q i))
    (hhi : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) l (q i)) :
    (∑ i ∈ s, liminf (q i) l) ≤
      liminf (∑ i ∈ s, q i) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change 0 ≤ liminf (fun _ : α ↦ (0 : ℝ)) l
      rw [liminf_const]
  | @insert i s hi ih =>
      have hi_lo := hlo i (Finset.mem_insert_self i s)
      have hi_hi := hhi i (Finset.mem_insert_self i s)
      have hs_lo : ∀ j ∈ s, IsBoundedUnder (· ≥ ·) l (q j) :=
        fun j hj ↦ hlo j (Finset.mem_insert_of_mem hj)
      have hs_hi : ∀ j ∈ s, IsBoundedUnder (· ≤ ·) l (q j) :=
        fun j hj ↦ hhi j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add_right (ih hs_lo hs_hi) _).trans
        (le_liminf_add hi_lo hi_hi
          (isBoundedUnder_ge_sum s hs_lo)
          (isBoundedUnder_le_sum s hs_hi).isCoboundedUnder_ge)

end Filter
