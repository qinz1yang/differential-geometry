import DifferentialGeometry.Topology.Manifold.OrderedStepPartition
import Mathlib.Order.Fin.Basic

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

theorem antitone_of_separated_steps
    {ι X : Type*} [LinearOrder ι] (θ : ι → X → ℝ) (P Q : ι → Set X)
    (hbound : ∀ i x, θ i x ∈ Icc (0 : ℝ) 1)
    (hzero : ∀ i x, x ∈ P i → θ i x = 0)
    (hone : ∀ i x, x ∈ Q i → θ i x = 1)
    (hsep : ∀ i j, i < j → Q i ∪ P j = univ) (x : X) :
    Antitone (fun i ↦ θ i x) := by
  intro i j hij
  change θ j x ≤ θ i x
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · rcases (show x ∈ Q i ∪ P j from (hsep i j hij).symm ▸ mem_univ x) with hq | hp
    · rw [hone i x hq]
      exact (hbound j x).2
    · rw [hzero j x hp]
      exact (hbound i x).1

namespace Manifold

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem tsupport_orderedStepPartition_subset
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (P Q : Fin (n + 2) → Set M)
    (hzero : ∀ i x, x ∈ P i → θ i x = 0)
    (hone : ∀ i x, x ∈ Q i → θ i x = 1) (i : Fin (n + 1)) :
    tsupport (orderedStepPartition θ horder hfirst hlast i) ⊆
      (interior (P i.castSucc))ᶜ ∩ (interior (Q i.succ))ᶜ := by
  apply closure_minimal
  · intro x hx
    change θ i.castSucc x - θ i.succ x ≠ 0 at hx
    constructor
    · intro hp
      have hnext : θ i.succ x = 0 := by
        apply le_antisymm
        · simpa only [hzero i.castSucc x (interior_subset hp)] using
            horder x (show i.castSucc ≤ i.succ from Fin.le_def.mpr (Nat.le_succ _))
        · simpa only [hlast x] using horder x (Fin.le_last i.succ)
      exact hx (by rw [hzero i.castSucc x (interior_subset hp), hnext, sub_self])
    · intro hq
      have hprev : θ i.castSucc x = 1 := by
        apply le_antisymm
        · simpa only [hfirst x] using horder x (Fin.zero_le i.castSucc)
        · simpa only [hone i.succ x (interior_subset hq)] using
            horder x (show i.castSucc ≤ i.succ from Fin.le_def.mpr (Nat.le_succ _))
      exact hx (by rw [hprev, hone i.succ x (interior_subset hq), sub_self])
  · exact isOpen_interior.isClosed_compl.inter isOpen_interior.isClosed_compl

theorem disjoint_tsupport_orderedStepPartition_of_separated_exteriors
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (P Q : Fin (n + 2) → Set M)
    (hzero : ∀ i x, x ∈ P i → θ i x = 0)
    (hone : ∀ i x, x ∈ Q i → θ i x = 1)
    (hsep : ∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ)
    (i j : Fin (n + 1)) (hij : i.val + 1 < j.val) :
    Disjoint (tsupport (orderedStepPartition θ horder hfirst hlast i))
      (tsupport (orderedStepPartition θ horder hfirst hlast j)) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi := tsupport_orderedStepPartition_subset θ horder hfirst hlast P Q hzero hone i hxi
  have hj := tsupport_orderedStepPartition_subset θ horder hfirst hlast P Q hzero hone j hxj
  have hx : x ∈ interior (Q i.succ) ∪ interior (P j.castSucc) :=
    (hsep i.succ j.castSucc (Fin.lt_def.mpr hij)).symm ▸ mem_univ x
  exact hx.elim hi.2 hj.1

theorem inter_tsupport_orderedStepPartition_subset_of_binary_off_band
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (j : Fin n) {K : Set M} (hK : IsClosed K)
    (hbinary : ∀ x ∉ K, θ j.succ.castSucc x = 0 ∨ θ j.succ.castSucc x = 1) :
    tsupport (orderedStepPartition θ horder hfirst hlast j.castSucc) ∩
      tsupport (orderedStepPartition θ horder hfirst hlast j.succ) ⊆ K := by
  intro x hx
  by_contra hxK
  rcases hbinary x hxK with hzero | hone
  · have hn : ∀ᶠ y in 𝓝 x, θ j.succ.castSucc y < 1 / 2 :=
      (θ j.succ.castSucc).contMDiff.continuous.continuousAt.eventually
        (Iio_mem_nhds (by rw [hzero]; norm_num))
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx.2
    filter_upwards [hK.isOpen_compl.mem_nhds hxK, hn] with y hy hyhalf
    have hmid : θ j.succ.castSucc y = 0 := by
      rcases hbinary y hy with h | h
      · exact h
      · rw [h] at hyhalf
        norm_num at hyhalf
    have hnext : θ j.succ.succ y = 0 := by
      apply le_antisymm
      · simpa only [hmid] using
          horder y (show j.succ.castSucc ≤ j.succ.succ from Fin.le_def.mpr (Nat.le_succ _))
      · simpa only [hlast y] using horder y (Fin.le_last j.succ.succ)
    change θ j.succ.castSucc y - θ j.succ.succ y = 0
    rw [hmid, hnext, sub_self]
  · have hn : ∀ᶠ y in 𝓝 x, 1 / 2 < θ j.succ.castSucc y :=
      (θ j.succ.castSucc).contMDiff.continuous.continuousAt.eventually
        (Ioi_mem_nhds (by rw [hone]; norm_num))
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx.1
    filter_upwards [hK.isOpen_compl.mem_nhds hxK, hn] with y hy hyhalf
    have hmid : θ j.succ.castSucc y = 1 := by
      rcases hbinary y hy with h | h
      · rw [h] at hyhalf
        norm_num at hyhalf
      · exact h
    have hprev : θ j.castSucc.castSucc y = 1 := by
      apply le_antisymm
      · simpa only [hfirst y] using horder y (Fin.zero_le j.castSucc.castSucc)
      · simpa only [hmid] using
          horder y (show j.castSucc.castSucc ≤ j.succ.castSucc from Fin.le_def.mpr (Nat.le_succ _))
    change θ j.castSucc.castSucc y - θ j.succ.castSucc y = 0
    rw [hprev, hmid, sub_self]

theorem orderedStepPartition_first_eq_one_near
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    {P : Set M} (hzero : ∀ y ∈ P, θ (0 : Fin (n + 1)).succ y = 0)
    {x : M} (hx : x ∈ interior P) :
    (orderedStepPartition θ horder hfirst hlast 0 : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  change θ 0 y - θ (0 : Fin (n + 1)).succ y = 1
  rw [hfirst y, hzero y (interior_subset hy), sub_zero]

theorem orderedStepPartition_last_eq_one_near
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    {Q : Set M} (hone : ∀ y ∈ Q, θ (Fin.last n).castSucc y = 1)
    {x : M} (hx : x ∈ interior Q) :
    (orderedStepPartition θ horder hfirst hlast (Fin.last n) : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  change θ (Fin.last n).castSucc y - θ (Fin.last (n + 1)) y = 1
  rw [hone y (interior_subset hy), hlast y, sub_zero]

end Manifold
end DifferentialGeometry.Topology
