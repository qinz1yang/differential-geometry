import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]

theorem exists_interval_or_ray_isometry_of_isometry_dist {p : X}
    (hcurves : ∀ x : X, ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = x)
    (hiso : Isometry (fun x : X => dist p x)) :
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ Icc (0 : ℝ) L, ∀ x, (e x : ℝ) = dist p x) ∨
    (∃ e : X ≃ᵢ Ici (0 : ℝ), ∀ x, (e x : ℝ) = dist p x) := by
  classical
  let S := range (fun x : X => dist p x)
  have hS0 : (0 : ℝ) ∈ S := ⟨p, dist_self p⟩
  have hclosed : IsClosed S := hiso.antilipschitzWith.isClosed_range hiso.uniformContinuous
  have hfill {y : X} {t : ℝ} (ht : 0 ≤ t) (hty : t ≤ dist p y) : t ∈ S := by
    obtain ⟨c, hc, hc0, hc1⟩ := hcurves y
    obtain ⟨s, hs⟩ := intermediate_value_univ (0 : unitInterval) 1 (continuous_const.dist hc)
      (show t ∈ Icc (dist p (c 0)) (dist p (c 1)) by rw [hc0, hc1, dist_self]; exact ⟨ht, hty⟩)
    exact ⟨c s, hs⟩
  have hequiv {T : Set ℝ} (hST : S = T) : ∃ e : X ≃ᵢ T, ∀ x, (e x : ℝ) = dist p x := by
    let F : X → T := fun x => ⟨dist p x, hST ▸ mem_range_self x⟩
    have hF : Isometry F := hiso
    have hsurj : Function.Surjective F := by
      intro y
      have hy : (y : ℝ) ∈ S := hST ▸ y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
    exact ⟨⟨Equiv.ofBijective F ⟨hF.injective, hsurj⟩, hF⟩, fun _ => rfl⟩
  by_cases hB : BddAbove S
  · let L := sSup S
    have hLS : L ∈ S := hclosed.csSup_mem ⟨0, hS0⟩ hB
    obtain ⟨u, hup⟩ := exists_ne p
    have hu : 0 < dist p u := dist_pos.mpr (Ne.symm hup)
    have hL : 0 < L := hu.trans_le (le_csSup hB (mem_range_self u))
    have hSL : S = Icc (0 : ℝ) L := by
      apply Subset.antisymm
      · rintro t ⟨x, rfl⟩
        exact ⟨dist_nonneg, le_csSup hB (mem_range_self x)⟩
      · intro t ht
        obtain ⟨y, hy⟩ := hLS
        exact hfill ht.1 (hy ▸ ht.2)
    obtain ⟨e, he⟩ := hequiv hSL
    exact Or.inl ⟨L, hL, e, he⟩
  · have hSray : S = Ici (0 : ℝ) := by
      apply Subset.antisymm
      · rintro t ⟨x, rfl⟩
        exact dist_nonneg
      · intro t ht
        obtain ⟨r, hr, htr⟩ := not_bddAbove_iff.mp hB t
        obtain ⟨y, hy⟩ := hr
        exact hfill ht (hy ▸ htr.le)
    exact Or.inr (hequiv hSray)

end Metric
