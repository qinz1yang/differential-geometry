import DifferentialGeometry.Analysis.ODE.ReciprocalTimeBarrier
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

open DifferentialGeometry.Analysis Set

namespace ContinuousMap

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]

theorem fundamentalGroup_map_injective_of_area_obstructions (f : C(S, X))
    (obstructions : ∀ x : S, ¬ Function.Injective (FundamentalGroup.map f x) →
      ∃ (T c b : ℝ) (A : ℝ → ℝ), 0 < T + c ∧ 0 < b ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - b))) :
    ∀ x : S, Function.Injective (FundamentalGroup.map f x) := by
  intro x
  by_contra h
  obtain ⟨T, c, b, A, hT, hb, hc, hn, hs⟩ := obstructions x h
  apply not_nonnegative_of_upper_barriers_div_time A T c (3 / 4) b hT (by norm_num) hb hc hn
  intro t ht
  convert hs t ht using 1
  rw [div_mul_eq_div_div]
  ring

end ContinuousMap
