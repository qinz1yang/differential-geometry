import DifferentialGeometry.Analysis.TimeInterval
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open scoped BigOperators

variable {M : Type*}

def towerReactionSum (w : ℕ -> Real -> M -> Real) (c : Real) (k : ℕ) (t : Real) (x : M) : Real :=
  ∑ j ∈ Finset.range (k + 1),
    c * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)

def TowerHeatBoundOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (w wLap : ℕ -> Real -> M -> Real) (c : Real) (k : ℕ) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    ∃ d : Real,
      HasDerivWithinAt (fun s : Real => w k s x) d D.carrier (t : Real) ∧
      d ≤ wLap k (t : Real) x +
        (-2 * w (k + 1) (t : Real) x + towerReactionSum (M := M) w c k (t : Real) x)

theorem towerReactionSum_mono_const
    (w : ℕ -> Real -> M -> Real) {c c' : Real} (hcc : c <= c')
    (k : ℕ) (t : Real) (x : M) :
    towerReactionSum (M := M) w c k t x <= towerReactionSum (M := M) w c' k t x := by
  unfold towerReactionSum
  apply Finset.sum_le_sum
  intro j _
  have h1 : 0 <= Real.sqrt (w j t x) := Real.sqrt_nonneg _
  have h2 : 0 <= Real.sqrt (w (k - j) t x) := Real.sqrt_nonneg _
  have h3 : 0 <= Real.sqrt (w k t x) := Real.sqrt_nonneg _
  have hprod : 0 <= Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) :=
    mul_nonneg (mul_nonneg h1 h2) h3
  calc c * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)
      = c * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) := by ring
    _ <= c' * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) :=
        mul_le_mul_of_nonneg_right hcc hprod
    _ = c' * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) := by ring

theorem TowerHeatBoundOn.mono_const
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {w wLap : ℕ -> Real -> M -> Real} {c₀ c₁ : Real} {k : ℕ}
    (hc : c₀ ≤ c₁) (h : TowerHeatBoundOn (D := D) w wLap c₀ k) :
    TowerHeatBoundOn (D := D) w wLap c₁ k := by
  intro t x
  obtain ⟨d, hd, hle⟩ := h t x
  refine ⟨d, hd, hle.trans ?_⟩
  apply add_le_add_right
  apply add_le_add_right
  exact towerReactionSum_mono_const w hc k (t : Real) x

end DifferentialGeometry.Analysis.Parabolic
