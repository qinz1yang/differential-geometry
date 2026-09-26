import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.WithTop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Lift

open Set Filter
open scoped Topology

namespace WithTop

theorem lowerSemicontinuousAt_of_continuousWithinAt_Iic_of_monotone_add
    {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {f : α → WithTop ℝ} {g : α → ℝ} {a : α}
    (hmono : Monotone (fun x => f x + (g x : WithTop ℝ)))
    (hleft : ContinuousWithinAt f (Iic a) a) (hg : ContinuousAt g a) :
    LowerSemicontinuousAt f a := by
  intro y hy
  have hleft' := hleft.lowerSemicontinuousWithinAt y hy
  have hyTop : y ≠ ⊤ := ne_top_of_lt hy
  lift y to ℝ using hyTop with y hyval
  obtain ⟨z, hyz, hzf⟩ := exists_between hy
  have hzTop : z ≠ ⊤ := ne_top_of_lt hzf
  lift z to ℝ using hzTop with z hzval
  have hyz' : y < z := WithTop.coe_lt_coe.mp hyz
  have hnear : ∀ᶠ x in 𝓝 a, g x < g a + (z - y) :=
    hg.eventually_lt_const (by linarith)
  have hright : ∀ᶠ x in 𝓝[≥] a, (y : WithTop ℝ) < f x := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hax
    by_cases hfx : f x = ⊤
    · rw [hfx]
      exact WithTop.coe_lt_top y
    · lift f x to ℝ using hfx with m hm
      have hbound := hmono hax
      change f a + (g a : WithTop ℝ) ≤ f x + (g x : WithTop ℝ) at hbound
      rw [← hm] at hbound
      by_contra hnot
      have hmy : m ≤ y := WithTop.coe_le_coe.mp (not_lt.mp hnot)
      have hzm : m + g x < z + g a := by linarith
      have hmid : (m : WithTop ℝ) + (g x : WithTop ℝ) <
          (z : WithTop ℝ) + (g a : WithTop ℝ) := by
        simpa only [← WithTop.coe_add] using WithTop.coe_lt_coe.mpr hzm
      have hlast : (z : WithTop ℝ) + (g a : WithTop ℝ) < f a + (g a : WithTop ℝ) := by
        exact WithTop.add_lt_add_right WithTop.coe_ne_top hzf
      exact (not_lt_of_ge hbound) (hmid.trans hlast)
  rw [← nhdsLE_sup_nhdsGE a]
  exact Filter.eventually_sup.mpr ⟨hleft', hright⟩

end WithTop
