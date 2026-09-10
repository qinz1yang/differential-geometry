import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas

open Set Function
set_option autoImplicit false
noncomputable section
namespace Poincare.Topology


def intervalPush {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε) where
  toFun t := ⟨max t.val (a + t.val / 2), t.property.1.trans (le_max_left _ _),
    max_le t.property.2 (by linarith [t.property.2])⟩
  continuous_toFun := by fun_prop

@[simp] theorem intervalPush_coe {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) (t : Icc (0 : ℝ) ε) :
    (intervalPush a haε t : ℝ) = max t.val (a + t.val / 2) := rfl


theorem strictMono_intervalPush {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε) :
    StrictMono (intervalPush a haε) := by
  intro s t hst
  change max s.val (a + s.val / 2) < max t.val (a + t.val / 2)
  exact max_lt_max hst (by change s.val < t.val at hst; linarith)


theorem intervalPush_fixed {ε : ℝ} (a : ℝ) (haε : 2 * a ≤ ε)
    (t : Icc (0 : ℝ) ε) (ht : 2 * a ≤ t.val) : intervalPush a haε t = t := by
  apply Subtype.ext
  exact max_eq_left (by linarith)


theorem range_intervalPush {a ε : ℝ} (haε : 2 * a ≤ ε) :
    range (intervalPush a haε) = {t : Icc (0 : ℝ) ε | a ≤ t.val} := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    change a ≤ max s.val (a + s.val / 2)
    exact (by linarith [s.property.1] : a ≤ a + s.val / 2).trans (le_max_right _ _)
  · intro ht
    change a ≤ t.val at ht
    by_cases hta : t.val ≤ 2 * a
    · let s : Icc (0 : ℝ) ε := ⟨2 * (t.val - a), by constructor <;> linarith⟩
      refine ⟨s, Subtype.ext ?_⟩
      change max (2 * (t.val - a)) (a + 2 * (t.val - a) / 2) = t.val
      have hh : a + 2 * (t.val - a) / 2 = t.val := by ring
      rw [hh, max_eq_right (by linarith)]
    · exact ⟨t, intervalPush_fixed a haε t (le_of_lt (lt_of_not_ge hta))⟩

end Poincare.Topology
