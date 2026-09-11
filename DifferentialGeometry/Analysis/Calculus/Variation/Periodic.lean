import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic







noncomputable section

open Set Function
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {X : Type*} [PseudoEMetricSpace X]


theorem eVariationOn_comp_add (f : ℝ → X) {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    eVariationOn (fun x => f (x + c)) (Icc a b) = eVariationOn f (Icc (a + c) (b + c)) := by
  have hm : Monotone (fun x : ℝ => x + c) := monotone_id.add_const c
  have h := eVariationOn.comp_eq_of_monotoneOn f (fun x : ℝ => x + c) (hm.monotoneOn (Icc a b))
  have hi : (fun x : ℝ => x + c) '' Icc a b = Icc (a + c) (b + c) := by
    simpa only [id_eq] using (continuous_id.add_const c).continuousOn.image_Icc_of_monotoneOn hab (hm.monotoneOn _)
  rw [hi] at h
  exact h


theorem eVariationOn_add_period {f : ℝ → X} {c : ℝ} (hf : Periodic f c)
    {a b : ℝ} (hab : a ≤ b) :
    eVariationOn f (Icc (a + c) (b + c)) = eVariationOn f (Icc a b) := by
  rw [← eVariationOn_comp_add f hab c]
  congr 1
  exact funext hf



theorem eVariationOn_unit_period {f : ℝ → X} (hf : Periodic f 1) (a : ℝ) :
    eVariationOn f (Icc a (a + 1)) = eVariationOn f (Icc 0 1) := by
  have hbase (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      eVariationOn f (Icc r (r + 1)) = eVariationOn f (Icc 0 1) := by
    have h₁ := eVariationOn.Icc_add_Icc f (s := univ) hr.2
      (by linarith [hr.1] : (1 : ℝ) ≤ r + 1) (mem_univ 1)
    have h₂ := eVariationOn.Icc_add_Icc f (s := univ) hr.1 hr.2 (mem_univ r)
    simp only [univ_inter] at h₁ h₂
    have hp : eVariationOn f (Icc 1 (r + 1)) = eVariationOn f (Icc 0 r) := by
      simpa only [zero_add] using eVariationOn_add_period hf hr.1
    rw [← h₁, hp, add_comm, h₂]
  have hp : Periodic f (⌊a⌋ : ℝ) := by simpa only [mul_one] using hf.int_mul ⌊a⌋
  have h := eVariationOn_add_period hp (a := Int.fract a) (b := Int.fract a + 1)
    (by linarith)
  have ha : Int.fract a + (⌊a⌋ : ℝ) = a := Int.fract_add_floor a
  have hb : Int.fract a + 1 + (⌊a⌋ : ℝ) = a + 1 := by linarith
  rw [ha, hb] at h
  exact h.trans (hbase _ ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩)



theorem eVariationOn_comp_monotone_lift {f : ℝ → X} (hf : Periodic f 1)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hm : Monotone ψ)
    (hp : ∀ t, ψ (t + 1) = ψ t + 1) :
    eVariationOn (f ∘ ψ) (Icc 0 1) = eVariationOn f (Icc 0 1) := by
  rw [eVariationOn.comp_eq_of_monotoneOn f ψ (hm.monotoneOn _),
    hψ.continuousOn.image_Icc_of_monotoneOn zero_le_one (hm.monotoneOn _)]
  have h := hp 0
  rw [zero_add] at h
  rw [h, eVariationOn_unit_period hf]

end DifferentialGeometry.Analysis
