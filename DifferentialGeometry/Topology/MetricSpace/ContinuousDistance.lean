import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set

@[instance_reducible]
def MetricSpace.ofContinuousDistOfCompact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (d : X → X → ℝ) (hself : ∀ x, d x x = 0) (hcomm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hsep : ∀ x y, d x y = 0 → x = y)
    (hcont : Continuous fun p : X × X => d p.1 p.2) : MetricSpace X := by
  refine MetricSpace.ofDistTopology d hself hcomm htri ?_ hsep
  have hnonneg (x y : X) : 0 ≤ d x y := by
    have h := htri x y x
    rw [hself, hcomm y x] at h
    linarith
  intro s
  constructor
  · intro hs x hx
    by_cases hne : sᶜ.Nonempty
    · have hc : Continuous (d x) := hcont.comp (continuous_const.prodMk continuous_id)
      obtain ⟨y, hy, hmin⟩ := hs.isClosed_compl.isCompact.exists_isMinOn hne hc.continuousOn
      have hpos : 0 < d x y := lt_of_le_of_ne (hnonneg x y) (by
        intro hz
        have heq := hsep x y hz.symm
        exact hy (heq ▸ hx))
      refine ⟨d x y, hpos, fun z hz => ?_⟩
      by_contra hzs
      exact (not_lt_of_ge (hmin hzs)) hz
    · refine ⟨1, zero_lt_one, fun y _ => ?_⟩
      by_contra hy
      exact hne ⟨y, hy⟩
  · intro hs
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨epsilon, hepsilon, hball⟩ := hs x hx
    have hc : Continuous (d x) := hcont.comp (continuous_const.prodMk continuous_id)
    apply Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds ?_) hball
    simpa only [mem_ofPred_eq, hself] using hepsilon
