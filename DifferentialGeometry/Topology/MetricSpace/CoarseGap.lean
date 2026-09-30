import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Topology

namespace IsPreconnected

variable {X : Type*} [PseudoMetricSpace X] {s : Set X}

theorem lt_iff_lt_of_coarse_bound (hs : IsPreconnected s) (f : X → ℝ)
    {C ε a b : ℝ} (hgap : ε < b - a)
    (hd : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ C * dist x y + ε)
    (havoid : ∀ x ∈ s, f x < a ∨ b < f x)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x < a ↔ f y < a := by
  apply hs.induction₂ (fun x y => f x < a ↔ f y < a) _
    (fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h.symm) hx hy
  intro z hz
  have hc : Continuous (fun w : X => C * dist z w + ε) :=
    (continuous_const.mul (continuous_const.dist continuous_id)).add continuous_const
  have hlim : Tendsto (fun w : X => C * dist z w + ε) (𝓝 z) (𝓝 ε) := by
    simpa only [ContinuousAt, dist_self, mul_zero, zero_add] using hc.continuousAt (x := z)
  have he := (hlim.eventually (gt_mem_nhds hgap)).filter_mono (nhdsWithin_le_nhds (s := s))
  filter_upwards [he, self_mem_nhdsWithin] with w hw hws
  have hdiff := abs_le.mp (hd z hz w hws)
  constructor
  · intro hza
    rcases havoid w hws with hw' | hw'
    · exact hw'
    · exfalso; linarith
  · intro hwa
    rcases havoid z hz with hz' | hz'
    · exact hz'
    · exfalso; linarith

end IsPreconnected
