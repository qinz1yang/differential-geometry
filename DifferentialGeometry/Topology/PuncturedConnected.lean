import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

theorem isPreconnected_compl_singleton_of_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hc : IsConnected (U \ {p})) : IsPreconnected ({p}ᶜ : Set X) := by
  classical
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  obtain ⟨q, hq⟩ := hc.nonempty
  let g := Function.update f p (f q)
  have hfg (z : X) (hz : z ≠ p) : g z = f z := Function.update_of_ne hz _ _
  have hgU : ∀ z ∈ U, g z = f q := by
    intro z hz
    by_cases hzp : z = p
    · subst z
      simp [g]
    · rw [hfg z hzp]
      exact hc.isPreconnected.constant (hf.mono (by
        intro w hw
        exact hw.2)) ⟨hz, hzp⟩ hq
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hzp : z = p
    · subst z
      apply continuousAt_const.congr
      exact Filter.eventuallyEq_of_mem hU fun z hz => (hgU z hz).symm
    · apply (continuousAt_update_of_ne hzp).mpr
      exact (hf z hzp).continuousAt (isOpen_compl_singleton.mem_nhds hzp)
  have hxy : g x = g y := IsPreconnected.constant isPreconnected_univ hg.continuousOn
    (mem_univ x) (mem_univ y)
  rwa [hfg x hx, hfg y hy] at hxy

theorem isPathConnected_compl_singleton_of_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    [LocallyPathConnectedSpace X] (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hc : IsConnected (U \ {p})) :
    IsPathConnected ({p}ᶜ : Set X) := by
  apply isOpen_compl_singleton.isConnected_iff_isPathConnected.mp
  obtain ⟨z, hz⟩ := hc.nonempty
  exact ⟨⟨z, hz.2⟩, isPreconnected_compl_singleton_of_punctured_neighborhood p hU hc⟩


theorem Metric.isPathConnected_ball_sdiff_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r \ {x}) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall x r
  have heinj : Function.Injective e := by
    intro y z hyz
    exact e.injOn (by simp [e]) (by simp [e]) hyz
  have herange : Set.range e = Metric.ball x r := by
    simpa only [e, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.univBall_target x hr, Set.image_univ] using
      e.image_source_eq_target
  have heimage : e '' ({0}ᶜ : Set E) = Metric.ball x r \ {x} := by
    rw [Set.image_compl_eq_range_sdiff_image heinj, herange, Set.image_singleton]
    simp only [e, OpenPartialHomeomorph.univBall_apply_zero]
  rw [← heimage]
  exact (isPathConnected_compl_singleton_of_one_lt_rank h 0).image
    (OpenPartialHomeomorph.continuous_univBall x r)
