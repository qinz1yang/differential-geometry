import DifferentialGeometry.Topology.Engulfing.Prism.Prism
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Piecewise

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

theorem exists_continuous_extension_zero_outside_of_frontier {Z : Type*}
    [TopologicalSpace Z] [NormalSpace Z] {F : Set Z} (hF : IsClosed F)
    {q : F → ℝ} (hq : Continuous q) (hfrontier : ∀ z : F, z.1 ∈ frontier F → q z = 0) :
    ∃ Q : Z → ℝ, Continuous Q ∧ (∀ z : F, Q z = q z) ∧
      ∀ z ∉ interior F, Q z = 0 := by
  classical
  obtain ⟨q', hq'⟩ := ContinuousMap.exists_restrict_eq hF (⟨q, hq⟩ : C(F, ℝ))
  have hq'eq (z : F) : q' z = q z := congrArg (fun h : C(F, ℝ) => h z) hq'
  let Q : Z → ℝ := F.piecewise q' 0
  have hQ : Continuous Q := by
    apply continuous_piecewise (fun z hz => ?_) q'.continuous.continuousOn
      continuous_const.continuousOn
    have hzF : z ∈ F := hF.closure_eq ▸ hz.1
    exact (hq'eq ⟨z, hzF⟩).trans (hfrontier ⟨z, hzF⟩ hz)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro z
    change F.piecewise q' 0 z = q z
    rw [piecewise_eq_of_mem _ _ _ z.2]
    exact hq'eq z
  · intro z hz
    by_cases hzF : z ∈ F
    · rw [show Q z = q' z from piecewise_eq_of_mem _ _ _ hzF, hq'eq ⟨z, hzF⟩]
      exact hfrontier ⟨z, hzF⟩ ⟨subset_closure hzF, hz⟩
    · exact piecewise_eq_of_notMem _ _ _ hzF

theorem exists_continuous_prism_extension {Z : Type*} [TopologicalSpace Z] [NormalSpace Z]
    {F : Set Z} (hF : IsClosed F) {f g : F → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, f z ≤ g z) (hboundary : ∀ z : F, z.1 ∈ frontier F → f z = g z) :
    ∃ f' g' : Z → ℝ, Continuous f' ∧ Continuous g' ∧ (∀ z, f' z ≤ g' z) ∧
      (∀ z : F, f' z = f z ∧ g' z = g z) ∧
      ∀ z ∉ interior F, f' z = g' z := by
  obtain ⟨f', hf'⟩ := ContinuousMap.exists_restrict_eq hF (⟨f, hf⟩ : C(F, ℝ))
  have hf'eq (z : F) : f' z = f z := congrArg (fun h : C(F, ℝ) => h z) hf'
  obtain ⟨Q, hQ, hQeq, hQzero⟩ := exists_continuous_extension_zero_outside_of_frontier
    hF (hg.sub hf) (fun z hz => sub_eq_zero.mpr (hboundary z hz).symm)
  have hQnonneg (z : Z) : 0 ≤ Q z := by
    by_cases hz : z ∈ F
    · rw [hQeq ⟨z, hz⟩]
      exact sub_nonneg.mpr (hfg ⟨z, hz⟩)
    · rw [hQzero z (fun hi => hz (interior_subset hi))]
  refine ⟨f', fun z => f' z + Q z, f'.continuous, f'.continuous.add hQ,
    fun z => le_add_of_nonneg_right (hQnonneg z), ?_, ?_⟩
  · intro z
    refine ⟨hf'eq z, ?_⟩
    change f' z + Q z = g z
    rw [hf'eq z, hQeq z, Pi.sub_apply]
    ring
  · intro z hz
    change f' z = f' z + Q z
    rw [hQzero z hz, add_zero]

theorem exists_transverse_closed_prism_engulfing {Y Z : Type*}
    [MetricSpace Y] [MetricSpace Z] (o : Y) {F : Set Z} (hF : IsClosed F)
    {f g : F → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : ∀ z, f z ≤ g z)
    (hboundary : ∀ z : F, z.1 ∈ frontier F → f z = g z)
    {U W : Set ((Y × Z) × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hgraph : ∀ z : F, ((o, z.1), f z) ∈ U)
    (hprism : ∀ (z : F) t, t ∈ Icc (f z) (g z) → ((o, z.1), t) ∈ W) :
    ∃ H : ((Y × Z) × ℝ) ≃ₜ ((Y × Z) × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p, p.1.2 ∉ interior F → H p = p) ∧
      ∀ (z : F) t, t ∈ Icc (f z) (g z) → ((o, z.1), t) ∈ H '' U := by
  obtain ⟨f', g', hf', hg', hfg', heq, hdeg⟩ :=
    exists_continuous_prism_extension hF hf hg hfg hboundary
  let A : Set (Y × Z) := {o} ×ˢ F
  have hA : IsClosed A := isClosed_singleton.prod hF
  obtain ⟨H, hHfst, hHfix, hHdeg, hHprism⟩ := exists_engulfing_over_closed_set hA
    (hf'.comp continuous_snd) (hg'.comp continuous_snd) (fun x => hfg' x.2) hU hW
    (by
      rintro ⟨y, z⟩ ⟨hy, hz⟩
      change y = o at hy
      subst y
      change ((o, z), f' z) ∈ U
      rw [(heq ⟨z, hz⟩).1]
      exact hgraph ⟨z, hz⟩)
    (by
      rintro ⟨y, z⟩ ⟨hy, hz⟩ t ht
      change y = o at hy
      subst y
      apply hprism ⟨z, hz⟩ t
      change t ∈ Icc (f' z) (g' z) at ht
      simpa only [(heq ⟨z, hz⟩).1, (heq ⟨z, hz⟩).2] using ht)
  refine ⟨H, hHfst, hHfix, ?_, ?_⟩
  · intro p hp
    exact hHdeg p.1 (hdeg p.1.2 hp) p.2
  · intro z t ht
    apply hHprism (o, z.1) ⟨rfl, z.2⟩ t
    change t ∈ Icc (f' z) (g' z)
    simpa only [(heq z).1, (heq z).2] using ht

end DifferentialGeometry.Topology.Engulfing
