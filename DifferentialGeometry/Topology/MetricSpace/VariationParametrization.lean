import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.MetricSpace.Lipschitz

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem dist_le_abs_variationOnFromTo_sub {c : unitInterval → X}
    (hc : BoundedVariationOn c univ) (s t : unitInterval) :
    dist (c s) (c t) ≤ |variationOnFromTo c univ 0 s - variationOnFromTo c univ 0 t| := by
  have hforward (u v : unitInterval) (huv : u ≤ v) :
      dist (c u) (c v) ≤ variationOnFromTo c univ 0 v - variationOnFromTo c univ 0 u := by
    rw [variationOnFromTo.sub_right hc.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _),
      variationOnFromTo.eq_of_le _ _ huv, univ_inter]
    exact (hc.mono (subset_univ _)).dist_le ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩
  rcases le_total s t with h | h
  · exact (hforward s t h).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · rw [dist_comm]
    exact (hforward t s h).trans (le_abs_self _)

theorem exists_lipschitz_parametrization_of_finite_variation
    (c : unitInterval → X) (hc : Continuous c) (hv : BoundedVariationOn c univ) :
    ∃ (φ : unitInterval → ℝ), Continuous φ ∧ Monotone φ ∧ φ 0 = 0 ∧
      φ 1 = (eVariationOn c univ).toReal ∧
      ∃ q : Icc (0 : ℝ) (eVariationOn c univ).toReal → X,
        LipschitzWith 1 q ∧
        q ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩⟩ = c 0 ∧
        q ⟨(eVariationOn c univ).toReal, ⟨ENNReal.toReal_nonneg, le_rfl⟩⟩ = c 1 ∧
        (∀ t, ∃ ht : φ t ∈ Icc (0 : ℝ) (eVariationOn c univ).toReal,
          q ⟨φ t, ht⟩ = c t) ∧
        ∀ s t, s ≤ t → eVariationOn q (Icc s t) = ENNReal.ofReal (t.val - s.val) := by
  classical
  let V := variationOnFromTo c univ (0 : unitInterval)
  have hVcont : Continuous V := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hv.continuousAt_variationOnFromTo_iff 0 t).mpr hc.continuousAt
  have hVmono : Monotone V := by
    intro s t hst
    exact variationOnFromTo.monotoneOn hv.locallyBoundedVariationOn (mem_univ _)
      (mem_univ _) (mem_univ _) hst
  have hV0 : V 0 = 0 := variationOnFromTo.self c univ 0
  have hall : Icc (0 : unitInterval) 1 = univ := by
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
  have hV1 : V 1 = (eVariationOn c univ).toReal := by
    dsimp [V]
    rw [variationOnFromTo.eq_of_le c univ unitInterval.nonneg', univ_inter, hall]
  have hVbounds (t : unitInterval) : V t ∈ Icc (0 : ℝ) (eVariationOn c univ).toReal := by
    constructor
    · rw [← hV0]; exact hVmono unitInterval.nonneg'
    · rw [← hV1]; exact hVmono unitInterval.le_one'
  have hsurj (t : Icc (0 : ℝ) (eVariationOn c univ).toReal) : ∃ s, V s = t.val := by
    apply intermediate_value_univ (0 : unitInterval) 1 hVcont
    simpa only [hV0, hV1] using t.property
  choose τ hτ using hsurj
  let q : Icc (0 : ℝ) (eVariationOn c univ).toReal → X := fun t => c (τ t)
  have hqLip : LipschitzWith 1 q := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hh := dist_le_abs_variationOnFromTo_sub hv (τ s) (τ t)
    change dist (q s) (q t) ≤ |V (τ s) - V (τ t)| at hh
    rw [hτ, hτ] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using hh
  have hqV (t : unitInterval) : q ⟨V t, hVbounds t⟩ = c t := by
    apply dist_le_zero.mp
    have hh := dist_le_abs_variationOnFromTo_sub hv (τ ⟨V t, hVbounds t⟩) t
    change dist (q ⟨V t, hVbounds t⟩) (c t) ≤ |V (τ ⟨V t, hVbounds t⟩) - V t| at hh
    simpa only [hτ, sub_self, abs_zero] using hh
  have hlength (s t : Icc (0 : ℝ) (eVariationOn c univ).toReal) (hst : s ≤ t) :
      eVariationOn q (Icc s t) = ENNReal.ofReal (t.val - s.val) := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · simp only [Icc_self, eVariationOn.subsingleton q (Set.subsingleton_singleton), sub_self,
        ENNReal.ofReal_zero]
    have hτst : τ s ≤ τ t := by
      by_contra hh
      have hvv := hVmono (le_of_not_ge hh)
      rw [hτ, hτ] at hvv
      exact (not_le_of_gt hst') hvv
    let ψ : unitInterval → Icc (0 : ℝ) (eVariationOn c univ).toReal := fun t => ⟨V t, hVbounds t⟩
    have hψ : Monotone ψ := fun _ _ hh => hVmono hh
    have hψs : ψ (τ s) = s := Subtype.ext (hτ s)
    have hψt : ψ (τ t) = t := Subtype.ext (hτ t)
    have hrange : ψ '' univ = univ := by
      apply Set.eq_univ_of_forall
      intro t
      exact ⟨τ t, mem_univ _, Subtype.ext (hτ t)⟩
    have hcomp : q ∘ ψ = c := funext hqV
    have hvar := eVariationOn.comp_inter_Icc_eq_of_monotoneOn q ψ (hψ.monotoneOn univ)
      (mem_univ (τ s)) (mem_univ (τ t))
    rw [hcomp, hrange, hψs, hψt, univ_inter, univ_inter] at hvar
    rw [← hvar]
    have hsub := variationOnFromTo.sub_right hv.locallyBoundedVariationOn
      (mem_univ (0 : unitInterval)) (mem_univ (τ t)) (mem_univ (τ s))
    rw [variationOnFromTo.eq_of_le c univ hτst, univ_inter] at hsub
    change V (τ t) - V (τ s) = _ at hsub
    rw [hτ, hτ] at hsub
    rw [hsub, ENNReal.ofReal_toReal (hv.mono (subset_univ _))]
  refine ⟨V, hVcont, hVmono, hV0, hV1, q, hqLip, ?_, ?_,
    (fun t => ⟨hVbounds t, hqV t⟩), hlength⟩
  · simpa only [hV0] using hqV 0
  · simpa only [hV1] using hqV 1

end Metric
