import DifferentialGeometry.Topology.MetricSpace.VariationParametrization

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_short_curve_prefix
    {p a : X} {η : ℝ} (hη : 0 < η)
    (c : unitInterval → X) (hc : Continuous c) (hc0 : c 0 = p) (hc1 : c 1 = a)
    (hlen : eVariationOn c univ < ENNReal.ofReal (dist p a + η)) :
    ∃ q : Icc (0 : ℝ) (dist p a) → X, LipschitzWith 1 q ∧
      q ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
      (∀ t, dist (q t) a < dist p a + η - t.val) ∧
      (∀ t, t.val - η ≤ dist p (q t) ∧ dist p (q t) ≤ t.val) ∧
      (∀ s t, s ≤ t → t.val - s.val - η ≤ dist (q s) (q t) ∧
        dist (q s) (q t) ≤ t.val - s.val) ∧
      ∀ t, q t ∈ range c := by
  have hv : BoundedVariationOn c univ := (hlen.trans_le le_top).ne
  let ℓ := (eVariationOn c univ).toReal
  have hℓ : ℓ < dist p a + η := by
    exact (ENNReal.toReal_lt_toReal hv ENNReal.ofReal_ne_top).mpr hlen |>.trans_eq
      (ENNReal.toReal_ofReal (by linarith [dist_nonneg (x := p) (y := a)]))
  have hdℓ : dist p a ≤ ℓ := by
    simpa only [hc0, hc1] using hv.dist_le (mem_univ (0 : unitInterval)) (mem_univ 1)
  obtain ⟨φ, hφc, hφm, hφ0, hφ1, Q, hQ, hQ0, hQ1, hQφ, hQvar⟩ :=
    exists_lipschitz_parametrization_of_finite_variation c hc hv
  let incl : Icc (0 : ℝ) (dist p a) → Icc (0 : ℝ) ℓ :=
    fun t => ⟨t.val, ⟨t.property.1, t.property.2.trans hdℓ⟩⟩
  let q := Q ∘ incl
  have hq : LipschitzWith 1 q := by
    have hi : Isometry incl := Isometry.of_dist_eq (fun _ _ => rfl)
    simpa only [mul_one] using hQ.comp hi.lipschitzWith
  have hq0 : q ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p := hQ0.trans hc0
  have htail (t : Icc (0 : ℝ) (dist p a)) : dist (q t) a < dist p a + η - t.val := by
    have hh := hQ.dist_le_mul (incl t) ⟨ℓ, ⟨ENNReal.toReal_nonneg, le_rfl⟩⟩
    rw [hQ1, hc1] at hh
    change dist (q t) a ≤ 1 * |t.val - ℓ| at hh
    rw [one_mul, abs_of_nonpos (sub_nonpos.mpr (t.property.2.trans hdℓ))] at hh
    linarith
  have hrad (t : Icc (0 : ℝ) (dist p a)) : dist p (q t) ≤ t.val := by
    have hh := hq.dist_le_mul ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ t
    rw [hq0] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, zero_sub,
      abs_neg, abs_of_nonneg t.property.1] using hh
  refine ⟨q, hq, hq0, htail, ?_, ?_, ?_⟩
  · intro t
    exact ⟨by linarith [dist_triangle p (q t) a, htail t], hrad t⟩
  · intro s t hst
    have hh := hq.dist_le_mul s t
    change dist (q s) (q t) ≤ 1 * |s.val - t.val| at hh
    rw [one_mul, abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst))] at hh
    exact ⟨by linarith [dist_triangle4 p (q s) (q t) a, hrad s, htail t], by linarith⟩
  · intro t
    obtain ⟨s, hs⟩ := intermediate_value_univ (0 : unitInterval) 1 hφc
      (show t.val ∈ Icc (φ 0) (φ 1) by rw [hφ0, hφ1]; exact (incl t).property)
    obtain ⟨ht, hqt⟩ := hQφ s
    refine ⟨s, ?_⟩
    have hsub : (⟨φ s, ht⟩ : Icc (0 : ℝ) ℓ) = incl t := Subtype.ext hs
    rw [hsub] at hqt
    exact hqt.symm

end Metric
