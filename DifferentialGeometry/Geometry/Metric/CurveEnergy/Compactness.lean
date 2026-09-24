import DifferentialGeometry.Geometry.Metric.CurveEnergy.Lipschitz
import DifferentialGeometry.Analysis.Sobolev.Interval.TraceCompactness

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [PseudoMetricSpace X]

theorem tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (γ : ℕ → ℝ → X) (v : ℝ → X)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ s t,
      riemannianEDistOf g (ι (γ n s)) (ι (γ n t)) ≤ (K : ℝ≥0∞) * edist s t)
    {a b B : ℝ} (hab : a < b)
    (hint : ∀ n, IntegrableOn (fun t => (riemannianCurveSpeed g (ι ∘ γ n) t) ^ 2) (Icc a b))
    (hbound : ∀ n, (∫ t in Icc a b, (riemannianCurveSpeed g (ι ∘ γ n) t) ^ 2) ≤ B)
    (hv : ContinuousOn v (Icc a b))
    (hae : ∀ᵐ t ∂volume.restrict (Icc a b), Tendsto (fun n => γ n t) atTop (𝓝 (v t))) :
    TendstoUniformlyOn γ v atTop (Icc a b) := by
  have hordered (n : ℕ) (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      dist (γ n s) (γ n t) ≤ Real.sqrt (B * (t - s)) := by
    obtain ⟨K, hK⟩ := hLip n
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have h := riemannianEDistOf_toReal_sq_le_interval_energy g hK hst ((hint n).mono_set hsub)
    have hmono : (∫ z in Icc s t, (riemannianCurveSpeed g (ι ∘ γ n) z) ^ 2) ≤ B :=
      (setIntegral_mono_set (hint n) (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hsub)).trans (hbound n)
    have heq : (riemannianEDistOf g (ι (γ n s)) (ι (γ n t))).toReal =
        dist (γ n s) (γ n t) := by rw [← hι, ← dist_edist]
    rw [heq] at h
    have hsq : dist (γ n s) (γ n t) ^ 2 ≤ B * (t - s) :=
      h.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hst)).trans_eq (mul_comm _ _))
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg] using hsqrt
  apply MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound (B := B) hab ?_ hv hae
  intro n s hs t ht
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hordered n s t hs ht hst
  · simpa only [dist_comm (γ n t) (γ n s), abs_of_nonneg (sub_nonneg.mpr hts)] using
      hordered n t s ht hs hts

end DifferentialGeometry.Geometry

end

end
