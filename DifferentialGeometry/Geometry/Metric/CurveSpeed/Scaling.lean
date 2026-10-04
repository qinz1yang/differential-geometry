import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem distance_parametrized_segment_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (gamma : ℝ → M) {ell : ℝ} (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hmin : ∀ s ∈ Icc 0 ell, ∀ t ∈ Icc 0 ell,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t => gamma (t / Real.sqrt c)) ∧
      (fun t => gamma (t / Real.sqrt c)) 0 = gamma 0 ∧
      (fun t => gamma (t / Real.sqrt c)) (Real.sqrt c * ell) = gamma ell ∧
      ∀ s ∈ Icc 0 (Real.sqrt c * ell), ∀ t ∈ Icc 0 (Real.sqrt c * ell),
        riemannianEDistOf (scaleMetric c hc g) (gamma (s / Real.sqrt c))
          (gamma (t / Real.sqrt c)) = ENNReal.ofReal |s - t| := by
  have hk := Real.sqrt_pos.mpr hc
  refine ⟨hsmooth.comp (contMDiff_iff_contDiff.mpr (contDiff_id.div_const _)),
    by simp, by dsimp only; rw [mul_div_cancel_left₀ ell hk.ne'], ?_⟩
  intro s hs t ht
  have hs' : s / Real.sqrt c ∈ Icc (0 : ℝ) ell :=
    ⟨div_nonneg hs.1 hk.le, (div_le_iff₀ hk).mpr (by simpa [mul_comm] using hs.2)⟩
  have ht' : t / Real.sqrt c ∈ Icc (0 : ℝ) ell :=
    ⟨div_nonneg ht.1 hk.le, (div_le_iff₀ hk).mpr (by simpa [mul_comm] using ht.2)⟩
  rw [edistOf_scale, hmin _ hs' _ ht', ← ENNReal.ofReal_mul hk.le]
  congr 1
  rw [← sub_div, abs_div, abs_of_pos hk, mul_div_cancel₀ _ hk.ne']

end DifferentialGeometry.Geometry
