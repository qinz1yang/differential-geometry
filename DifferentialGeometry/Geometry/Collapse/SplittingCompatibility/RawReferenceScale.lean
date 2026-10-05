import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RawScaleThreshold
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
An original splitting measured at its own scale is normalized at a reference centre without
changing its map. Inverse source scaling cancels exactly, leaving the reference metric and
the prescribed scaled original Euclidean coordinates with their original residual values.
-/

set_option autoImplicit false

noncomputable section

namespace GC.MetricGeometry

universe u v

theorem exists_reference_scaled_raw_splitting {X : Type u} {A : Type v}
    [mX : MetricSpace X] [mA : MetricSpace A] {k : ℕ} {p : X} {q : A}
    {ε δ c : ℝ} (hc : 0 < c)
    (f : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
      (mX.rescale c⁻¹ (inv_pos.mpr hc)) inferInstance p (WithLp.toLp 2 (0, q)) ε)
    (a : X) (hcmin : (1 / 2 : ℝ) ≤ c) (hcmax : c ≤ 2) (hδ : 0 < δ) (hδone : δ < 1)
    (C : ℝ) (hC : 0 ≤ C) (ha : dist a p ≤ C) (hε : ε ≤ rawScaleQuality δ (2 * C)) :
    let raw := @KleinerLottApprox.toFun X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
      (mX.rescale c⁻¹ (inv_pos.mpr hc)) inferInstance p (WithLp.toLp 2 (0, q)) ε f
    ∃ F : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
      mX (MetricSpace.scaledProduct inferInstance mA c hc)
      a (WithLp.toLp 2 (0, (raw a).snd)) δ,
      ∀ x, @KleinerLottApprox.toFun X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
        mX (MetricSpace.scaledProduct inferInstance mA c hc)
        a (WithLp.toLp 2 (0, (raw a).snd)) δ F x =
          WithLp.toLp 2 (c • ((raw x).fst - (raw a).fst), (raw x).snd) := by
  have hci : c⁻¹ ≤ 2 := by
    have hdiv : 1 / c ≤ 2 := (div_le_iff₀ hc).mpr (by linarith)
    simpa only [one_div] using hdiv
  have haold : @dist X (mX.rescale c⁻¹ (inv_pos.mpr hc)).toDist a p ≤ 2 * C := by
    rw [MetricSpace.rescale_dist]
    calc
      c⁻¹ * dist a p ≤ c⁻¹ * C := mul_le_mul_of_nonneg_left ha (inv_pos.mpr hc).le
      _ ≤ 2 * C := mul_le_mul_of_nonneg_right hci hC
  have hsource : (mX.rescale c⁻¹ (inv_pos.mpr hc)).rescale c hc = mX := by
    rw [MetricSpace.rescale_mul]
    simp only [mul_inv_cancel₀ hc.ne', MetricSpace.rescale_one]
  let ownSourceMetric : MetricSpace X := mX.rescale c⁻¹ (inv_pos.mpr hc)
  obtain ⟨hbudget, hdomain⟩ := rawScaleQuality_budgets hδ hδone
    (by positivity : 0 ≤ 2 * C) f.error_pos hε hcmin hcmax
  let F := f.recenterRescaleNormedProduct a hc hbudget hδone
    (by linarith only [haold, hdomain])
  have hF := f.recenterRescaleNormedProduct_apply a hc hbudget hδone
    (by linarith only [haold, hdomain])
  have hresult : ∃ G : @KleinerLottApprox X
      (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
      ((mX.rescale c⁻¹ (inv_pos.mpr hc)).rescale c hc)
      (MetricSpace.scaledProduct inferInstance mA c hc)
      a (WithLp.toLp 2 (0, (f.toFun a).snd)) δ,
      ∀ x, @KleinerLottApprox.toFun X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
        ((mX.rescale c⁻¹ (inv_pos.mpr hc)).rescale c hc)
        (MetricSpace.scaledProduct inferInstance mA c hc)
        a (WithLp.toLp 2 (0, (f.toFun a).snd)) δ G x =
          WithLp.toLp 2 (c • ((f.toFun x).fst - (f.toFun a).fst), (f.toFun x).snd) :=
    ⟨F, hF⟩
  rw [hsource] at hresult
  exact hresult

end GC.MetricGeometry
