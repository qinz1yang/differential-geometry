import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem abs_redLength_sub_le_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x y : F.M) {tau U : ℝ} (htau : 0 < tau)
    (hx : redLength F.S 0 p x tau ≤ U) (hy : redLength F.S 0 p y tau ≤ U) :
    |redLength F.S 0 p x tau - redLength F.S 0 p y tau| ≤
      (Real.sqrt 3 / Real.sqrt tau * Real.sqrt U) *
        (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  have hnonneg (z : F.M) : 0 ≤ redLength F.S 0 p z tau := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
    intro s hs w
    simpa only [zero_sub] using (hC (-s) (by
      rw [ancientTimeInterval_carrier]
      exact neg_nonpos.mpr hs.1) w).1
  have hcont := continuous_redLength_of_ancient F hF p htau
  have hmin := fun z ↦ exists_lRegularized_minimizer_of_ancient F hF p z htau
  have hxy := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    F hF p x y htau hcont hmin
  have hyx := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    F hF p y x htau hcont hmin
  rw [riemannianEDistOf_comm (F.S.base.metric (-tau)) y x] at hyx
  have hdiff :
      |Real.sqrt (redLength F.S 0 p x tau) - Real.sqrt (redLength F.S 0 p y tau)| ≤
        Real.sqrt 3 / (2 * Real.sqrt tau) *
          (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum :
      Real.sqrt (redLength F.S 0 p x tau) + Real.sqrt (redLength F.S 0 p y tau) ≤
        2 * Real.sqrt U := by
    linarith [Real.sqrt_le_sqrt hx, Real.sqrt_le_sqrt hy]
  calc
    |redLength F.S 0 p x tau - redLength F.S 0 p y tau| =
        |(Real.sqrt (redLength F.S 0 p x tau) - Real.sqrt (redLength F.S 0 p y tau)) *
          (Real.sqrt (redLength F.S 0 p x tau) + Real.sqrt (redLength F.S 0 p y tau))| := by
      congr 1
      nlinarith [Real.sq_sqrt (hnonneg x), Real.sq_sqrt (hnonneg y)]
    _ = |Real.sqrt (redLength F.S 0 p x tau) - Real.sqrt (redLength F.S 0 p y tau)| *
        (Real.sqrt (redLength F.S 0 p x tau) + Real.sqrt (redLength F.S 0 p y tau)) := by
      rw [abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    _ ≤ (Real.sqrt 3 / (2 * Real.sqrt tau) *
        (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal) * (2 * Real.sqrt U) :=
      mul_le_mul hdiff hsum (by positivity) (by positivity)
    _ = _ := by ring

theorem abs_redLength_sub_le_of_time_lower_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p x y : F.M) {a tau U D : ℝ} (ha : 0 < a) (hat : a ≤ tau)
    (hx : redLength F.S 0 p x tau ≤ U) (hy : redLength F.S 0 p y tau ≤ U)
    (hdist : (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal ≤ D) :
    |redLength F.S 0 p x tau - redLength F.S 0 p y tau| ≤
      (Real.sqrt 3 / Real.sqrt a * Real.sqrt U) * D := by
  have hcoefficient : Real.sqrt 3 / Real.sqrt tau ≤ Real.sqrt 3 / Real.sqrt a :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr ha)
      (Real.sqrt_le_sqrt hat)
  calc
    |redLength F.S 0 p x tau - redLength F.S 0 p y tau| ≤
        (Real.sqrt 3 / Real.sqrt tau * Real.sqrt U) *
          (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal :=
      abs_redLength_sub_le_of_ancient F hF p x y (ha.trans_le hat) hx hy
    _ ≤ (Real.sqrt 3 / Real.sqrt a * Real.sqrt U) *
          (riemannianEDistOf (F.S.base.metric (-tau)) x y).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hdist (by positivity)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
