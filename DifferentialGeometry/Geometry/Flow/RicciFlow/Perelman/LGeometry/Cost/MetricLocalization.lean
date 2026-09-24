import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Localization
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Minimizing

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

private theorem radius_bound
    (b r d R Q : ℝ) (hb : 0 < b) (hr : 0 < r) (hd : 0 ≤ d)
    (hdist : d ≤ r / 4) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hQtwo : Q ≤ 2)
    (hsmall : 32 * b ^ 4 * R ≤ r ^ 2) :
    Real.sqrt b * Real.sqrt (Q * (Q * (d ^ 2 / b) + 8 * b ^ 3 * R)) < r := by
  have hbudget : 0 ≤ Q * (Q * (d ^ 2 / b) + 8 * b ^ 3 * R) := by positivity
  have hsquare : (Real.sqrt b *
      Real.sqrt (Q * (Q * (d ^ 2 / b) + 8 * b ^ 3 * R))) ^ 2 =
      Q ^ 2 * d ^ 2 + 8 * Q * b ^ 4 * R := by
    rw [mul_pow, Real.sq_sqrt hb.le, Real.sq_sqrt hbudget]
    field_simp
  have hd2 : d ^ 2 ≤ r ^ 2 / 16 := by
    have hh := (sq_le_sq₀ hd (by positivity : 0 ≤ r / 4)).mpr hdist
    nlinarith
  have hQ2 : Q ^ 2 ≤ 4 := by nlinarith
  have hpart : Q ^ 2 * d ^ 2 ≤ r ^ 2 / 4 := by
    have hh := mul_le_mul hQ2 hd2 (sq_nonneg d) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have htail : 8 * Q * b ^ 4 * R ≤ r ^ 2 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hQtwo (by positivity : 0 ≤ 8 * b ^ 4 * R)
    nlinarith
  have htotal : Q ^ 2 * d ^ 2 + 8 * Q * b ^ 4 * R < r ^ 2 := by
    nlinarith [sq_pos_of_pos hr]
  have hnn := mul_nonneg (Real.sqrt_nonneg b)
    (Real.sqrt_nonneg (Q * (Q * (d ^ 2 / b) + 8 * b ^ 3 * R)))
  nlinarith

section ComparisonCurve

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_contMDiff_curve_energy_eq_and_radius_bound
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (C b r : ℝ) (hb : 0 < b) (hr : 0 < r)
    (x y : M) (hdist : riemannianEDistOf g x y ≤ ENNReal.ofReal (r / 4))
    (htime : 2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2 ≤ Real.log 2)
    (hsmall : 32 * b ^ 4 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C ≤ r ^ 2) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α 0 = x ∧ α b = y ∧
      curveEnergy g α 0 b = (riemannianEDistOf g x y).toReal ^ 2 / b ∧
      Real.sqrt b * Real.sqrt
        (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
          (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
            curveEnergy g α 0 b + 8 * b ^ 3 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C)) < r := by
  have hfin : riemannianEDistOf g x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist
  obtain ⟨α, hα, h0, h1, henergy⟩ := exists_contMDiff_curve_energy_eq_riemannianEDistOf_sq_div
    g hg x y hfin b hb
  refine ⟨α, hα, h0, h1, henergy, ?_⟩
  rw [henergy]
  let Q := Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2)
  let R := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have hQ : Q ≤ 2 := (Real.exp_le_exp.mpr htime).trans_eq (Real.exp_log (by norm_num))
  have hreal : (riemannianEDistOf g x y).toReal ≤ r / 4 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r / 4)] using hh
  have hsmall' : 32 * b ^ 4 * R ≤ r ^ 2 := by simpa only [R, mul_assoc] using hsmall
  simpa only [Q, R, mul_assoc] using radius_bound b r
    (riemannianEDistOf g x y).toReal R Q hb hr ENNReal.toReal_nonneg
    hreal (by positivity) (Real.exp_pos _).le hQ hsmall'

end ComparisonCurve

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

theorem exists_contMDiff_lCost_minimizer_in_ball_of_distance_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (C T b r : ℝ) (hb : 0 < b) (hr : 0 < r)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ C)
    (x y : M)
    (hdist : riemannianEDistOf (S.base.metric T) x y ≤ ENNReal.ofReal (r / 4))
    (htime : 2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * b ^ 2 ≤ Real.log 2)
    (hsmall : 32 * b ^ 4 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C ≤ r ^ 2) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α 0 = x ∧ α b = y ∧
      lLength S T (squareRootReparametrization α) 0 (b ^ 2) = lCost S T x y (b ^ 2) ∧
      ∀ s ∈ Icc 0 b, riemannianEDistOf (S.base.metric T) x (α s) < ENNReal.ofReal r := by
  obtain ⟨α₀, hα₀, h0, h1, _, hgap⟩ := exists_contMDiff_curve_energy_eq_and_radius_bound
    (S.base.metric T) (RiemannianMetricComplete.of_compact _) C b r hb hr x y hdist htime hsmall
  exact exists_contMDiff_lCost_minimizer_in_ball_of_curvature_bound S hS C T b r hb hreg hRm
    x y α₀ (hα₀.of_le (by simp)) h0 h1 hgap

end DifferentialGeometry.PDE.RicciFlow.Perelman
