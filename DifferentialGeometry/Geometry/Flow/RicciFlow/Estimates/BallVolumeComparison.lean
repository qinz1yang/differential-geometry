import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison

set_option autoImplicit false
noncomputable section

open Set Manifold Bundle
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem riemannianVolumeMeasure_ball_le_exp_mul_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C s t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ u ∈ Icc a b, ∀ x : M,
      normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (p : M) (r : ℝ) :
    riemannianVolumeMeasure I M (S.base.metric s)
      (riemannianBallOf (S.base.metric s) p r) ≤
      ENNReal.ofReal
        (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * Real.sqrt C * |s - t|)) *
      riemannianVolumeMeasure I M (S.base.metric t)
        (riemannianBallOf (S.base.metric t) p
          (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) * r)) := by
  let c := 2 * (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|
  have hst (x : M) (v : TangentSpace I x) :
      (S.base.metric s).inner x v v ≤ Real.exp c * (S.base.metric t).inner x v v :=
    (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x
      (fun u hu => hRm u hu x) hs ht v).2
  have hts (x : M) (v : TangentSpace I x) :
      (S.base.metric t).inner x v v ≤ Real.exp c * (S.base.metric s).inner x v v := by
    have h := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x
      (fun u hu => hRm u hu x) ht hs v).2
    rwa [abs_sub_comm t s] at h
  have h := Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds
    (S.base.metric s) (S.base.metric t) (Real.exp_pos c) (Real.exp_pos c) p r
    (fun x _ v => hst x v) hts
  have hsqrt : Real.sqrt (Real.exp c) =
      Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |s - t|) := by
    rw [← Real.exp_half]
    congr 1
    dsimp [c]
    ring
  have hvol : Real.sqrt (Real.exp c ^ Module.finrank ℝ E) =
      Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * Real.sqrt C * |s - t|) := by
    rw [← Real.exp_nat_mul, ← Real.exp_half]
    congr 1
    dsimp [c]
    ring
  simpa only [hsqrt, hvol] using h


theorem riemannianVolumeMeasure_ball_initial_le_exp_mul_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T K t : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcarrier : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hRm : ∀ u ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric u) x 4 (S.base.rm04 u x)) ≤ K)
    (ht : t ∈ Icc 0 T) (p : M) (r : ℝ) :
    riemannianVolumeMeasure I M (S.base.metric 0)
      (riemannianBallOf (S.base.metric 0) p r) ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * K * t)) *
      riemannianVolumeMeasure I M (S.base.metric t)
        (riemannianBallOf (S.base.metric t) p
          (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * t) * r)) := by
  have hsq : ∀ u ∈ Icc 0 T, ∀ x : M,
      normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ K ^ 2 := by
    intro u hu x
    exact (Real.sqrt_le_iff.mp (hRm u hu x)).2
  have h := riemannianVolumeMeasure_ball_le_exp_mul_of_curvature_bound S hS
    hcarrier hregular hsq (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht p r
  simpa only [Real.sqrt_sq hK, zero_sub, abs_neg, abs_of_nonneg ht.1] using h


theorem riemannianVolumeMeasure_ball_ge_of_initial_volume_and_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T K t : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcarrier : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hRm : ∀ u ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric u) x 4 (S.base.rm04 u x)) ≤ K)
    (ht : t ∈ Icc 0 T) (p : M) {r : ℝ} (hr : 0 ≤ r) {v : ℝ≥0∞}
    (hinitial : v ≤ riemannianVolumeMeasure I M (S.base.metric 0)
      (riemannianBallOf (S.base.metric 0) p
        (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 * K * T)) * r))) :
    ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 3 * K * T))) * v ≤
      riemannianVolumeMeasure I M (S.base.metric t)
        (riemannianBallOf (S.base.metric t) p r) := by
  let A := (Module.finrank ℝ E : ℝ) ^ 2 * K
  let B := (Module.finrank ℝ E : ℝ) ^ 3 * K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrad : Real.exp (A * t) * (Real.exp (-(A * T)) * r) ≤ r := by
    rw [← mul_assoc, ← Real.exp_add]
    apply (mul_le_mul_of_nonneg_right
      (show Real.exp (A * t + -(A * T)) ≤ 1 by
        rw [Real.exp_le_one_iff]
        have h := mul_le_mul_of_nonneg_left ht.2 hA
        linarith) hr).trans_eq
    exact one_mul r
  have hvol := riemannianVolumeMeasure_ball_initial_le_exp_mul_of_curvature_bound
    S hS hT hK hcarrier hregular hRm ht p (Real.exp (-(A * T)) * r)
  have hupper : v ≤ ENNReal.ofReal (Real.exp (B * T)) *
      riemannianVolumeMeasure I M (S.base.metric t)
        (riemannianBallOf (S.base.metric t) p r) := by
    apply hinitial.trans (hvol.trans ?_)
    apply mul_le_mul'
    · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2 hB))
    · exact MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hrad)
  change ENNReal.ofReal (Real.exp (-(B * T))) * v ≤ _
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(B * T))) *
        (ENNReal.ofReal (Real.exp (B * T)) *
          riemannianVolumeMeasure I M (S.base.metric t)
            (riemannianBallOf (S.base.metric t) p r)) := mul_le_mul' le_rfl hupper
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem riemannianVolumeMeasure_ball_ge_of_initial_volume_ratio_and_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T K t κ R : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcarrier : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hRm : ∀ u ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric u) x 4 (S.base.rm04 u x)) ≤ K)
    (ht : t ∈ Icc 0 T) (p : M)
    (hinitial : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      ENNReal.ofReal κ * ENNReal.ofReal ρ ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure I M (S.base.metric 0) (riemannianBallOf (S.base.metric 0) p ρ))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal (Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 3 * K * T)) * κ) *
      ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M (S.base.metric t) (riemannianBallOf (S.base.metric t) p r) := by
  let n := Module.finrank ℝ E
  let a := Real.exp (-((n : ℝ)^2 * K * T))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have harp : 0 < a * r := mul_pos ha hr
  have harR : a * r ≤ R := (mul_le_mul_of_nonneg_right ha1 hr.le).trans_eq (one_mul r) |>.trans hrR
  have h := riemannianVolumeMeasure_ball_ge_of_initial_volume_and_curvature_bound
    S hS hT hK hcarrier hregular hRm ht p hr.le (hinitial (a * r) harp harR)
  have hexp : Real.exp (-((n : ℝ)^3 * K * T)) * a ^ n =
      Real.exp (-(2 * (n : ℝ)^3 * K * T)) := by
    dsimp only [a]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have heq : ENNReal.ofReal (Real.exp (-((n : ℝ)^3 * K * T))) *
      (ENNReal.ofReal κ * ENNReal.ofReal (a * r) ^ n) =
      ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)^3 * K * T)) * κ) * ENNReal.ofReal r ^ n := by
    rw [ENNReal.ofReal_mul ha.le, mul_pow]
    calc
      _ = (ENNReal.ofReal (Real.exp (-((n : ℝ)^3 * K * T))) *
          ENNReal.ofReal a ^ n) * ENNReal.ofReal κ * ENNReal.ofReal r ^ n := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_pow ha.le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, hexp,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [← heq]
  exact h


end DifferentialGeometry.PDE.RicciFlow
