import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowEquivalence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Bundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section FixedManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metric_uniform_equivalent_on_closed_interval_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b t₀ A : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (ht₀ : t₀ ∈ Icc a b)
    {K : Set M} (hA : 0 ≤ A)
    (hquad : ∀ t ∈ Icc a b, ∀ x ∈ K, ∀ v : TangentSpace I x,
      |S.ricciAt t x (vec2 v v)| ≤ A * (S.base.metric t).inner x v v) :
    MetricUniformEquivalentOnWindow K a b (S.base.metric t₀)
      (fun _ t => S.base.metric t) (fun t => metricEquivalenceFactor 1 A t t₀) := by
  intro _ t ht
  have hfactor : 1 ≤ metricEquivalenceFactor 1 A t t₀ := by
    simp only [metricEquivalenceFactor, one_mul]
    exact Real.one_le_exp (by positivity)
  refine ⟨hfactor, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp
  let f : ℝ → ℝ := fun s => (S.base.metric s).inner x v v
  let f' : ℝ → ℝ := fun s => -2 * S.ricciAt s x (vec2 v v)
  have hpos (s : ℝ) : 0 < f s := (S.base.metric s).pos x v hv
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun r => Real.log (f r)) (f' s / f s) (Icc a b) s :=
    (metric_inner_hasDerivWithinAt_on_closed_interval S hS hab hcarrier hregular hs x v v).log
      (hpos s).ne'
  have hbound (s : ℝ) (hs : s ∈ Icc a b) : ‖f' s / f s‖ ≤ 2 * A := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos s)]
    dsimp only [f']
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact (div_le_iff₀ (hpos s)).mpr (by
      have h := mul_le_mul_of_nonneg_left (hquad s hs x hx v) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [f, mul_assoc] using h)
  have hlog := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound ht₀ ht
  have hlog' : |Real.log (f t) - Real.log (f t₀)| ≤ 2 * A * |t - t₀| := by
    simpa only [Real.norm_eq_abs] using hlog
  have hexp := exp_bounds_of_abs_log_sub_le (hpos t₀) (hpos t) hlog'
  simpa only [metricEquivalenceFactor, one_mul, Real.exp_neg, f] using hexp

end FixedManifold

theorem FlowCurvatureBoundedOnCompactWindows.metric_equiv_on_closed_interval
    (X : PointedFlowSeq (I := I)) (hcurv : FlowCurvatureBoundedOnCompactWindows X)
    {a b t₀ : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ X.D.carrier)
    (hregular : Ioo a b ⊆ X.D.regular) (ht₀ : t₀ ∈ Icc a b) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      letI : ChartedSpace H (X.term k).M := (X.term k).charted
      letI : T2Space (X.term k).M := (X.term k).t2
      letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
      letI : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
      MetricUniformEquivalentOnWindow univ a b ((X.term k).S.family.metric t₀)
        (fun _ t => (X.term k).S.family.metric t) (fun _ => B) := by
  obtain ⟨C, _, hC⟩ := hcurv.bound_on_window a b hcarrier
  let A : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let B : ℝ := Real.exp (2 * A * (b - a))
  have hB : 1 ≤ B := Real.one_le_exp
    (mul_nonneg (mul_nonneg (by norm_num) hA) (sub_nonneg.mpr hab.le))
  refine ⟨B, hB, fun k => ?_⟩
  let : TopologicalSpace (X.term k).M := (X.term k).topology
  let : ChartedSpace H (X.term k).M := (X.term k).charted
  let : T2Space (X.term k).M := (X.term k).t2
  let : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  let : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
  have hquad := twoTensorQuadBound_of_solutions (fun _ => (X.term k).S)
    univ a b C (fun _ t ht x _ => hC k t ht x)
  have hEq := metric_uniform_equivalent_on_closed_interval_of_solution
    (X.term k).S (X.term k).isSolution hab hcarrier hregular ht₀ hA
    (fun t ht x hx v => hquad.2 0 t ht x hx v)
  intro i t ht
  apply metricUniformEquivalentOn_of_le (hEq i t ht)
  simp only [metricEquivalenceFactor, one_mul]
  apply Real.exp_le_exp.mpr
  have hdist : |t - t₀| ≤ b - a := abs_le.mpr ⟨by linarith [ht.1, ht₀.2],
    by linarith [ht.2, ht₀.1]⟩
  exact mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hA)

end DifferentialGeometry.CheegerGromovCompactness
