import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Comparison.LocalDistanceComparison
import DifferentialGeometry.Geometry.Metric.Distance.Ball

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian (riemannianEDistOf_le_of_metric_lower_on_ball)

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem curvDerivNorm_le_on_terminal_ball_of_curvature_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {T r K : ℝ} (hT : 0 < T) (hr : 0 < r) (hK : 0 < K)
    (hcarrier : Icc (-T) 0 ⊆ D.carrier) (hregular : Ioo (-T) 0 ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric (-(T / 2))))
    (p : M)
    (hcurv : ∀ t ∈ Icc (-T) 0, ∀ y ∈ riemannianClosedBallOf (S.base.metric 0) p r,
      curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2)
    (m : ℕ) (t : ℝ) (ht : t ∈ Icc (-(T / 4)) 0)
    (x : M) (hx : x ∈ riemannianClosedBallOf (S.base.metric 0) p (r / 2)) :
    curvDerivNorm (I := I) m (S.base.metric t) x ≤
      shiLocalUniformBound (Module.finrank ℝ E) m (K * (T / 2))
        (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 * K * T / 2)) * (r / 4) *
          Real.sqrt K) * K / Real.sqrt (T / 4) ^ m := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : BoundarylessManifold I M := inferInstance
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let beta : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) ^ 2 * K * T / 2))
  let rho : ℝ := beta * (r / 4)
  let R : ℝ := rho * Real.sqrt K
  have hbeta : 0 < beta := Real.exp_pos _
  have hrho : 0 < rho := mul_pos hbeta (by positivity)
  have hR : 0 < R := mul_pos hrho (Real.sqrt_pos.mpr hK)
  have hRdiv : R / Real.sqrt K = rho := by
    dsimp only [R]
    exact mul_div_cancel_right₀ rho (Real.sqrt_pos.mpr hK).ne'
  have ha : -(T / 2) ∈ Icc (-T) 0 := ⟨by linarith, by linarith⟩
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
  have hsub : Icc (-(T / 2)) 0 ⊆ Icc (-T) 0 :=
    fun _ hs => ⟨by linarith [hs.1], hs.2⟩
  have hsubreg : Ico (-(T / 2)) 0 ⊆ D.regular := by
    intro s hs
    exact hregular ⟨by linarith [hs.1], hs.2⟩
  have hballx : ∀ y : M,
      riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (r / 2) →
        y ∈ riemannianClosedBallOf (S.base.metric 0) p r := by
    intro y hy
    have hadd : ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) =
        ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ r / 2) (by positivity : 0 ≤ r / 2)]
      congr 1
      ring
    exact (riemannianEDistOf_triangle (S.base.metric 0) p x y).trans
      ((add_le_add hx hy).trans_eq hadd)
  have hmetric : ∀ y : M,
      riemannianEDistOf (S.base.metric 0) x y ≤ ENNReal.ofReal (r / 2) →
      ∀ v : TangentSpace I y,
        beta ^ 2 * (S.base.metric 0).inner y v v ≤
          (S.base.metric (-(T / 2))).inner y v v := by
    intro y hy v
    have hbound : ∀ s ∈ Icc (-T) 0,
        Tensor0SBundle.normSq0S (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K ^ 2 := by
      intro s hs
      exact hcurv s hs y (hballx y hy)
    have h := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular y
      hbound ha hzero v).1
    have habs : |-(T / 2) - (0 : ℝ)| = T / 2 := by
      rw [sub_zero, abs_neg, abs_of_pos (by positivity : 0 < T / 2)]
    have hbetasq : beta ^ 2 =
        Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 2 * K * (T / 2))) := by
      dsimp only [beta]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Real.sqrt_sq hK.le, habs, ← hbetasq] at h
    exact h
  have hcapture : ∀ y : M,
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤ ENNReal.ofReal rho →
        y ∈ riemannianClosedBallOf (S.base.metric 0) p r := by
    intro y hy
    have hsmall : rho < beta * (r / 2) := by dsimp only [rho]; nlinarith
    have hdist : riemannianEDistOf (S.base.metric (-(T / 2))) x y <
        ENNReal.ofReal (beta * (r / 2)) :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hsmall)
    have hle := riemannianEDistOf_le_of_metric_lower_on_ball
      (S.base.metric 0) (S.base.metric (-(T / 2))) x y hbeta hmetric hdist
    have hreal : (riemannianEDistOf (S.base.metric (-(T / 2))) x y).toReal ≤ rho :=
      (ENNReal.toReal_le_of_le_ofReal hrho.le hy)
    apply hballx y
    apply hle.trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hbeta).2
    exact hreal.trans (by dsimp only [rho]; nlinarith)
  have hball : IsCompact {y : M |
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    rw [hRdiv]
    exact hcomplete.closedEBall_isCompact x rho
  have hcurv' : ∀ s ∈ Icc (-(T / 2)) 0, ∀ y : M,
      riemannianEDistOf (S.base.metric (-(T / 2))) x y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
      curvDerivNormSq (I := I) 0 (S.base.metric s) y ≤ K ^ 2 := by
    intro s hs y hy
    rw [hRdiv] at hy
    exact hcurv s (hsub hs) y (hcapture y hy)
  have hcenter : riemannianEDistOf (S.base.metric (-(T / 2))) x x ≤
      ENNReal.ofReal (R / (2 * Real.sqrt K)) := by
    rw [riemannianEDistOf_self]
    exact bot_le
  have hshi := Perelman.KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets
    S hS hdim (a := -(T / 2)) (b := 0) (by linarith) hK hR
    (hsub.trans hcarrier) hsubreg x hball hcurv' m t
    ⟨by linarith [ht.1], ht.2⟩ x hcenter
  have hden : Real.sqrt (T / 4) ^ m ≤ Real.sqrt (t - -(T / 2)) ^ m :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith [ht.1])) m
  have hbound := hshi.trans (div_le_div_of_nonneg_left
    (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
    (pow_pos (Real.sqrt_pos.mpr (by positivity : 0 < T / 4)) m) hden)
  simpa only [sub_neg_eq_add, zero_add, R, rho, beta] using hbound

end DifferentialGeometry.PDE.RicciFlow
