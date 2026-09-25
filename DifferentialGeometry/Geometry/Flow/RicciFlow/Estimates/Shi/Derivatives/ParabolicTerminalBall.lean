import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem shi_curvDerivNorm_parabolicClosedWindow_on_terminal_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T Q θ K r : ℝ} (hQ : 0 < Q) (hθ : 0 < θ)
    (hK : 0 < K) (hr : 0 < r)
    (hcarrier : Icc (T - θ / Q) T ⊆ D.carrier)
    (hregular : Ioo (T - θ / Q) T ⊆ D.regular)
    (p : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric T) p
      (r / Real.sqrt Q)))
    (hcurv : ∀ t ∈ Icc (T - θ / Q) T,
      ∀ x ∈ riemannianClosedBallOf (S.base.metric T) p (r / Real.sqrt Q),
        curvDerivNormSq 0 (S.base.metric t) x ≤ (K * Q) ^ 2) :
    let S₀ := S.parabolicClosedWindow T Q θ hQ hθ.le
    IsSolutionOn S₀ ∧
      IsCompact (riemannianClosedBallOf (S₀.base.metric 0) p r) ∧
      (∀ s ∈ Icc (-θ) 0, ∀ x ∈ riemannianClosedBallOf (S₀.base.metric 0) p r,
        curvDerivNormSq 0 (S₀.base.metric s) x ≤ K ^ 2) ∧
      ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0,
        ∀ x ∈ riemannianClosedBallOf (S₀.base.metric 0) p (r / 4),
          curvDerivNorm m (S₀.base.metric s) x ≤
            shiLocalUniformBound (Module.finrank ℝ E) m (K * (θ / 4))
              ((r / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * θ))) *
                Real.sqrt K /
                  (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (θ / 4)))) *
                K / Real.sqrt (θ / 4) ^ m := by
  let S₀ := S.parabolicClosedWindow T Q θ hQ hθ.le
  have hsol : IsSolutionOn S₀ := isSolutionOn_parabolicClosedWindow S hS hQ hθ.le
    hcarrier hregular
  have hball : riemannianClosedBallOf (S₀.base.metric 0) p r =
      riemannianClosedBallOf (S.base.metric T) p (r / Real.sqrt Q) := by
    change riemannianClosedBallOf
      ((S.parabolicClosedWindow T Q θ hQ hθ.le).base.metric 0) p r = _
    rw [SolutionOn.parabolicClosedWindow_metric_zero]
    have hh := riemannianClosedBallOf_scaleMetric Q hQ (S.base.metric T) p (r / Real.sqrt Q)
    have heq : Real.sqrt Q * (r / Real.sqrt Q) = r := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hQ)]
    rwa [heq] at hh
  have hcpt : IsCompact (riemannianClosedBallOf (S₀.base.metric 0) p r) :=
    hball.symm ▸ hcompact
  have hbound : ∀ s ∈ Icc (-θ) 0,
      ∀ x ∈ riemannianClosedBallOf (S₀.base.metric 0) p r,
        curvDerivNormSq 0 (S₀.base.metric s) x ≤ K ^ 2 := by
    intro s hs x hx
    have ht : T + s / Q ∈ Icc (T - θ / Q) T := by
      have hlo := div_le_div_of_nonneg_right hs.1 hQ.le
      have hhi := div_le_div_of_nonneg_right hs.2 hQ.le
      simp only [neg_div, zero_div] at hlo hhi
      constructor <;> linarith
    have hh := hcurv (T + s / Q) ht x (hball ▸ hx)
    change curvDerivNormSq 0 (scaleMetric Q hQ (S.base.metric (T + s / Q))) x ≤ _
    rw [curvDerivNormSq_scaleMetric]
    calc Q⁻¹ ^ (0 + 2) * curvDerivNormSq 0 (S.base.metric (T + s / Q)) x
        ≤ Q⁻¹ ^ (0 + 2) * (K * Q) ^ 2 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = K ^ 2 := by
        norm_num only [Nat.zero_add]
        field_simp [hQ.ne']
  refine ⟨hsol, hcpt, hbound, ?_⟩
  have hh := shi_curvDerivNorm_on_terminal_ball S₀ hsol (neg_lt_zero.mpr hθ) hK hr
    Subset.rfl Subset.rfl p hcpt hbound
  simpa only [zero_sub, neg_neg, neg_add_rev, zero_add, add_zero, neg_div] using hh

end DifferentialGeometry.PDE.RicciFlow
