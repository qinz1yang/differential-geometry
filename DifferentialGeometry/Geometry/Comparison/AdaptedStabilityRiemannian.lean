import DifferentialGeometry.Geometry.Collapse.RadialAdaptedCoordinates

/-!
# Ambient Lipschitz differences preserve actual adapted coordinates

The derivative bound is obtained along a true unit geodesic in the open ball.
All three clauses are then transferred for the same supplied comparison coordinate.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem abs_mvfderiv_le_of_lipschitzOn (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    {x : M} (hx : x ∈ U) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    {h : ℝ} (hlip : ∀ y ∈ U, ∀ z ∈ U, |f y - f z| ≤ h * dist y z)
    (w : TangentSpace I x) (hw : g.inner x w w = 1) : |mvfderiv (I := I) f x w| ≤ h := by
  let c := intrinsicGeodesic g hEnorm x w
  have hc0 : c 0 = x := intrinsicGeodesic_zero g hEnorm x w
  have hc := intrinsicGeodesic_contMDiff g hEnorm x w
  have hcU : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U := by
    have ht := hc.continuous.tendsto 0
    change Tendsto c (𝓝 0) (𝓝 (c 0)) at ht
    rw [hc0] at ht
    exact ht.eventually (hU.mem_nhds hx)
  have hvel : mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) = w :=
    intrinsicGeodesic_mfderiv_zero g hEnorm x w
  by_cases hh : 0 ≤ h
  · have hd := hasDerivAt_comp_mfderiv_along I f c 0
      (by simpa only [hc0] using hf) (hc.contMDiffAt.mdifferentiableAt (by simp))
    change HasDerivAt (fun t => f (c t))
      (mvfderiv (I := I) f (c 0) (mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ))) 0 at hd
    rw [hvel, hc0] at hd
    have he := hd.le_of_lip' hh (show ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖f (c t) - f (c 0)‖ ≤ h * ‖t - 0‖ from by
      filter_upwards [hcU] with t ht
      have hdist := (lipschitzWith_one_intrinsicGeodesic g hEnorm x w hw).dist_le_mul t 0
      change dist (c t) (c 0) ≤ ((1 : NNReal) : ℝ) * dist t 0 at hdist
      simp only [NNReal.coe_one, one_mul, hc0] at hdist
      rw [hc0, Real.norm_eq_abs]
      exact (hlip (c t) ht x hx).trans (mul_le_mul_of_nonneg_left
        (by simpa only [Real.dist_eq, Real.norm_eq_abs] using hdist) hh))
    simpa only [Real.norm_eq_abs] using he
  · have heq : c =ᶠ[𝓝 (0 : ℝ)] fun _t => x := by
      filter_upwards [hcU] with t ht
      have hb := (abs_nonneg _).trans (hlip (c t) ht x hx)
      have hz : dist (c t) x = 0 := by
        nlinarith [dist_nonneg (x := c t) (y := x)]
      exact dist_eq_zero.mp hz
    have hd0 : mfderiv 𝓘(ℝ, ℝ) I c 0 = 0 := by
      rw [heq.mfderiv_eq]
      simp only [mfderiv_const, ContinuousLinearMap.comp_zero]
    have hw0 : w = 0 := by rw [← hvel, hd0]; rfl
    simp only [hw0, map_zero] at hw
    norm_num at hw

theorem adapted_of_lipschitz_perturbation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (q : M) {φ ψ Φ : M → ℝ} {γ h ζ : ℝ}
    (hγ : 0 < γ) (hh : 0 ≤ h) (hζ : γ + h ≤ ζ)
    (hφs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ (Metric.ball q 1))
    (hψs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (Metric.ball q 1))
    (hφq : φ q = 0) (hψq : ψ q = 0)
    (hφlip : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |φ x - φ y| ≤ (1 + γ) * dist x y)
    (hφ1 : ∀ x ∈ Metric.ball q 1, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ)
    (hφ2 : ∀ t ∈ Ioo (-1 : ℝ) 1, Metric.infDist t (φ '' Metric.ball q 1) ≤ γ)
    (hφtest : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q γ⁻¹, 1 < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) φ x w - (Φ y - Φ x) / dist x y| < γ)
    (hdiff : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |(ψ x - φ x) - (ψ y - φ y)| ≤ h * dist x y) :
    (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
    (∀ x ∈ Metric.ball q 1, Metric.infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
    (∀ t ∈ Ioo (-1 : ℝ) 1, Metric.infDist t (ψ '' Metric.ball q 1) ≤ ζ) ∧
    ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q ζ⁻¹, 1 < dist x y →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x y) = y →
      |mvfderiv (I := I) ψ x w - (Φ y - Φ x) / dist x y| < ζ := by
  have hval : ∀ x ∈ Metric.ball q 1, |ψ x - φ x| ≤ h := by
    intro x hx
    have he := hdiff x hx q (Metric.mem_ball_self (by norm_num))
    rw [hψq, hφq, sub_self, sub_zero] at he
    exact he.trans (by nlinarith [show dist x q < 1 from Metric.mem_ball.mp hx])
  obtain ⟨h1, h2⟩ := image_clauses_of_perturbation hζ hh hval hφ1 hφ2
  refine ⟨lipschitz_clause_of_perturbation hζ hφlip hdiff, h1, h2, ?_⟩
  intro x hx y hy hxy w hw hend
  have hxnhds := Metric.isOpen_ball.mem_nhds hx
  have hφd := (hφs.contMDiffAt hxnhds).mdifferentiableAt (by simp)
  have hψd := (hψs.contMDiffAt hxnhds).mdifferentiableAt (by simp)
  have hder := abs_mvfderiv_le_of_lipschitzOn g hEnorm Metric.isOpen_ball hx
    (hψd.sub hφd) hdiff w hw
  have hder' : |mvfderiv (I := I) ψ x w - mvfderiv (I := I) φ x w| ≤ h := by
    simpa only [_root_.mvfderiv_sub hψd hφd, sub_apply] using hder
  exact derivative_clause_of_perturbation hζ
    (hφtest x hx y (ball_inv_subset_of_le q hγ (by linarith) hy) hxy w hw hend) hder'

end DifferentialGeometry.Geometry.Comparison
