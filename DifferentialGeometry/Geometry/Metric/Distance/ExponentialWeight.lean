import DifferentialGeometry.Geometry.Metric.Distance.Approximation
import DifferentialGeometry.Geometry.Operator.Gradient.Composition

noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_positive_smooth_exp_distance_weight
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {a : ℝ} (ha : 0 ≤ a) :
    ∃ η : C^∞⟮I, M; ℝ⟯,
      (∀ x, 0 < η x) ∧
      (∀ x, Real.exp (-a * ((riemannianEDistOf g p x).toReal + 1)) ≤ η x ∧
        η x ≤ Real.exp (-a * ((riemannianEDistOf g p x).toReal - 1))) ∧
      (∀ x, Tensor0SBundle.normSq0S g x 1
        (Geometry.Operator.differential1FormFun η x) ≤ 9 * a ^ 2 * (η x) ^ 2) := by
  obtain ⟨ρ, hρapprox, hderiv, hgrad⟩ := exists_contMDiff_riemannianDistance_approx g p
    (ε := 1) (by norm_num)
  have hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ρ : M → ℝ) := ρ.contMDiff
  have hnorm (f : M → ℝ) (x : M) : Tensor0SBundle.normSq0S g x 1
      (Geometry.Operator.differential1FormFun f x) =
      g.inner x (Geometry.Operator.gradFun g f x) (Geometry.Operator.gradFun g f x) := by
    have hsharp : cotangentSharp (I := I) g x
        (Geometry.Operator.differential1FormFun f x) = Geometry.Operator.gradFun g f x := by
      apply tangentFlatLinear_injective g x
      ext v
      change g.inner x (cotangentSharp g x (Geometry.Operator.differential1FormFun f x)) v =
        g.inner x (Geometry.Operator.gradFun g f x) v
      rw [cotangentSharp_inner, cotangentToDual_apply]
      exact Geometry.Operator.differential1FormFun_apply_eq_inner_gradientFun g f x v
    rw [Tensor0SBundle.normSq0S_eq_inner, Tensor0SBundle.inner0S_one_eq_cotangent,
      Tensor0SBundle.cotangentInner_eq_sharp, hsharp]
  let η : M → ℝ := fun x => Real.exp (-a * ρ x)
  have hη : ContMDiff I 𝓘(ℝ, ℝ) ∞ η := by
    exact Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hρ)
  have hρsq (x : M) : Tensor0SBundle.normSq0S g x 1
      (Geometry.Operator.differential1FormFun ρ x) ≤ 9 := by
    have hpos := DifferentialGeometry.metric_inner_self_nonneg g x
      (Geometry.Operator.gradFun g ρ x)
    rw [hnorm]
    nlinarith [hgrad x, Real.sq_sqrt hpos, Real.sqrt_nonneg (g.inner x (Geometry.Operator.gradFun g ρ x) (Geometry.Operator.gradFun g ρ x))]
  have hηbound (x : M) : Tensor0SBundle.normSq0S g x 1
      (Geometry.Operator.differential1FormFun η x) ≤ 9 * a ^ 2 * (η x) ^ 2 := by
    simpa only [η, mul_comm, mul_left_comm] using
      Geometry.Operator.normSq0S_differential1FormFun_exp_neg_le g
      (u := ρ) (a := a) (L := 9) (x := x)
      (hρ.mdifferentiable (by simp) x) (hρsq x)
  refine ⟨⟨η, hη⟩, ?_, ?_, ?_⟩
  · intro x; exact Real.exp_pos _
  · intro x
    have h := abs_le.mp (hρapprox x)
    constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith
  · intro x; exact hηbound x

end DifferentialGeometry.Geometry.Metric
