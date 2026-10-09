import DifferentialGeometry.Geometry.Collapse.LocalGradientLipschitz
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import DifferentialGeometry.Geometry.Collapse.AnnularDirections
set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison
open ContinuousLinearMap

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The actual gradient lift of the coordinate covectors. -/
def edgeCoordinateGradientLift (g : SmoothRiemannianMetric I M)
    (χ : M → EuclideanSpace ℝ (Fin 2)) (y : M) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I y :=
  ∑ j : Fin 2, (PiLp.proj 2 (fun _j : Fin 2 => ℝ) j).smulRight
    (gradFun g (fun z => χ z j) y)

/-- Gradient Gram operator; its entries are g(grad χ_i, grad χ_j). -/
def edgeCoordinateGradientGram (g : SmoothRiemannianMetric I M)
    (χ : M → EuclideanSpace ℝ (Fin 2)) (y : M) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (mvfderiv I χ y).comp (edgeCoordinateGradientLift g χ y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem edgeCoordinate_deriv (χ : M → EuclideanSpace ℝ (Fin 2)) {y : M}
    (hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y)
    (w : TangentSpace I y) (j : Fin 2) :
    mvfderiv I (fun z => χ z j) y w = mvfderiv I χ y w j := by
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _j : Fin 2 => ℝ) j
  have h := _root_.mvfderiv_comp_apply y p.differentiableAt.mdifferentiableAt hχ w
  rw [mvfderiv_eq_fderiv, p.fderiv] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem edgeCoordinateGradientLift_pairing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (χ : M → EuclideanSpace ℝ (Fin 2)) {y : M}
    (hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y)
    (a : EuclideanSpace ℝ (Fin 2)) (w : TangentSpace I y) :
    inner ℝ (edgeCoordinateGradientLift g χ y a) w = inner ℝ a (mvfderiv I χ y w) := by
  simp only [edgeCoordinateGradientLift, sum_apply, smulRight_apply]
  rw [sum_inner]
  simp only [hEnorm.inner_eq, map_smul, smul_apply, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [PiLp.proj_apply, star_trivial, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  have hg := inner_gradientFun g (fun z => χ z j) y w
  change g.inner y (gradFun g (fun z => χ z j) y) w = _ at hg
  rw [hg, edgeCoordinate_deriv χ hχ]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The gradient Gram is the native differential Gram, with no adjoint in its public input. -/
theorem edgeCoordinateGradientGram_entry (g : SmoothRiemannianMetric I M)
    (χ : M → EuclideanSpace ℝ (Fin 2)) {y : M}
    (hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) χ y) (i j : Fin 2) :
    edgeCoordinateGradientGram g χ y (PiLp.single 2 j 1) i =
      g.inner y (gradFun g (fun z => χ z i) y) (gradFun g (fun z => χ z j) y) := by
  have he : edgeCoordinateGradientLift g χ y (PiLp.single 2 j 1) =
      gradFun g (fun z => χ z j) y := by
    fin_cases j <;> simp [edgeCoordinateGradientLift]
  simp only [edgeCoordinateGradientGram, comp_apply, he]
  rw [← edgeCoordinate_deriv χ hχ]
  exact (inner_gradientFun g (fun z => χ z i) y _).symm

theorem rankTwo_adapted_of_buffered_perturbation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {x : M} {χ J Φ : M → EuclideanSpace ℝ (Fin 2)} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100)
    (hχ : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ χ (ball x 300))
    (hJ : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x 300))
    (hχx : χ x = 0)
    (hχL : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100,
      dist (χ y) (χ z) ≤ (1 + γ / 4) * dist y z)
    (hχI : ∀ y ∈ ball x 100, infDist (χ y) (ball 0 100) ≤ 100 * (γ / 4))
    (hχI' : ∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
      infDist w (χ '' ball x 100) ≤ 100 * (γ / 4))
    (hχtest : ∀ y ∈ ball x 100, ∀ z ∈ ball x (400 / γ), 100 < dist y z →
      ∀ w ∈ minimizingDirectionsTo g hEnorm {z} y,
        ‖mvfderiv I χ y w - (dist y z)⁻¹ • (Φ z - Φ y)‖ < γ / 4)
    (hgram : ∀ y ∈ ball x 300, ‖edgeCoordinateGradientGram g χ y - 1‖ < γ / 4)
    (hDJ : ∀ y ∈ ball x 300, ∀ w : TangentSpace I y,
      ‖mvfderiv I J y w - mvfderiv I χ y w‖ ≤ γ / 100 * Real.sqrt (g.inner y w w)) :
    (∀ y ∈ ball x 100, Function.Surjective (mvfderiv I J y)) ∧
      (∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (J y) (J z) ≤ (1 + γ) * dist y z) ∧
      (∀ y ∈ ball x 100, infDist (J y) (ball (J x) 100) ≤ 100 * γ) ∧
      (∀ w ∈ ball (J x) 100, infDist w (J '' ball x 100) ≤ 100 * γ) ∧
      (∀ y ∈ ball x 100, ∀ z ∈ ball x (100 / γ), 100 < dist y z →
        ∀ w ∈ minimizingDirectionsTo g hEnorm {z} y,
          ‖mvfderiv I J y w - (dist y z)⁻¹ • (Φ z - Φ y)‖ < γ)
 := by
  have hder (y : M) (hy : y ∈ ball x 300) :
      ‖mvfderiv I J y - mvfderiv I χ y‖ ≤ γ / 100 := by
    refine opNorm_le_bound _ (by positivity) fun w => ?_
    simpa only [sub_apply, norm_tangent_eq_sqrt_gInner hEnorm] using hDJ y hy w
  have hd (y : M) (hy : y ∈ ball x 300) :
      MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun z => J z - χ z) y :=
    ((hJ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp)).sub
      ((hχ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
  have hc (y : M) (hy : y ∈ ball x 300) :
      mvfderiv I (fun z => J z - χ z) y = mvfderiv I J y - mvfderiv I χ y :=
    _root_.mvfderiv_sub
      ((hJ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
      ((hχ.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
  have hscalar (a : EuclideanSpace ℝ (Fin 2)) (y : M) (hy : y ∈ ball x 300)
      (w : TangentSpace I y) :
      mvfderiv I (fun z => inner ℝ a (J z - χ z)) y w =
        inner ℝ a ((mvfderiv I J y - mvfderiv I χ y) w) := by
    let L := innerSL ℝ a
    have hh := _root_.mvfderiv_comp_apply y L.differentiableAt.mdifferentiableAt (hd y hy) w
    have heq : L ∘ (fun z => J z - χ z) = (fun z => inner ℝ a (J z - χ z)) := by
      funext z
      exact innerSL_apply_apply ℝ a (J z - χ z)
    rw [heq, mvfderiv_eq_fderiv, L.fderiv] at hh
    have hh' : mvfderiv I (fun z => inner ℝ a (J z - χ z)) y w =
        inner ℝ a (mvfderiv I (fun z => J z - χ z) y w) := by
      simpa only [mvfderiv, comp_apply, L, innerSL_apply_apply] using hh
    rw [hc y hy] at hh'
    exact hh'
  have hD : ∀ a : EuclideanSpace ℝ (Fin 2), ‖a‖ = 1 → ∀ y ∈ ball x 300,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => inner ℝ a (J z - χ z)) y := by
    intro a _ha y hy
    exact (innerSL ℝ a).differentiableAt.mdifferentiableAt.comp y (hd y hy)
  have hgrad : ∀ a : EuclideanSpace ℝ (Fin 2), ‖a‖ = 1 → ∀ y ∈ ball x 300,
      Real.sqrt (g.inner y (gradFun g (fun z => inner ℝ a (J z - χ z)) y)
        (gradFun g (fun z => inner ℝ a (J z - χ z)) y)) ≤ γ / 100 := by
    intro a ha y hy
    let V := gradFun g (fun z => inner ℝ a (J z - χ z)) y
    have hh := abs_real_inner_le_norm a ((mvfderiv I J y - mvfderiv I χ y) V)
    rw [ha, one_mul, ← hscalar a y hy, ← inner_gradientFun] at hh
    change |g.inner y V V| ≤ ‖(mvfderiv I J y - mvfderiv I χ y) V‖ at hh
    rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
    have hb : ‖(mvfderiv I J y - mvfderiv I χ y) V‖ ≤ γ / 100 * ‖V‖ :=
      (le_opNorm _ V).trans (mul_le_mul_of_nonneg_right (hder y hy) (norm_nonneg V))
    have hn := norm_nonneg V
    have hg : ‖V‖ ≤ γ / 100 := by nlinarith
    simpa only [← norm_tangent_eq_sqrt_gInner hEnorm] using hg
  have hmetric := vector_adapted_metric_clauses_riemannian g hEnorm hχx hχL hχI hχI' hD hgrad
  refine ⟨?_, hmetric.1, hmetric.2.1, hmetric.2.2, ?_⟩
  · intro y hy
    have hy300 : y ∈ ball x 300 := ball_subset_ball (by norm_num) hy
    let : InnerProductSpace ℝ (TangentSpace I y) :=
      Bundle.instInnerProductSpaceReal (E := fun z : M => TangentSpace I z) y
    let : CompleteSpace (TangentSpace I y) := FiniteDimensional.complete ℝ _
    have hχy := (hχ.contMDiffAt (isOpen_ball.mem_nhds hy300)).mdifferentiableAt (by simp)
    have hlift : edgeCoordinateGradientLift g χ y = adjoint (mvfderiv I χ y) := by
      apply (eq_adjoint_iff _ _).mpr
      exact edgeCoordinateGradientLift_pairing g hEnorm χ hχy
    have hg : ‖(mvfderiv I χ y).comp (adjoint (mvfderiv I χ y)) - 1‖ < γ / 4 := by
      rw [← hlift]
      exact hgram y hy300
    let γ' := (γ + 1 / 100) / 2
    have hgg : γ < γ' := by dsimp [γ']; linarith
    apply surjective_of_gram_perturbation (γ := γ') (by dsimp [γ']; linarith)
    · exact hg.trans (by linarith)
    · exact (hder y hy300).trans_lt (by linarith)
  · intro y hy z hz hlen w hw
    have hz' : z ∈ ball x (400 / γ) :=
      ball_subset_ball (div_le_div_of_nonneg_right (by norm_num) hγ.le) hz
    have hdw := hDJ y (ball_subset_ball (by norm_num) hy) w
    rw [hw.1, Real.sqrt_one, mul_one] at hdw
    exact norm_sub_lt_of_derivative_perturbation hγ hdw (hχtest y hy z hz' hlen w hw)

end DifferentialGeometry.Geometry.Collapse
