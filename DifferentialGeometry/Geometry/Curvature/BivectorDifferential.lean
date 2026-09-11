import DifferentialGeometry.Geometry.Curvature.ConformalOperator
import DifferentialGeometry.Geometry.Operator.GradientPerturbation
import DifferentialGeometry.Geometry.Operator.JetComparison
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff InnerProductSpace BigOperators
namespace DifferentialGeometry.Geometry.Curvature
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
def bivectorDifferentialAt (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) : E3 :=
  WithLp.toLp 2 ![mvfderiv I F x (B 2), -mvfderiv I F x (B 1), mvfderiv I F x (B 0)]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
theorem inner_bivectorDifferentialAt (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (c : E3) :
    ⟪bivectorDifferentialAt F x B, c⟫_ℝ = mvfderiv I F x (bivectorNormalAt x B c) := by
  simp only [bivectorDifferentialAt, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_trivial, bivectorNormalAt, map_add, map_sub, map_smul,
    smul_eq_mul]
  ring

omit [T2Space M] in
theorem norm_sq_bivectorDifferentialAt (g : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B) :
    ‖bivectorDifferentialAt F x B‖ ^ 2 = g.inner x (gradFun g F x) (gradFun g F x) := by
  have hBon : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := hB
  rw [inner_gradFun_self_eq_sum_sq g F x B hBon, EuclideanSpace.real_norm_sq_eq]
  simp only [bivectorDifferentialAt, Fin.sum_univ_three, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, neg_sq]
  ring

private theorem normalize_quadratic_bound (q : E3) (hq : q ≠ 0) (c : E3) :
    |⟪q, c⟫_ℝ ^ 2 - ⟪NormedSpace.normalize q, c⟫_ℝ ^ 2| ≤
      |‖q‖ ^ 2 - 1| * ‖c‖ ^ 2 := by
  have hv := NormedSpace.norm_normalize hq
  have he : ⟪q, c⟫_ℝ = ‖q‖ * ⟪NormedSpace.normalize q, c⟫_ℝ := by
    rw [← real_inner_smul_left, NormedSpace.norm_smul_normalize]
  have hcs := abs_real_inner_le_norm (NormedSpace.normalize q) c
  rw [hv, one_mul] at hcs
  have hsq : ⟪NormedSpace.normalize q, c⟫_ℝ ^ 2 ≤ ‖c‖ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hcs
  calc
    _ = |(‖q‖ ^ 2 - 1) * ⟪NormedSpace.normalize q, c⟫_ℝ ^ 2| := by rw [he]; congr 1; ring
    _ = |‖q‖ ^ 2 - 1| * ⟪NormedSpace.normalize q, c⟫_ℝ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ⟪NormedSpace.normalize q, c⟫_ℝ)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

theorem normalize_bivectorDifferentialAt_spec
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt h x B)
    (hunit : g.inner x (gradFun g F x) (gradFun g F x) = 1)
    (ε : ℝ) (hε : ε ≤ 1 / 2) (hmetric : metricDerivNorm 0 h g g x ≤ ε) :
    ‖NormedSpace.normalize (bivectorDifferentialAt F x B)‖ = 1 ∧
      ∀ c : E3, |(mvfderiv I F x (bivectorNormalAt x B c)) ^ 2 -
        ⟪NormedSpace.normalize (bivectorDifferentialAt F x B), c⟫_ℝ ^ 2| ≤
          2 * ε * ‖c‖ ^ 2 := by
  let q := bivectorDifferentialAt F x B
  have hq : ‖q‖ ^ 2 = h.inner x (gradFun h F x) (gradFun h F x) :=
    norm_sq_bivectorDifferentialAt h F x B hB
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using hmetric.trans hε)
  have hl := inner_gradFun_le_of_metricUniformEquivalentOn h g
    (metricUniformEquivalentOn_symm heq) F (Set.mem_singleton x)
  rw [hunit, ← hq] at hl
  have hq0 : q ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hl
    linarith
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _ : 0 ≤ metricDerivNorm 0 h g g x).trans hmetric
  have hclose := abs_inner_gradFun_sub_le_of_metricDerivNorm g h F x ε (by linarith) hmetric
  rw [hunit, ← hq, mul_one] at hclose
  have hfrac : ε / (1 - ε) ≤ 2 * ε := by
    rw [div_le_iff₀ (show 0 < 1 - ε by linarith)]
    nlinarith [mul_nonneg hε0 (show 0 ≤ 1 / 2 - ε by linarith)]
  have hc : |‖q‖ ^ 2 - 1| ≤ 2 * ε := hclose.trans hfrac
  refine ⟨NormedSpace.norm_normalize hq0, ?_⟩
  intro c
  rw [← inner_bivectorDifferentialAt]
  exact (normalize_quadratic_bound q hq0 c).trans
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

theorem exists_unit_bivectorDifferential_approx_of_metricDerivNorm
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt h x B)
    (hunit : g.inner x (gradFun g F x) (gradFun g F x) = 1)
    (ε : ℝ) (hε : ε ≤ 1 / 2) (hmetric : metricDerivNorm 0 h g g x ≤ ε) :
    ∃ v : E3, ‖v‖ = 1 ∧ ∀ c : E3,
      |(mvfderiv I F x (bivectorNormalAt x B c)) ^ 2 - ⟪v, c⟫_ℝ ^ 2| ≤ 2 * ε * ‖c‖ ^ 2 :=
  ⟨NormedSpace.normalize (bivectorDifferentialAt F x B),
    normalize_bivectorDifferentialAt_spec g h F x B hB hunit ε hε hmetric⟩

end DifferentialGeometry.Geometry.Curvature
