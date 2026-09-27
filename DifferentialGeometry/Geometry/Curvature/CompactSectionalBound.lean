import DifferentialGeometry.Geometry.Curvature.SectionalContraction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Uniform.OperatorNorm



noncomputable section

open Set Bundle Manifold DifferentialGeometry
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]




theorem exists_uniform_abs_sectionalCurvature_bound_orthogonal
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : M) (v w : TangentSpace I p), g.inner p v w = 0 →
      |sectionalCurvature g p v w| ≤ C := by
  by_cases hdim : Module.finrank ℝ E = 0
  · refine ⟨0, le_rfl, ?_⟩
    intro p v w _
    have hv : v = 0 := (finrank_zero_iff_forall_zero.mp hdim) v
    rw [hv, sectionalCurvature_zero_left, abs_zero]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    obtain ⟨K, hK, hbound⟩ := exists_uniform_riemannOp_LeviCivita_gNorm_bound g
    refine ⟨K + 1, by linarith, ?_⟩
    intro p v w horth
    let a := g.inner p v v
    let b := g.inner p w w
    let R := riemannOp (LeviCivita g) p v w w
    have ha : 0 ≤ a := (g.toRiemannianMetric.toCore p).re_inner_nonneg v
    have hb : 0 ≤ b := (g.toRiemannianMetric.toCore p).re_inner_nonneg w
    have hcs := sectionalCurvatureDenominator_nonneg g p v R
    rw [sectionalCurvatureDenominator_def] at hcs
    have hR : g.inner p R R ≤ K * a * b * b := hbound p v w w
    have hm := mul_le_mul_of_nonneg_left hR ha
    have hKsq : K ≤ (K + 1) ^ 2 := by nlinarith
    have hsqmul := mul_le_mul_of_nonneg_right hKsq (sq_nonneg (a * b))
    have hsq : (g.inner p v R) ^ 2 ≤ ((K + 1) * a * b) ^ 2 := by
      change 0 ≤ a * g.inner p R R - (g.inner p v R) ^ 2 at hcs
      nlinarith
    have hab : |g.inner p v R| ≤ (K + 1) * a * b :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by rwa [sq_abs])
    rw [sectionalCurvature_eq_riemann, horth, zero_pow (by norm_num), sub_zero, abs_div]
    change |g.inner p v R| / |a * b| ≤ K + 1
    rw [abs_of_nonneg (mul_nonneg ha hb)]
    by_cases hab0 : a * b = 0
    · rw [hab0, div_zero]
      linarith
    · apply (div_le_iff₀ (lt_of_le_of_ne (mul_nonneg ha hb) (Ne.symm hab0))).mpr
      nlinarith [hab]

end DifferentialGeometry.Geometry
