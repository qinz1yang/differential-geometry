import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Module
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff BigOperators

private theorem exists_wedge_coordinates (z : Fin 3 → ℝ) :
    ∃ a b : Fin 3 → ℝ, ∀ i : Fin 3,
      a (bivectorIndex3 i).1 * b (bivectorIndex3 i).2 -
        a (bivectorIndex3 i).2 * b (bivectorIndex3 i).1 = z i := by
  by_cases h₀ : z 0 = 0
  · by_cases h₁ : z 1 = 0
    · refine ⟨![0, 1, 0], ![0, 0, z 2], ?_⟩
      intro i
      fin_cases i <;> simp [bivectorIndex3, h₀, h₁]
    · refine ⟨![1, z 2 / z 1, 0], ![0, 0, z 1], ?_⟩
      intro i
      fin_cases i <;> simp [bivectorIndex3, h₀, h₁]
  · refine ⟨![1, 0, -(z 2 / z 0)], ![0, z 0, z 1], ?_⟩
    intro i
    fin_cases i <;> simp [bivectorIndex3, h₀]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance threePositivityC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance threePositivityC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance threePositivityC3 : IsManifold I 3 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] in
theorem three_bivector_quadratic_realized (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    {n : ℕ} (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    ∃ a b : TangentSpace I x,
      g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 =
        algebraicCurvatureIdentityQuadraticEval g c v w ∧
      tensor04StandardAt (I := I) (A : Tensor04At (I := I) (M := M) x) a b b a =
        algebraicCurvatureOperatorQuadraticEval A c v w := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  let z : Fin 3 → ℝ := fun i => ∑ k : Fin n, c k *
    (basis.repr (v k) (bivectorIndex3 i).1 * basis.repr (w k) (bivectorIndex3 i).2 -
      basis.repr (v k) (bivectorIndex3 i).2 * basis.repr (w k) (bivectorIndex3 i).1)
  obtain ⟨a₀, b₀, hab⟩ := exists_wedge_coordinates z
  let a : TangentSpace I x := basis.equivFun.symm a₀
  let b : TangentSpace I x := basis.equivFun.symm b₀
  have ha (i : Fin 3) : basis.repr a i = a₀ i :=
    congrFun (basis.equivFun.apply_symm_apply a₀) i
  have hb (i : Fin 3) : basis.repr b i = b₀ i :=
    congrFun (basis.equivFun.apply_symm_apply b₀) i
  have hcoord (i : Fin 3) :
      basis.repr a (bivectorIndex3 i).1 * basis.repr b (bivectorIndex3 i).2 -
        basis.repr a (bivectorIndex3 i).2 * basis.repr b (bivectorIndex3 i).1 = z i := by
    simpa only [ha, hb] using hab i
  have hnorm : algebraicCurvatureIdentityQuadraticEval g
      (fun _ : Fin 1 => 1) (fun _ => a) (fun _ => b) =
        algebraicCurvatureIdentityQuadraticEval g c v w := by
    rw [algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq g x
        (fun _ : Fin 1 => 1) (fun _ => a) (fun _ => b) basis horth,
      algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq g x c v w basis horth]
    simp only [Fin.sum_univ_one, one_mul, hcoord]
    rfl
  have hvalue : algebraicCurvatureOperatorQuadraticEval A
      (fun _ : Fin 1 => 1) (fun _ => a) (fun _ => b) =
        algebraicCurvatureOperatorQuadraticEval A c v w := by
    rw [algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad x basis A
        (fun _ : Fin 1 => 1) (fun _ => a) (fun _ => b),
      algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad x basis A c v w]
    simp only [Fin.sum_univ_one, one_mul, hcoord]
    rfl
  refine ⟨a, b, ?_, ?_⟩
  · simpa only [algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one,
      one_mul, g.symm x b a, ← pow_two, one_pow] using hnorm
  · simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul]
      using hvalue

variable [T2Space M]

def CurvatureOperatorPositiveAt (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
    0 < algebraicCurvatureIdentityQuadraticEval g c v w →
      0 < algebraicCurvatureOperatorQuadraticEval
        (metricAlgebraicCurvatureTensorAt g x) c v w

theorem curvatureOperatorPositiveAt_iff_sectional (g : SmoothRiemannianMetric I M)
    (x : M) (_hdim : Module.finrank ℝ E = 3) :
    CurvatureOperatorPositiveAt g x ↔
      ∀ a b : TangentSpace I x,
        0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 →
          0 < metricRm04StandardAt g x a b b a := by
  constructor
  · intro h a b hab
    have hgram : 0 < algebraicCurvatureIdentityQuadraticEval g
        (fun _ : Fin 1 => 1) (fun _ => a) (fun _ => b) := by
      simpa only [algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one,
        one_mul, g.symm x b a, ← pow_two, one_pow] using hab
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt]
      using h 1 (fun _ => 1) (fun _ => a) (fun _ => b) hgram
  · intro h n c v w hnorm
    obtain ⟨a, b, hgram, hvalue⟩ := three_bivector_quadratic_realized g x _hdim
      (metricAlgebraicCurvatureTensorAt g x) c v w
    rw [← hvalue]
    simpa only [metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using
      h a b (hgram.symm ▸ hnorm)



end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem curvatureOperatorPositiveAt_of_leastCurvatureOperatorEigenvalueAt_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ E = 3)
    (hleast : 0 < leastCurvatureOperatorEigenvalueAt g x
      (metricAlgebraicCurvatureTensorAt g x)) :
    CurvatureOperatorPositiveAt g x := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  have hbound : curvatureOperatorLowerBoundAt g x
      (metricAlgebraicCurvatureTensorAt g x)
      (-leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x)) :=
    (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
      basis horth).mpr le_rfl
  intro n c v w hnorm
  have hquad := hbound n c v w
  exact lt_of_lt_of_le (mul_pos hleast hnorm) (by linarith [hquad])

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
