import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Evolution.Solution
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem norm_bound_of_three_dimensional_trace
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ric : Tensor02At (I := I) (M := M) x) (scalar : ℝ)
    (Rm : Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (htrace : RiemannFromRicci3DTraceDataAt g Ric scalar Rm basis) :
    Real.sqrt (normSq0S g x 4 Rm) ≤ 63 * Real.sqrt (normSq0S g x 2 Ric) := by
  let K := Real.sqrt (normSq0S g x 2 Ric)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hinv : MetricInverseInBasis g x basis (identityInvMetric (Idx := Fin 3)) := by
    have he : (identityInvMetric : Fin 3 → Fin 3 → ℝ) = delta3 := by
      funext i j
      simp only [identityInvMetric, diagonalInvMetric, delta3]
    rw [he]
    exact orthonormal_invBasis3 g basis htrace.orthonormal
  have hRic (i j : Fin 3) : |ricciCompAt basis Ric i j| ≤ K :=
    component_le_sqrt g basis hinv Ric (slots2 i j)
  have hscalar : |scalar| ≤ 3 * K := by
    rw [htrace.scalar_trace]
    unfold standardScalar3
    rw [← htrace.ricci_trace 0 0, ← htrace.ricci_trace 1 1, ← htrace.ricci_trace 2 2]
    have hh := (abs_add_le (ricciCompAt basis Ric 0 0 + ricciCompAt basis Ric 1 1)
      (ricciCompAt basis Ric 2 2)).trans
      (add_le_add (abs_add_le (ricciCompAt basis Ric 0 0) (ricciCompAt basis Ric 1 1)) le_rfl)
    linarith [hRic 0 0, hRic 1 1, hRic 2 2]
  have hd (i j : Fin 3) : |delta3 i j| ≤ 1 := by
    unfold delta3
    split <;> norm_num
  have hdp (i j k l : Fin 3) : |delta3 i j * delta3 k l| ≤ 1 := by
    rw [abs_mul]
    have hh := mul_le_mul (hd i j) (hd k l) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hRd (i j k l : Fin 3) : |ricciCompAt basis Ric i j * delta3 k l| ≤ K := by
    rw [abs_mul]
    have hh := mul_le_mul (hRic i j) (hd k l) (abs_nonneg _) hK
    simpa only [mul_one] using hh
  have hswap (i j k l : Fin 3) : |rm04CompAt basis Rm i j l k| ≤ 7 * K := by
    rw [rm04Comp_displayedRiemannFromRicci3D_at htrace]
    have hdet : |delta3 i l * delta3 j k - delta3 j l * delta3 i k| ≤ 2 := by
      have hh := abs_sub (delta3 i l * delta3 j k) (delta3 j l * delta3 i k)
      linarith [hdp i l j k, hdp j l i k]
    have hlast : |(1 / 2 : ℝ) * scalar *
        (delta3 i l * delta3 j k - delta3 j l * delta3 i k)| ≤ 3 * K := by
      rw [abs_mul, abs_mul, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hscalar (by norm_num)) hdet
        (abs_nonneg _) (by positivity : 0 ≤ (1 / 2 : ℝ) * (3 * K))
      nlinarith
    have h1 := abs_sub
      (ricciCompAt basis Ric i l * delta3 j k) (ricciCompAt basis Ric j l * delta3 i k)
    have h2 := abs_sub
      (ricciCompAt basis Ric i l * delta3 j k - ricciCompAt basis Ric j l * delta3 i k)
      (ricciCompAt basis Ric i k * delta3 j l)
    have h3 := abs_add_le
      (ricciCompAt basis Ric i l * delta3 j k - ricciCompAt basis Ric j l * delta3 i k -
        ricciCompAt basis Ric i k * delta3 j l) (ricciCompAt basis Ric j k * delta3 i l)
    have h4 := abs_sub
      (ricciCompAt basis Ric i l * delta3 j k - ricciCompAt basis Ric j l * delta3 i k -
        ricciCompAt basis Ric i k * delta3 j l + ricciCompAt basis Ric j k * delta3 i l)
      ((1 / 2 : ℝ) * scalar * (delta3 i l * delta3 j k - delta3 j l * delta3 i k))
    linarith [hRd i l j k, hRd j l i k, hRd i k j l, hRd j k i l]
  have hcomp (i j k l : Fin 3) : |standardRmCompAt basis Rm i j k l| ≤ 7 * K :=
    hswap i j l k
  have hsum : standardRmNormSq3 (standardRmCompAt basis Rm) ≤
      ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _k : Fin 3, ∑ _l : Fin 3, (7 * K) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcomp i j k l)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [normSq0S_four_eq_standardRmNormSq3 htrace.orthonormal]
  change standardRmNormSq3 (standardRmCompAt basis Rm) ≤ (63 * K) ^ 2
  nlinarith

variable [CompleteSpace E] [T2Space M]

theorem sqrt_normSq_metricRm04_le_ricci_three
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤
      63 * Real.sqrt (normSq0S g x 2 (metricRicci g x)) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 0 le_rfl) :=
    { base := { metric := fun _ => g } }
  have ht := riemann_from_ricci_trace S (t := 0) horth
  have hh := norm_bound_of_three_dimensional_trace g x _ _ _ basis ht
  change Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤
    63 * Real.sqrt (normSq0S g x 2 (-(metricRicci g x))) at hh
  rw [show -(metricRicci g x) = (-1 : ℝ) • metricRicci g x by rw [neg_one_smul],
    sqrt_normSq0S_smul] at hh
  simpa only [abs_neg, abs_one, one_mul] using hh
end DifferentialGeometry.Geometry.Curvature
