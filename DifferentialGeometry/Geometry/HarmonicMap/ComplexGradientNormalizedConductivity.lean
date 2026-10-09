import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientRootConductivity
import DifferentialGeometry.Analysis.Complex.PowerConjugation
import DifferentialGeometry.Analysis.Elliptic.Planar.PowerPullback
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

open Set Filter Metric Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold
-- This scope supplies the finite-dimensional matrix regularity structures.
-- Every quantitative estimate below still uses the complex-plane operator norm.
open scoped Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry

private theorem complexPlaneMatrixOperator_one :
    complexPlaneMatrixOperator 1 = ContinuousLinearMap.id ℝ ℂ := by
  ext z
  apply Complex.ext <;> simp [complexPlaneMatrixOperator, Complex.real_smul]

private theorem complexPlaneMatrixOperator_mul
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    complexPlaneMatrixOperator (A * B) =
      (complexPlaneMatrixOperator A).comp (complexPlaneMatrixOperator B) := by
  ext z
  apply Complex.ext <;>
    simp [complexPlaneMatrixOperator, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.real_smul] <;> ring

private theorem complexPlaneMatrixOperator_complex_mul (q : ℂ) :
    complexPlaneMatrixOperator (Analysis.planarComplexMulMatrix q) =
      ContinuousLinearMap.mul ℝ ℂ q := by
  ext z
  apply Complex.ext <;>
    simp [complexPlaneMatrixOperator, Analysis.planarComplexMulMatrix,
      Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

private def complexPlaneOperatorMatrix :
    (ℂ →L[ℝ] ℂ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ((![Complex.reCLM, Complex.imCLM] : Fin 2 → ℂ →L[ℝ] ℝ) i).comp
      (ContinuousLinearMap.apply ℝ ℂ ((![1, Complex.I] : Fin 2 → ℂ) j))

private theorem complexPlaneOperatorMatrix_operator (A : Matrix (Fin 2) (Fin 2) ℝ) :
    complexPlaneOperatorMatrix (complexPlaneMatrixOperator A) = A := by
  ext i j
  change ((![Complex.reCLM, Complex.imCLM] : Fin 2 → ℂ →L[ℝ] ℝ) i)
    (complexPlaneMatrixOperator A ((![1, Complex.I] : Fin 2 → ℂ) j)) = A i j
  fin_cases i <;> fin_cases j <;>
    simp [complexPlaneMatrixOperator, Complex.real_smul]

private theorem complexPlaneMatrixOperator_power_conjugate
    (m : ℕ) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) :
    complexPlaneMatrixOperator (if w = 0 then 1 else
      Analysis.planarComplexMulMatrix (w ^ m)⁻¹ * A w *
        Analysis.planarComplexMulMatrix (w ^ m)) =
      Analysis.complexPowerConjugate m (fun z => complexPlaneMatrixOperator (A z)) w := by
  by_cases hw : w = 0
  · subst w
    simp [Analysis.complexPowerConjugate, complexPlaneMatrixOperator_one]
  · simp only [Analysis.complexPowerConjugate, ite_eq_right hw]
    rw [complexPlaneMatrixOperator_mul,
      complexPlaneMatrixOperator_mul, complexPlaneMatrixOperator_complex_mul,
      complexPlaneMatrixOperator_complex_mul]
    ext v
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The literal matrix principal in the normalized branch coordinate extends
with one continuous derivative and zero derivative at the center. Its operator
bounds and physical chart domain come from the same original-metric height and
leading frame. No coefficient estimate is an additional hypothesis. -/
theorem chartLeadingPlaneProjection_normalized_conductivity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ)
    {m : ℕ} (hm : 1 ≤ m) {H : ℂ → ℝ}
    (hH : ContDiffAt ℝ 2 H 0) (hH0 : H 0 = 0) (hDH : fderiv ℝ H 0 = 0)
    (hHess : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let R := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let Y : ℂ → E := fun w => extChartAt 𝓘(ℝ, E) p x + L (P w - c) + H w • N
    let G : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y w))
        (L (![1, Complex.I] i) + R w (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + R w (![1, Complex.I] j) • N)
    let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w =>
      Analysis.planarConductivity (G w 0 0) (G w 1 1) (G w 0 1)
    let Aop : ℂ → ℂ →L[ℝ] ℂ := fun w => complexPlaneMatrixOperator (A w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix (w ^ m)⁻¹ * A w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let Kop : ℂ → ℂ →L[ℝ] ℂ := fun w => complexPlaneMatrixOperator (K w)
    Aop 0 = ContinuousLinearMap.id ℝ ℂ ∧
      (∀ w, Kop w = Analysis.complexPowerConjugate m Aop w) ∧
      K 0 = 1 ∧ ContDiffAt ℝ 1 K 0 ∧
      HasFDerivAt K (0 : ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) 0 ∧
      ∃ C > 0,
        (∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 Aop w ∧
          ‖Aop w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
          ‖fderiv ℝ Aop w‖ ≤ C * ‖w‖) ∧
        (∀ᶠ w in 𝓝 (0 : ℂ),
          ‖Kop w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
          ‖fderiv ℝ Kop w‖ ≤ ((2 * (m : ℝ) + 1) * C) * ‖w‖) ∧
        ∀ᶠ w in 𝓝 (0 : ℂ),
          Y w ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
          0 < G w 0 0 * G w 1 1 - G w 0 1 ^ 2 := by
  intro R P Y G A Aop K Kop
  have hroot := chartLeadingPlaneProjection_root_conductivity_bounds
    g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  change (Aop 0 = ContinuousLinearMap.id ℝ ℂ ∧
    ∃ C > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 Aop w ∧
      ‖Aop w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖fderiv ℝ Aop w‖ ≤ C * ‖w‖) ∧
    ∀ᶠ w in 𝓝 (0 : ℂ), Y w ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      0 < G w 0 0 * G w 1 1 - G w 0 1 ^ 2 at hroot
  obtain ⟨⟨hA0, C, hC, hAb⟩, hdomain⟩ := hroot
  have hconj : Kop = Analysis.complexPowerConjugate m Aop := by
    funext w
    exact complexPlaneMatrixOperator_power_conjugate m A w
  have hrot := Analysis.contDiffAt_complexPowerConjugate_of_quadratic_order
    hm hC.le (hAb.mono fun _ hw => hw.1) (hAb.mono fun _ hw => hw.2)
  change ContDiffAt ℝ 1 (Analysis.complexPowerConjugate m Aop) 0 ∧
    HasFDerivAt (Analysis.complexPowerConjugate m Aop)
      (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) 0 ∧ _ at hrot
  rw [← hconj] at hrot
  have hmatrix : K = fun w => complexPlaneOperatorMatrix (Kop w) := by
    funext w
    exact (complexPlaneOperatorMatrix_operator (K w)).symm
  have hK : ContDiffAt ℝ 1 K 0 := by
    rw [hmatrix]
    exact complexPlaneOperatorMatrix.contDiff.contDiffAt.comp 0 hrot.1
  have hDK : HasFDerivAt K (0 : ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) 0 := by
    rw [hmatrix]
    refine (complexPlaneOperatorMatrix.hasFDerivAt.comp 0 hrot.2.1).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    change complexPlaneOperatorMatrix (0 : ℂ →L[ℝ] ℂ) = 0
    exact map_zero complexPlaneOperatorMatrix
  refine ⟨hA0, fun w => congrFun hconj w, ?_, hK, hDK, C, hC,
    hAb, hrot.2.2, hdomain⟩
  simp [K]

end DifferentialGeometry.Geometry
