import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalizedConductivity
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false

noncomputable section

open Set Filter Metric Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold InnerProductSpace

namespace DifferentialGeometry.Geometry

private theorem complexMulMatrix_inv_transpose (q : ℂ) :
    Analysis.planarComplexMulMatrix q⁻¹ =
      (Complex.normSq q)⁻¹ • (Analysis.planarComplexMulMatrix q).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Analysis.planarComplexMulMatrix, Matrix.transpose_apply,
      Complex.inv_re, Complex.inv_im, div_eq_mul_inv, mul_comm]

private theorem complexMulMatrix_det (q : ℂ) :
    (Analysis.planarComplexMulMatrix q).det = Complex.normSq q := by
  simp only [Analysis.planarComplexMulMatrix, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.normSq_apply]
  ring

private theorem complex_conjugate_isSymm
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsSymm) (q : ℂ) :
    (Analysis.planarComplexMulMatrix q⁻¹ * A * Analysis.planarComplexMulMatrix q).IsSymm := by
  rw [complexMulMatrix_inv_transpose, Matrix.smul_mul, Matrix.smul_mul]
  apply Matrix.IsSymm.smul
  change ((Analysis.planarComplexMulMatrix q).transpose * A *
    Analysis.planarComplexMulMatrix q).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]

private theorem complex_conjugate_det_one
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) {q : ℂ} (hq : q ≠ 0) :
    (Analysis.planarComplexMulMatrix q⁻¹ * A * Analysis.planarComplexMulMatrix q).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, complexMulMatrix_det, complexMulMatrix_det,
    Complex.normSq_inv, hA, mul_one, inv_mul_cancel₀ (Complex.normSq_pos.mpr hq).ne']

private theorem complex_operator_quadratic_bounds
    {T : ℂ →L[ℝ] ℂ} (hT : ‖T - ContinuousLinearMap.id ℝ ℂ‖ ≤ (1 / 2 : ℝ))
    (v : ℂ) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ⟪v, T v⟫_ℝ ∧
      ⟪v, T v⟫_ℝ ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2 := by
  have hdiff : |⟪v, T v⟫_ℝ - ‖v‖ ^ 2| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
    calc
      _ = |⟪v, (T - ContinuousLinearMap.id ℝ ℂ) v⟫_ℝ| := by
        simp only [sub_apply, ContinuousLinearMap.id_apply,
          inner_sub_right, real_inner_self_eq_norm_sq]
      _ ≤ ‖v‖ * ‖(T - ContinuousLinearMap.id ℝ ℂ) v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖T - ContinuousLinearMap.id ℝ ℂ‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((T - ContinuousLinearMap.id ℝ ℂ).le_opNorm v)
          (norm_nonneg v)
      _ ≤ ‖v‖ * ((1 / 2 : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
          (norm_nonneg v)
      _ = (1 / 2 : ℝ) * ‖v‖ ^ 2 := by ring
  obtain ⟨hl, hu⟩ := abs_le.mp hdiff
  constructor <;> nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The same original-metric normalized principal is symmetric, has determinant
one, and is uniformly elliptic on a single neighborhood of the center. The
quadratic estimates use the complex-plane Euclidean norm. -/
theorem chartLeadingPlaneProjection_normalized_conductivity_structure
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
    let _Aop : ℂ → ℂ →L[ℝ] ℂ := fun w => complexPlaneMatrixOperator (A w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix (w ^ m)⁻¹ * A w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let Kop : ℂ → ℂ →L[ℝ] ℂ := fun w => complexPlaneMatrixOperator (K w)
    ∃ ε > 0, ∀ w ∈ ball (0 : ℂ) ε,
      Y w ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      0 < G w 0 0 * G w 1 1 - G w 0 1 ^ 2 ∧
      (K w).IsSymm ∧ (K w).det = 1 ∧
      ∀ v : ℂ, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ⟪v, Kop w v⟫_ℝ ∧
        ⟪v, Kop w v⟫_ℝ ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2 := by
  intro R P Y G A _Aop K Kop
  obtain ⟨_hA0, _hconj, hK0, _hK, _hDK, C, _hC, _hAb, hKb, hdomain⟩ :=
    chartLeadingPlaneProjection_normalized_conductivity
      g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  change K 0 = 1 at hK0
  have hlim : Tendsto (fun w : ℂ => C * ‖w‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((continuous_norm.tendsto (0 : ℂ)).pow 2)
  have hsmall : ∀ᶠ w in 𝓝 (0 : ℂ), C * ‖w‖ ^ 2 < (1 / 2 : ℝ) :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖Kop w - ContinuousLinearMap.id ℝ ℂ‖ ≤ (1 / 2 : ℝ) ∧
      Y w ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      0 < G w 0 0 * G w 1 1 - G w 0 1 ^ 2 := by
    filter_upwards [hKb, hdomain, hsmall] with w hw hd hs
    exact ⟨hw.1.trans hs.le, hd⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro w hw
  obtain ⟨hnorm, hY, hdetG⟩ := hεsub hw
  have hAsymm : (A w).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A, Analysis.planarConductivity]
  have hAdet : (A w).det = 1 := Analysis.det_planarConductivity hdetG
  refine ⟨hY, hdetG, ?_, ?_, complex_operator_quadratic_bounds hnorm⟩
  · by_cases hw0 : w = 0
    · subst w
      rw [hK0]
      exact Matrix.isSymm_one
    · simpa only [K, ite_eq_right hw0] using complex_conjugate_isSymm hAsymm (w ^ m)
  · by_cases hw0 : w = 0
    · subst w
      rw [hK0, Matrix.det_one]
    · simpa only [K, ite_eq_right hw0] using complex_conjugate_det_one hAdet (pow_ne_zero _ hw0)

end DifferentialGeometry.Geometry
