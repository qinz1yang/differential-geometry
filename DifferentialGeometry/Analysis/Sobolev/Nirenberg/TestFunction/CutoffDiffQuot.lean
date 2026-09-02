import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivative

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem fderiv_cutoff_sq_apply {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (j : Fin d) (x : E) :
    (fderiv ℝ (fun y : E => (η y)^2) x) (EuclideanSpace.single j 1) =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) := by
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  rw [fderiv_fun_pow 2 (hη_diff x), smul_apply]
  have h_pow : (η x) ^ ((2 : ℕ) - 1) = η x := by norm_num
  rw [h_pow]
  have h_two : ((2 : ℕ) • η x) = 2 * η x := by
    rw [two_smul]
    ring
  rw [h_two, smul_eq_mul]

omit [NeZero d] in
theorem hasWeakPartialDeriv_cutoff_sq_mul_diffQuot
    (k j : Fin d) (h : ℝ) {η u g_j : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure E).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure E).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (fun y => (η y)^2 * diffQuot k h g_j y +
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
          diffQuot k h u y)
      (fun y => (η y)^2 * diffQuot k h u y) Set.univ := by
  have h_wp_dq :
      DeGiorgi.HasWeakPartialDeriv (d := d) j
        (diffQuot k h g_j) (diffQuot k h u) Set.univ :=
    hasWeakPartialDeriv_diffQuot (d := d) k j h hu_locInt hg_j_locInt hwp
  have h_dq_u_locInt :
      LocallyIntegrable (diffQuot k h u)
        ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hu_locInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hu_locInt
  have h_dq_g_locInt :
      LocallyIntegrable (diffQuot k h g_j)
        ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hg_j_locInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hg_j_locInt
  exact DeGiorgi.HasWeakPartialDeriv.mul_smooth (Ω := Set.univ) isOpen_univ
    h_wp_dq (hη.pow 2) h_dq_u_locInt h_dq_g_locInt

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
