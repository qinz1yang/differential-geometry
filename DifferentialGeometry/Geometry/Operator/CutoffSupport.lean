import DifferentialGeometry.Geometry.Operator.GradientRegularity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_gradient_eq_zero_of_eventuallyEq_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {χ : M → ℝ} {c : ℝ} {q : M}
    (he : χ =ᶠ[nhds q] fun _ => c) :
    laplacian cov g χ q = 0 ∧ gradientFun g χ q = 0 := by
  have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ q :=
    contMDiffAt_const.congr_of_eventuallyEq he
  constructor
  · calc
      _ = laplacian cov g (fun _ : M => c) q :=
        laplacian_congr_of_eventuallyEq cov g hc contMDiffAt_const he
      _ = 0 := laplacian_const cov g c q
  · apply gradientFun_eq_zero_of_mfderiv_eq_zero
    rw [he.mfderiv_eq]
    exact mfderiv_const

theorem exists_isCompact_laplacian_gradient_support_of_eventuallyEq_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {χ : M → ℝ} (hc : HasCompactSupport χ)
    {p : M} {c : ℝ} (hp : χ =ᶠ[nhds p] fun _ => c) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tsupport χ ∧ p ∉ K ∧
      ∀ q ∉ K, laplacian cov g χ q = 0 ∧ gradientFun g χ q = 0 := by
  obtain ⟨U, hUχ, hU, hpU⟩ := mem_nhds_iff.mp hp
  refine ⟨tsupport χ \ U, hc.diff hU, sdiff_subset, fun hpK => hpK.2 hpU, ?_⟩
  intro q hq
  by_cases hqs : q ∈ tsupport χ
  · have hqU : q ∈ U := by
      by_contra hqU
      exact hq ⟨hqs, hqU⟩
    exact laplacian_gradient_eq_zero_of_eventuallyEq_const cov g
      (Filter.Eventually.mono (hU.mem_nhds hqU) hUχ)
  · exact laplacian_gradient_eq_zero_of_eventuallyEq_const cov g
      (notMem_tsupport_iff_eventuallyEq.mp hqs)

end DifferentialGeometry.Geometry.Operator
