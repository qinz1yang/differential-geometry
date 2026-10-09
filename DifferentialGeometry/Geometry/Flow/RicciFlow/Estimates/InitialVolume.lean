import DifferentialGeometry.Geometry.Comparison.Volume.CompactSmallBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.BallVolumeComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem exists_uniform_initial_ball_volume_lower_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ τ ρ κ : ℝ, 0 < τ ∧ 0 < ρ ∧ 0 < κ ∧
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
        S.base.metric 0 = g → ∀ {T : ℝ},
        Icc 0 T ⊆ D.carrier → Ioo 0 T ⊆ D.regular →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
              (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        ∀ t ∈ Icc (0 : ℝ) T, t ≤ τ → ∀ x : M,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
              riemannianVolumeMeasure (I := I) (M := M) (S.base.metric t)
                (riemannianBallOf (S.base.metric t) x r) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨ρ, κ₀, hρ, hκ₀, hvolume⟩ :=
    Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound g
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).mp hdim
    have heq (h : SmoothRiemannianMetric I M) : h = g := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      let _ : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
      have hv : v = 0 := Subsingleton.elim _ _
      simp only [hv, map_zero, zero_apply]
    refine ⟨1, ρ, κ₀, zero_lt_one, hρ, hκ₀, ?_⟩
    intro D S _ _ T _ _ _ t _ _ x r hr hrρ
    rw [heq (S.base.metric t)]
    exact hvolume x r hr hrρ
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  obtain ⟨K₂, _, hcurv₂⟩ := exists_rm04_bound g
  let K := Real.sqrt K₂
  have hcurv : ∀ x : M, Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K :=
    fun x => Real.sqrt_le_sqrt (hcurv₂ x)
  let τ := compactCurvatureControlTime (Module.finrank ℝ E) K
  let B := Real.sqrt (2 * K ^ 2 + 1)
  let κ := Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 3 * B * τ)) * κ₀
  have hτ : 0 < τ := compactCurvatureControlTime_pos _ K
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨τ, ρ, κ, hτ, hρ, mul_pos (Real.exp_pos _) hκ₀, ?_⟩
  intro D S hS hinit T hcarrier hregular hgram t ht htτ x r hr hrρ
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  have hslab : Icc (0 : ℝ) t ⊆ D.carrier := hsub.trans hcarrier
  have hreg : Ioo (0 : ℝ) t ⊆ D.regular :=
    (Ioo_subset_Ioo_right ht.2).trans hregular
  have hRm := curvature_bound_from_initial_compact t ht.1 K htτ D S hS
    hslab hreg (fun x₀ i j => (hgram x₀ i j).mono (prod_mono hsub subset_rfl))
    (fun y => by rw [hinit]; exact hcurv y)
  have hvol := riemannianVolumeMeasure_ball_ge_of_initial_volume_ratio_and_curvature_bound
    S hS ht.1 hB hslab hreg hRm
    (show t ∈ Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩) x
    (κ := κ₀) (R := ρ) (fun r hr hrρ => by rw [hinit]; exact hvolume x r hr hrρ) hr hrρ
  have hκ : κ ≤ Real.exp (-(2 * (Module.finrank ℝ E : ℝ) ^ 3 * B * t)) * κ₀ := by
    apply mul_le_mul_of_nonneg_right _ hκ₀.le
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left htτ
      (show 0 ≤ 2 * (Module.finrank ℝ E : ℝ) ^ 3 * B by positivity)
    linarith
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hκ) (by positivity)).trans hvol

end DifferentialGeometry.PDE.RicciFlow
