import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution

noncomputable section
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Soliton
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_curvatureOperatorKernelAt_parallel
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    (hdim : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain σ) :
    IsParallelContinuousAlternatingSubmoduleFamily
      (canonicalMetric g f σ hcomplete hsol ht)
      (fun x => curvatureOperatorKernelAt (canonicalMetric g f σ hcomplete hsol ht) x
        ⟨metricRm04At (canonicalMetric g f σ hcomplete hsol ht) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (canonicalMetric g f σ hcomplete hsol ht) x⟩) := by
  let q : ℝ := 1 - σ * t
  let b : ℝ := t + q / (2 * (σ + 1))
  have hσ1 : 0 < σ + 1 := by linarith
  have hq : 0 < q := mem_canonicalTimeDomain_iff.mp ht
  have hden : 0 < (2 : ℝ) * (σ + 1) := mul_pos two_pos hσ1
  have htb : t < b := by
    dsimp [b]
    exact lt_add_of_pos_right t (div_pos hq hden)
  have hb : b ∈ canonicalTimeDomain σ := by
    rw [mem_canonicalTimeDomain_iff]
    dsimp [b, q]
    have hfactor : 0 < 1 - σ / (2 * (σ + 1)) := by
      apply sub_pos.mpr
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hEq : 1 - σ * b = (1 - σ * t) * (1 - σ / (2 * (σ + 1))) := by
      dsimp [b, q]
      field_simp
      ring
    rw [hEq]
    exact mul_pos hq hfactor
  have hD : Set.Iio b ⊆ canonicalTimeDomain σ := by
    intro r hr
    rw [mem_canonicalTimeDomain_iff]
    have hsigma : σ * r ≤ σ * b := mul_le_mul_of_nonneg_left hr.le hσ
    have hbpos := mem_canonicalTimeDomain_iff.mp hb
    linarith
  let D := RealTimeInterval.infiniteOpen b t htb
  have hD' : D.carrier ⊆ canonicalTimeDomain σ := by
    change Set.Iio b ⊆ canonicalTimeDomain σ
    exact hD
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD'
  have hreg : Set.Icc (t - 1) t ⊆ D.regular := by
    intro r hr
    change r < b
    exact lt_of_le_of_lt hr.2 htb
  have hst : t - 1 < t := by linarith
  have hR : ∀ r ∈ Set.Icc (t - 1) t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    apply curvatureOperator_nonnegative_of_complete_ancient S hS
    · intro s hs
      change s < b
      exact lt_of_le_of_lt hs (lt_of_le_of_lt hr.2 htb)
    · intro s hs
      change s < b
      exact lt_of_lt_of_le hs (le_of_lt (lt_of_le_of_lt hr.2 htb))
    · intro s hs
      have hsD : s ∈ D.carrier := by
        change s < b
        exact lt_of_le_of_lt hs (lt_of_le_of_lt hr.2 htb)
      exact canonicalSolutionOn_complete g f σ hcomplete hsol D hD' hsD
    · exact hdim
  have hpar := curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hst hreg hR
  have hmetric : S.family.metric t = canonicalMetric g f σ hcomplete hsol ht := by
    change canonicalMetricFamily (I := I) g f σ hcomplete hsol t = _
    exact canonicalMetricFamily_eq g f σ hcomplete hsol ht
  rw [hmetric] at hpar
  exact hpar

end DifferentialGeometry.PDE.RicciFlow.Soliton

namespace DifferentialGeometry.Geometry
open Curvature Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Soliton
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem gradientRicciSoliton_curvatureOperatorKernelAt_parallel
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3) :
    IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) := by
  let b : ℝ := (σ + 1)⁻¹
  have hden : 0 < σ + 1 := by linarith
  have hb : 0 < b := inv_pos.mpr hden
  have hσb : σ * b < 1 := by
    have hdiv : σ * b = σ / (σ + 1) := by
      dsimp [b]
      rw [div_eq_mul_inv]
    rw [hdiv]
    exact (div_lt_iff₀ hden).2 (by linarith)
  let D := RealTimeInterval.infiniteOpen b 0 hb
  have hD : D.carrier ⊆ canonicalTimeDomain σ := by
    intro t ht
    change 0 < 1 - σ * t
    have ht' : t < b := ht
    have hmul : σ * t ≤ σ * b := mul_le_mul_of_nonneg_left ht'.le hσ
    linarith
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : Icc (-1 : ℝ) 0 ⊆ D.regular := by
    intro t ht
    change t < b
    exact ht.2.trans_lt hb
  have hR : ∀ r ∈ Icc (-1 : ℝ) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun t ht => ht.trans_lt (hr.2.trans_lt hb))
      (fun t ht => ht.trans (hr.2.trans_lt hb))
      (fun t ht => canonicalSolutionOn_complete g f σ hcomplete hsol D hD
        (ht.trans_lt (hr.2.trans_lt hb))) hdim x
  have hk := curvatureOperatorKernelAt_parallel_at_later_time S hS hdim
    (show (-1 : ℝ) < 0 by norm_num) hreg hR
  have hzero : S.family.metric 0 = g :=
    canonicalSolutionOn_metric_zero g f σ hcomplete hsol D
  rw [hzero] at hk
  exact hk
end DifferentialGeometry.Geometry
