import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem closed_bound (S : PartialStandardSolution) (T : ℝ) (hT : 0 < T)
    (hTl : ENNReal.ofReal T < S.lifetime) (K : ℝ)
    (hcontrol : T ≤ compactCurvatureControlTime (Module.finrank ℝ E3) K)
    (hinit : ∀ x : E3, Real.sqrt (normSq0S (S.metric 0) x 4 (metricRm04 (S.metric 0) x)) ≤ K) :
    ∀ t ∈ Icc 0 T, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤
        Real.sqrt (2 * K ^ 2 + 1) := by
  let Q := S.toSolutionOn
  have Qsol : IsSolutionOn Q := S.isSolutionOn
  have hslab : Icc 0 T ⊆ S.domain := (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos T hT.le).mpr hTl
  have hreg (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) :
      t ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨hp, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTl⟩
  have hgram := chartGram_contMDiffOn_of_cartesian S.metric (Icc 0 T)
    (S.smooth.mono (prod_mono hslab subset_rfl))
  have hsmall := compactCurvatureControlTime_reaction_bound (Module.finrank ℝ E3) K T hcontrol
  let u := nablaKRm04NormSqIntrinsic Q 0
  let c := rmTowerCost (Module.finrank ℝ E3) 0
  have hc : 0 ≤ c := rmTowerCost_nonneg _ _
  have hg := hgram
  have hu : ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (Icc 0 T ×ˢ univ) := by
    have hh := (covariantRiemannNormSq_contMDiffOn Q.base.metric (Icc 0 T)
      (uniqueDiffOn_Icc hT) hg 0).continuousOn
    apply hh.congr
    intro p _
    dsimp only [u]
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : E3) :
      DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t := by
    obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution Q Qsol 0 ⟨t, hreg t ht hp⟩ x
    exact (hd.mono hslab).differentiableWithinAt
  have hheat (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : E3) :
      parabolicOperatorWithDrift (flowG Q) T (fun _ _ => 0) u t x ≤ -2 * nablaKRm04NormSqIntrinsic Q 1 t x + c * (u t x + 1) ^ 2 := by
    obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution Q Qsol 0 ⟨t, hreg t ht hp⟩ x
    have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hT) t ht)
    rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
    change d - nablaKNormLap Q 0 t x ≤ _
    have hnonneg : 0 ≤ u t x := nablaKRm04NormSqIntrinsic_nonneg Q 0 t x
    have hs := Real.sq_sqrt hnonneg
    have hroot : Real.sqrt (u t x) ≤ u t x + 1 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith [sq_nonneg (u t x)]
    have hr : towerReactionSum (nablaKRm04NormSqIntrinsic Q) c 0 t x =
        c * u t x * Real.sqrt (u t x) := by
      simp only [towerReactionSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.sub_zero]
      change c * Real.sqrt (u t x) * Real.sqrt (u t x) * Real.sqrt (u t x) = _
      calc
        _ = c * (Real.sqrt (u t x)) ^ 2 * Real.sqrt (u t x) := by ring
        _ = _ := by rw [hs]
    change d ≤ nablaKNormLap Q 0 t x +
      (-2 * nablaKRm04NormSqIntrinsic Q 1 t x + towerReactionSum (nablaKRm04NormSqIntrinsic Q) c 0 t x) at hle
    rw [hr] at hle
    have hm := mul_le_mul_of_nonneg_left hroot (mul_nonneg hc hnonneg)
    nlinarith [mul_nonneg hc (show 0 ≤ u t x + 1 by linarith)]
  obtain ⟨B, hB, hRm⟩ := S.curvature_bound T hT.le hTl
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) (x : E3) : u t x ≤ B ^ 2 :=
    (Real.sqrt_le_iff.mp (hRm t ht x)).2
  have hcomplete := S.complete 0 (hslab ⟨le_rfl, hT.le⟩)
  have hcut := nonempty_shi_barrier_cutoff_data_of_solution Q Qsol hT hslab
    (fun t ht => hreg t ⟨ht.1.le, ht.2⟩ ht.1) hcomplete (sq_nonneg B) hz
  have hb := DifferentialGeometry.Analysis.scalar_quadratic_reaction_bound_cutoffs (flowG Q) T hT
    u (nablaKRm04NormSqIntrinsic Q 1) c (K ^ 2) (B ^ 2) hc (sq_nonneg K) (sq_nonneg B)
    hsmall hu htime (fun t _ _ => nablaKNorm_smooth Q t 0) hz
    (fun t _ x => nablaKRm04NormSqIntrinsic_nonneg Q 1 t x)
    (fun t _ _ x => towerNorm_grad_le Q 0 t x) hheat
    (fun x => (Real.sqrt_le_iff.mp (hinit x)).2) hcut
  intro t ht x
  exact Real.sqrt_le_sqrt (hb t ht x)

theorem standard_uniform_initial_curvature_control :
    ∃ α : ℝ, 0 < α ∧ ∃ K : ℝ, 0 < K ∧ ∀ S : PartialStandardSolution,
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ α → ENNReal.ofReal θ < S.lifetime →
      ∀ t ∈ Icc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K := by
  obtain ⟨A, hA, hAb⟩ := standard_initial_curvature_derivative_bounds
  refine ⟨compactCurvatureControlTime (Module.finrank ℝ E3) (A 0),
    compactCurvatureControlTime_pos _ _, Real.sqrt (2 * (A 0) ^ 2 + 1),
    Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro S θ hθ hθα hθl
  have hinit (x : E3) : Real.sqrt (normSq0S (S.metric 0) x 4 (metricRm04 (S.metric 0) x)) ≤ A 0 :=
    hAb S 0 x
  by_cases hp : 0 < θ
  · exact closed_bound S θ hp hθl (A 0) hθα hinit
  · have he : θ = 0 := le_antisymm (le_of_not_gt hp) hθ
    subst θ
    intro t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    apply (hinit x).trans
    simpa only [Real.sqrt_sq (hA 0).le] using Real.sqrt_le_sqrt
      (show (A 0) ^ 2 ≤ 2 * (A 0) ^ 2 + 1 by nlinarith [sq_nonneg (A 0)])
end DifferentialGeometry.PDE.RicciFlow
