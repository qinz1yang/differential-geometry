import DifferentialGeometry.Analysis.ODE.ScalarODEComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointCurvatureBounds
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def compactCurvatureControlTime (n : ℕ) (K : ℝ) : ℝ :=
  1 / (2 * (rmTowerCost n 0 + 1) * (K ^ 2 + 1))

theorem compactCurvatureControlTime_pos (n : ℕ) (K : ℝ) :
    0 < compactCurvatureControlTime n K := by
  have hc := rmTowerCost_nonneg n 0
  unfold compactCurvatureControlTime
  positivity

theorem compactCurvatureControlTime_reaction_bound (n : ℕ) (K T : ℝ)
    (hT : T ≤ compactCurvatureControlTime n K) :
    rmTowerCost n 0 * (K ^ 2 + 1) * T ≤ 1 / 2 := by
  have hc := rmTowerCost_nonneg n 0
  apply (mul_le_mul_of_nonneg_left hT (mul_nonneg hc (by positivity))).trans
  unfold compactCurvatureControlTime
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (rmTowerCost n 0 + 1) * (K ^ 2 + 1))).mpr
  nlinarith [sq_nonneg K]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

private theorem curvature_bound_regular (T : ℝ) (hT : 0 < T) (K : ℝ)
    (hsmall : rmTowerCost (Module.finrank ℝ E) 0 * (K ^ 2 + 1) * T ≤ 1 / 2)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hreg : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hinit : ∀ x : M, Real.sqrt (normSq0S (S.base.metric 0) x 4 (metricRm04 (S.base.metric 0) x)) ≤ K) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤
        Real.sqrt (2 * K ^ 2 + 1) := by
  let u := nablaKRm04NormSqIntrinsic S 0
  let c := rmTowerCost (Module.finrank ℝ E) 0
  have hc : 0 ≤ c := rmTowerCost_nonneg _ _
  have hg := hgram
  have hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ univ) := by
    have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
      (uniqueDiffOn_Icc hT) hg 0).continuousOn
    apply hh.congr
    intro p _
    dsimp only [u]
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : M) :
      DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t := by
    obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution S hS 0 ⟨t, hreg t ht hp⟩ x
    exact (hd.mono hslab).differentiableWithinAt
  have hheat (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : M) :
      parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) u t x ≤ c * (u t x + 1) ^ 2 := by
    obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution S hS 0 ⟨t, hreg t ht hp⟩ x
    have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hT) t ht)
    rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
    change d - nablaKNormLap S 0 t x ≤ _
    have hnonneg : 0 ≤ u t x := nablaKRm04NormSqIntrinsic_nonneg S 0 t x
    have hs := Real.sq_sqrt hnonneg
    have hroot : Real.sqrt (u t x) ≤ u t x + 1 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith [sq_nonneg (u t x)]
    have hr : towerReactionSum (nablaKRm04NormSqIntrinsic S) c 0 t x =
        c * u t x * Real.sqrt (u t x) := by
      simp only [towerReactionSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.sub_zero]
      change c * Real.sqrt (u t x) * Real.sqrt (u t x) * Real.sqrt (u t x) = _
      calc
        _ = c * (Real.sqrt (u t x)) ^ 2 * Real.sqrt (u t x) := by ring
        _ = _ := by rw [hs]
    change d ≤ nablaKNormLap S 0 t x +
      (-2 * nablaKRm04NormSqIntrinsic S 1 t x + towerReactionSum (nablaKRm04NormSqIntrinsic S) c 0 t x) at hle
    rw [hr] at hle
    have hm := mul_le_mul_of_nonneg_left hroot (mul_nonneg hc hnonneg)
    have hnext := nablaKRm04NormSqIntrinsic_nonneg S 1 t x
    nlinarith [mul_nonneg hc (show 0 ≤ u t x + 1 by linarith)]
  have hb := DifferentialGeometry.Analysis.scalar_quadratic_reaction_bound_compact (flowG S) T hT.le (fun _ _ => 0) u c (K ^ 2)
    hc (sq_nonneg K) hsmall hu htime (fun t _ _ => nablaKNorm_smooth S t 0) hheat ?_
  · intro t ht x
    have hh := Real.sqrt_le_sqrt (hb t ht x)
    simp only [u, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero] at hh
    convert hh using 1
    all_goals rfl
  · intro x
    have hh := (Real.sqrt_le_iff.mp (hinit x)).2
    simp only [u, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero]
    convert hh using 1
    all_goals rfl

theorem curvature_bound_from_initial_compact (T : ℝ) (hT : 0 ≤ T) (K : ℝ)
    (hcontrol : T ≤ compactCurvatureControlTime (Module.finrank ℝ E) K)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hinit : ∀ x : M, Real.sqrt (normSq0S (S.base.metric 0) x 4 (metricRm04 (S.base.metric 0) x)) ≤ K) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤
        Real.sqrt (2 * K ^ 2 + 1) := by
  by_cases hp : 0 < T
  · intro t ht x
    have hb : ∀ r ∈ Ico 0 T,
        Real.sqrt (normSq0S (S.base.metric r) x 4 (metricRm04 (S.base.metric r) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
      intro r hr
      let τ := (r + T) / 2
      have hτ : 0 < τ := by dsimp only [τ]; linarith [hr.1]
      have hτT : τ < T := by dsimp only [τ]; linarith [hr.2]
      have hrτ : r ≤ τ := by dsimp only [τ]; linarith [hr.2]
      have hsub : Icc 0 τ ⊆ Icc 0 T := fun q hq => ⟨hq.1, hq.2.trans hτT.le⟩
      exact curvature_bound_regular τ hτ K
        (compactCurvatureControlTime_reaction_bound _ K τ (hτT.le.trans hcontrol)) D S hS
        (hsub.trans hslab) (fun q hq hqp => hregular ⟨hqp, hq.2.trans_lt hτT⟩)
        (fun x₀ i j => (hgram x₀ i j).mono (prod_mono hsub subset_rfl)) hinit r ⟨hr.1, hrτ⟩ x
    have hc : ContinuousOn (fun r =>
        Real.sqrt (normSq0S (S.base.metric r) x 4 (metricRm04 (S.base.metric r) x))) (Icc 0 T) := by
      have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
        (uniqueDiffOn_Icc hp) hgram 0).continuousOn.sqrt
      have hmap : Continuous (fun r : ℝ => (r, x)) := continuous_id.prodMk continuous_const
      have he := hh.comp hmap.continuousOn (fun r hr => ⟨hr, mem_univ x⟩)
      convert he using 1
      all_goals rfl
    have hcl : closure (Ico 0 T) = Icc 0 T := closure_Ico hp.ne
    rw [← hcl] at hc
    exact le_on_closure hb hc continuousOn_const (by rw [hcl]; exact ht)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    have hh : |K| ≤ Real.sqrt (2 * K ^ 2 + 1) := by
      simpa only [Real.sqrt_sq_eq_abs] using
        Real.sqrt_le_sqrt (show K ^ 2 ≤ 2 * K ^ 2 + 1 by nlinarith [sq_nonneg K])
    exact (hinit x).trans ((le_abs_self K).trans hh)
end DifferentialGeometry.PDE.RicciFlow
