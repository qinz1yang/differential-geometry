import DifferentialGeometry.Analysis.Parabolic.Bernstein.Reaction
import DifferentialGeometry.Analysis.Calculus.TimeJet.CompleteEndpointTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

def completeCurvatureEndpointBound (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) : ℝ :=
  Real.sqrt (DifferentialGeometry.Analysis.completeEndpointTowerBound
    (∑ k ∈ Finset.range (N + 1), rmTowerCost n k) K T A N) +
      ∑ k ∈ Finset.range (N + 1), |A k|

theorem completeCurvatureEndpointBound_nonneg (n N : ℕ) (T K : ℝ) (A : ℕ → ℝ) :
    0 ≤ completeCurvatureEndpointBound n N T K A :=
  add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg (A k))

theorem completeCurvatureEndpointBound_congr_initial (n N : ℕ) (T K : ℝ) (A B : ℕ → ℝ)
    (hAB : ∀ k ≤ N, A k = B k) :
    completeCurvatureEndpointBound n N T K A = completeCurvatureEndpointBound n N T K B := by
  unfold completeCurvatureEndpointBound
  rw [DifferentialGeometry.Analysis.completeEndpointTowerBound_congr_initial _ K T A B N hAB]
  congr 1
  exact Finset.sum_congr rfl fun k hk => congrArg abs (hAB k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk))

theorem curvature_endpoint_bound_complete (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K) (A : ℕ → ℝ)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0)) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K)
    (hinit : ∀ k ≤ N, ∀ x : M, Real.sqrt (nablaKRm04NormSqIntrinsic S k 0 x) ≤ A k) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤
        completeCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
  classical
  by_cases hp : 0 < T
  · have hT := hp
    let c := ∑ k ∈ Finset.range (N + 1), rmTowerCost (Module.finrank ℝ E) k
    have hc : 0 ≤ c := Finset.sum_nonneg (fun k _ => rmTowerCost_nonneg _ k)
    have hcost (k : ℕ) (hk : k ≤ N) : rmTowerCost (Module.finrank ℝ E) k ≤ c :=
      Finset.single_le_sum (fun j _ => rmTowerCost_nonneg _ j) (Finset.mem_range.mpr (by omega))
    have hcont (k : ℕ) (_ : k ≤ N) :
        ContinuousOn (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S k p.1 p.2) (Icc 0 T ×ˢ univ) := by
      have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
        (uniqueDiffOn_Icc hT) hgram k).continuousOn
      apply hh.congr
      intro p _
      dsimp only
      unfold nablaKRm04NormSqIntrinsic
      rw [nablaKRm_eq_iterCov]
      rfl
    have htime (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (hp : 0 < t) (x : M) :
        DifferentiableWithinAt ℝ (fun s => nablaKRm04NormSqIntrinsic S k s x) (Icc 0 T) t := by
      obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution S hS k ⟨t, hregular t ht hp⟩ x
      exact (hd.mono hslab).differentiableWithinAt
    have hheat (k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : t ∈ Icc 0 T)
        (hp : 0 < t) (x : M) :
        parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) (nablaKRm04NormSqIntrinsic S k) t x ≤
          -2 * nablaKRm04NormSqIntrinsic S (k + 1) t x +
            towerReactionSum (nablaKRm04NormSqIntrinsic S) c k t x := by
      obtain ⟨d, hd, hle⟩ := (towerHeatBoundOn_of_solution S hS k).mono_const (hcost k hk)
        ⟨t, hregular t ht hp⟩ x
      have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hT) t ht)
      rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
      change d - nablaKNormLap S k t x ≤ _
      exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hle)
    have hz (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) : nablaKRm04NormSqIntrinsic S 0 t x ≤ K ^ 2 :=
      (Real.sqrt_le_iff.mp (hcurv t ht x)).2
    have hcut := nonempty_shi_barrier_cutoff_data_of_solution S hS hT hslab
      (fun t ht => hregular t ⟨ht.1.le, ht.2⟩ ht.1) hcomplete (sq_nonneg K) hz
    have hb := DifferentialGeometry.Analysis.endpoint_tower_bound_complete (flowG S) T hT
      (nablaKRm04NormSqIntrinsic S) N c K A hc hK
      (fun k _ t _ x => nablaKRm04NormSqIntrinsic_nonneg S k t x) hz hcont
      (fun k _ t ht hp x => htime k t ht hp x)
      (fun k _ t _ _ => nablaKNorm_smooth S t k)
      (fun k hk x => (Real.sqrt_le_iff.mp (hinit k hk x)).2) hheat
      (fun k _ t _ _ x => towerNorm_grad_le S k t x) hcut
    intro k hk t ht x
    exact (Real.sqrt_le_sqrt (hb k hk t ht x)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg (A j)))
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro k hk t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    have hsum : |A k| ≤ ∑ j ∈ Finset.range (N + 1), |A j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_range.mpr (by omega))
    exact ((hinit k hk x).trans (le_abs_self _)).trans
      (hsum.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _)))

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.curvature_derivative_bound_closed (S : PartialStandardSolution)
    {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hθT : ENNReal.ofReal θ < S.lifetime)
    (hRm : ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (N : ℕ) (A : ℕ → ℝ)
    (hinit : ∀ k ≤ N, ∀ x : E3, Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x) ≤ A k) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k t x) ≤
        completeCurvatureEndpointBound 3 N θ K A := by
  have hslab : Icc 0 θ ⊆ S.domain := fun s hs =>
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hreg : ∀ t ∈ Icc 0 θ, 0 < t → t ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular := fun t ht hp =>
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨hp, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hθT⟩
  have hg := chartGram_contMDiffOn_of_cartesian S.metric (Icc 0 θ)
    (S.smooth.mono (prod_mono hslab subset_rfl))
  have hh := curvature_endpoint_bound_complete θ hθ N K hK A _ S.toSolutionOn S.isSolutionOn
    (S.complete 0 (hslab ⟨le_rfl, hθ⟩)) hslab hreg hg hRm hinit
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hh

theorem uniformStandardLifetime_curvature_derivative_bounds_closed (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : StandardSolution, ∀ k : ℕ, k ≤ N →
      ∀ t ∈ Icc 0 θ, ∀ x : E3, Real.sqrt (nablaKRm04NormSqIntrinsic S.val.toSolutionOn k t x) ≤ C := by
  obtain ⟨hT, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  obtain ⟨A, _, hinit⟩ := standard_initial_curvature_derivative_bounds
  refine ⟨completeCurvatureEndpointBound 3 N θ K A, completeCurvatureEndpointBound_nonneg _ _ _ _ _, ?_⟩
  intro S
  exact S.val.curvature_derivative_bound_closed hθ hK (hT S) (hRm S) N A (fun k _ x => hinit S.val k x)
end DifferentialGeometry.PDE.RicciFlow
