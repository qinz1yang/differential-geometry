import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def PartialStandardSolution.pointedFlow (S : PartialStandardSolution) :
    PointedFlowData (I := 𝓡 3) (lifetimeInterval S.lifetime S.lifetime_pos) where
  M := E3
  basepoint := 0
  S := S.toSolutionOn
  isSolution := S.isSolutionOn

@[simp] theorem PartialStandardSolution.pointedFlow_metric (S : PartialStandardSolution) (t : ℝ) :
    (S.pointedFlow.atTime t).metric = S.metric t := rfl

theorem PartialStandardSolution.pointedFlow_complete (S : PartialStandardSolution)
    (t : ℝ) (ht : t ∈ S.domain) : MetricComplete (S.pointedFlow.atTime t) := by
  exact (S.complete t ht).complete

theorem PartialStandardSolution.initial_curvature_derivative_norm (S : PartialStandardSolution)
    (k : ℕ) (x : E3) :
    nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x =
      normSq0S DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x (4 + k)
        (iterCov DifferentialGeometry.PDE.RicciFlow.StandardCap.metric 4
          (metricRm04 DifferentialGeometry.PDE.RicciFlow.StandardCap.metric) k x) := by
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm_eq_iterCov]
  change normSq0S (S.metric 0) x (4 + k) (iterCov (S.metric 0) 4
    (metricRm04 (S.metric 0)) k x) = _
  rw [S.initial]

theorem standard_initial_curvature_derivative_bounds :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧ ∀ S : PartialStandardSolution, ∀ k : ℕ, ∀ x : E3,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x) ≤ A k := by
  choose A hA hbound using DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04
  refine ⟨A, hA, ?_⟩
  intro S k x
  rw [S.initial_curvature_derivative_norm]
  exact hbound k x

theorem PartialStandardSolution.curvature_derivative_bound_positive (S : PartialStandardSolution)
    {δ θ K : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hθT : ENNReal.ofReal θ < S.lifetime)
    (hRm : ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : t ∈ Icc δ θ) (x : E3) :
    Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k t x) ≤
      Real.sqrt (rmOpenBound 3 (K ^ 2) 0 δ θ N k) := by
  have hslab : Icc 0 θ ⊆ S.domain := fun s hs =>
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hreg : Ioc 0 θ ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := fun s hs =>
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hcurv : ∀ s ∈ Icc 0 θ, ∀ y : S.pointedFlow.M, S.pointedFlow.rmNormSq s y ≤ K ^ 2 := by
    intro s hs y
    exact (Real.sqrt_le_iff.mp (hRm s hs y)).2
  have hcomplete := S.pointedFlow_complete 0 (hslab ⟨le_rfl, hδ.le.trans hδθ⟩)
  have h := movingRm_of_bound S.pointedFlow hδ hδθ hslab hreg hcomplete (sq_nonneg K)
    hcurv N k hk t ht x
  have hbound : nablaKRm04NormSqIntrinsic S.toSolutionOn k t x ≤
      rmOpenBound 3 (K ^ 2) 0 δ θ N k := by
    simpa only [PartialStandardSolution.pointedFlow, finrank_euclideanSpace, Fintype.card_fin] using h
  exact Real.sqrt_le_sqrt hbound

theorem uniformStandardLifetime_curvature_derivative_bounds (δ θ : ℝ)
    (hδ : 0 < δ) (hδθ : δ ≤ θ) (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : StandardSolution, ∀ k : ℕ, k ≤ N →
      ∀ t ∈ Icc δ θ, ∀ x : E3, Real.sqrt (nablaKRm04NormSqIntrinsic S.val.toSolutionOn k t x) ≤ C := by
  obtain ⟨hT, K, _, hRm⟩ := uniformStandardLifetime_slab θ (hδ.le.trans hδθ) hlt
  let B : ℕ → ℝ := fun k => Real.sqrt (rmOpenBound 3 (K ^ 2) 0 δ θ N k)
  refine ⟨∑ k ∈ Finset.range (N + 1), B k,
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _), ?_⟩
  intro S k hk t ht x
  have hb := S.val.curvature_derivative_bound_positive hδ hδθ (hT S) (hRm S) N k hk t ht x
  apply hb.trans
  exact Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _)
    (show k ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
end DifferentialGeometry.PDE.RicciFlow
