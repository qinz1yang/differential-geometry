import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CurvatureTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.curvature_time_jet_regular (S : PartialStandardSolution) (a b : ℕ) (x : E3) :
    let U := iteratedCovariantTimeDerivWithin S.metric
      (fun t => nablaKRm04Field S.toSolutionOn t a x) S.domain b
    ContDiffOn ℝ ∞ U S.domain ∧
      ContDiffOn ℝ ∞ (fun t => normSq0S (S.metric t) x (4 + a) (U t)) S.domain := by
  classical
  let T := fun t => nablaKRm04Field S.toSolutionOn t a x
  let basis := coordinateFrameAtToBasis (I := 𝓡 3) x
  let B := fun t (i j : CoordinateIdx (𝕜 := ℝ) E3) =>
    inverseMetricFlatModelInChartComponent (S.metric t) x i j (extChartAt (𝓡 3) x x)
  have hJ := uniqueDiffOn_lifetimeInterval S.lifetime S.lifetime_pos
  have hg := chartGram_contMDiffOn_of_cartesian S.metric S.domain S.smooth
  have hT : ContDiffOn ℝ ∞ T S.domain := by
    apply tensor0S_contDiffOn_of_components basis
    intro m
    have hh := covariantRiemannComponents_contMDiffOn S.metric S.domain hJ hg x a m
    have hs := hh.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
      (fun r hr => ⟨hr, self_mem_chartLeviCivitaGoodSet (I := 𝓡 3) x⟩)
    have he : (fun r => component0S basis (T r) m) =
        (fun r => iterCov (S.metric r) 4 (metricRm04 (S.metric r)) a x
          (frameTuple (coordinateFrameAt (I := 𝓡 3) x) x m)) := by
      funext r
      unfold component0S
      dsimp only [T]
      rw [nablaKRm_eq_iterCov]
      apply congrArg (iterCov (S.metric r) 4 (metricRm04 (S.metric r)) a x)
      funext q
      exact coordinateFrameAt_toBasis_apply (I := 𝓡 3) x (m q)
    rw [he]
    exact hs.contDiffOn
  have hB (t : ℝ) (_ : t ∈ S.domain) : MetricInverseInBasis (S.metric t) x basis (B t) :=
    gInvBasisAt (S.metric t) x (coordinateFrameAt_mem (I := 𝓡 3) x)
  have hBs (i j : CoordinateIdx (𝕜 := ℝ) E3) : ContDiffOn ℝ ∞ (fun t => B t i j) S.domain := by
    have hh := inverseComponents_contMDiffOn S.metric S.domain hg x i j
    have hs := hh.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
      (fun r hr => ⟨hr, self_mem_chartLeviCivitaGoodSet (I := 𝓡 3) x⟩)
    exact hs.contDiffOn
  have hR (i j : CoordinateIdx (𝕜 := ℝ) E3) :
      ContDiffOn ℝ ∞ (fun t => ricciTensor (S.metric t) x (basis i) (basis j)) S.domain := by
    have hh := S.ricci_contDiffOn.comp (contDiffOn_id.prodMk (contDiffOn_const (c := x)))
      (fun r hr => ⟨hr, mem_univ x⟩)
    exact (hh.clm_apply (contDiffOn_const (c := basis i))).clm_apply (contDiffOn_const (c := basis j))
  have hu := iteratedCovariantTimeDerivWithin_contDiffOn S.metric T basis B S.domain hJ hB hBs hR hT b
  exact ⟨hu, normSq0S_contDiffOn_of_basis S.metric _ basis B S.domain hB hBs hu⟩

private theorem uniform_positive_first_time_bound (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : StandardSolution, ∀ k : ℕ, k + 2 ≤ N →
      ∀ t ∈ Ioc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x (4 + k)
          (covariantTimeDerivWithin S.val.metric
            (fun r => nablaKRm04Field S.val.toSolutionOn r k x) S.val.domain t)) ≤ B := by
  obtain ⟨C, hC, hnorm⟩ := uniformStandardLifetime_curvature_derivative_bounds_closed θ hθ hlt N
  obtain ⟨hT, _⟩ := uniformStandardLifetime_slab θ hθ hlt
  refine ⟨∑ k ∈ Finset.range (N + 1), curvatureTimeBound 3 k C,
    Finset.sum_nonneg (fun k _ => curvatureTimeBound_nonneg 3 k C hC), ?_⟩
  intro S k hk t ht x
  have hreg : t ∈ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt (hT S)⟩
  have hb := curvature_time_derivative_bound S.val.toSolutionOn S.val.isSolutionOn k
    ⟨t, hreg⟩ x C hC (fun j hj => hnorm S j (hj.trans hk) t ⟨ht.1.le, ht.2⟩ x)
  have hb' : Real.sqrt (normSq0S (S.val.metric t) x (4 + k)
      (covariantTimeDerivWithin S.val.metric
        (fun r => nablaKRm04Field S.val.toSolutionOn r k x) S.val.domain t)) ≤
          curvatureTimeBound 3 k C := by
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hb
    exact hb
  exact hb'.trans (Finset.single_le_sum (fun j _ => curvatureTimeBound_nonneg 3 j C hC)
    (Finset.mem_range.mpr (by omega)))

theorem uniformStandardLifetime_first_time_curvature_bounds_closed (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : StandardSolution, ∀ k : ℕ, k + 2 ≤ N →
      ∀ t ∈ Icc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x (4 + k)
          (covariantTimeDerivWithin S.val.metric
            (fun r => nablaKRm04Field S.val.toSolutionOn r k x) S.val.domain t)) ≤ B := by
  obtain ⟨η, hη, hθη, hηL⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hltη : θ < η := lt_of_not_ge (fun h =>
    (not_le_of_gt hθη) (ENNReal.ofReal_le_ofReal h))
  have hηpos : 0 < η := hθ.trans_lt hltη
  obtain ⟨B, hB, hbound⟩ := uniform_positive_first_time_bound η hη hηL N
  obtain ⟨hT, _⟩ := uniformStandardLifetime_slab η hη hηL
  refine ⟨B, hB, ?_⟩
  intro S k hk t ht x
  let f := fun r => Real.sqrt (normSq0S (S.val.metric r) x (4 + k)
    (covariantTimeDerivWithin S.val.metric
      (fun q => nablaKRm04Field S.val.toSolutionOn q k x) S.val.domain r))
  have hcont : ContinuousOn f (Icc 0 η) := by
    have hh := (S.val.curvature_time_jet_regular k 1 x).2.continuousOn.sqrt
    have hsub : Icc 0 η ⊆ S.val.domain := fun r hr =>
      (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos r).mpr
        ⟨hr.1, (ENNReal.ofReal_le_ofReal hr.2).trans_lt (hT S)⟩
    exact hh.mono hsub
  have hcl : closure (Ioc 0 η) = Icc 0 η := closure_Ioc hηpos.ne
  have hc : ContinuousOn f (closure (Ioc 0 η)) := by rw [hcl]; exact hcont
  have htcl : t ∈ closure (Ioc 0 η) := by rw [hcl]; exact ⟨ht.1, ht.2.trans hltη.le⟩
  exact le_on_closure (fun r hr => hbound S k hk r hr x) hc continuousOn_const htcl
end DifferentialGeometry.PDE.RicciFlow
