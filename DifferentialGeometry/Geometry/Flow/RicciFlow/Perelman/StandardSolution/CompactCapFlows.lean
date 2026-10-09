import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMixedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem exists_uniform_compact_cap_flows :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ, (∀ N, 0 ≤ B N) ∧
      ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R),
      ∃ S : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
        IsSolutionOn S ∧ S.base.metric 0 = compactDoubleMetric north R hR ∧
        (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (S.base.metric t)) ∧
        (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
        (∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
          HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
            (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t) ∧
        ∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 τ, ∀ x : S3,
          Real.sqrt (normSq0S (S.base.metric t) x (4 + a)
            (iteratedCovariantTimeDerivWithin S.base.metric
              (fun r => nablaKRm04Field S r a x) (Icc 0 τ) b t)) ≤ B N := by
  obtain ⟨A, _, hA⟩ := exists_pos_bounds_iterCov_compactDoubleMetric
  let τ := compactCurvatureControlTime 3 (A 0)
  have hτ : 0 < τ := compactCurvatureControlTime_pos _ _
  let K := Real.sqrt (2 * A 0 ^ 2 + 1)
  let B := fun N => endpointMixedCurvatureBound 3 N τ K A
  refine ⟨τ, hτ, B, (fun N => endpointMixedCurvatureBound_nonneg _ N _ _ _), ?_⟩
  intro north R hR
  let g₀ := compactDoubleMetric north R hR
  have hi (x : S3) : Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ A 0 := hA north R hR 0 x
  obtain ⟨T, hT, ⟨P⟩⟩ := exists_compact_flow_beyond_control_time g₀ (by simp) (A 0) hi
  have hτT : τ < T := by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hT
  let D := RealTimeInterval.closed 0 τ hτ.le
  let S := P.S.timeRestrict D
  have hsub : Icc 0 τ ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hτT⟩
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict P.isSolution hsub
    (fun t ht => ⟨ht.1, ht.2.trans hτT⟩)
  have hstart : S.base.metric 0 = g₀ := P.start
  have hg (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet) :=
    (P.joint x₀ i j).mono (prod_mono hsub subset_rfl)
  have hcurv : ∀ t ∈ Icc 0 τ, ∀ x : S3,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K := by
    have hinitial (x : S3) : Real.sqrt (normSq0S (P.S.base.metric 0) x 4
        (metricRm04 (P.S.base.metric 0) x)) ≤ A 0 := by
      have he : P.S.base.metric 0 = g₀ := P.start
      rw [he]
      exact hi x
    exact curvature_bound_from_initial_compact τ hτ.le (A 0) (by simp only [τ, finrank_euclideanSpace,
      Fintype.card_fin, le_refl]) _ P.S P.isSolution hsub
      (fun t ht => ⟨ht.1, ht.2.trans hτT⟩)
      (fun x₀ i j => (P.joint x₀ i j).mono (prod_mono hsub subset_rfl)) hinitial
  refine ⟨S, hS, hstart, (fun _ _ => ⟨by infer_instance⟩), hg, ?_, ?_⟩
  · intro t ht x v w
    exact P.pde t (hsub ht) x v w
  · intro N a b hab t ht x
    have hinit (j : ℕ) (_hj : j ≤ 3 * N) (y : S3) :
        Real.sqrt (nablaKRm04NormSqIntrinsic S j 0 y) ≤ A j := by
      unfold nablaKRm04NormSqIntrinsic
      rw [nablaKRm_eq_iterCov]
      change Real.sqrt (normSq0S (S.base.metric 0) y (4 + j)
        (iterCov (S.base.metric 0) 4 (metricRm04 (S.base.metric 0)) j y)) ≤ A j
      rw [hstart]
      exact hA north R hR j y
    have hdense : D.carrier ⊆ closure D.regular := by
      change Icc 0 τ ⊆ closure (Ioo 0 τ)
      rw [closure_Ioo hτ.ne]
    have hh := curvature_endpoint_mixed_bound τ hτ.le N K A D S hS (uniqueDiffOn_Icc hτ)
      hg hdense (Or.inr (inferInstance : CompactSpace S3)) subset_rfl subset_rfl hcurv hinit
      a b hab t ht x
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
    convert hh using 1
    all_goals rfl
end DifferentialGeometry.PDE.RicciFlow
