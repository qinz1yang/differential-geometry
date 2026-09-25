import DifferentialGeometry.Geometry.Metric.Family.Cartesian
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCapMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology BigOperators ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem exists_uniform_bounded_complete_cap_limit :
    ∃ τ : ℝ, 0 < τ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ _north : S3,
    ∃ g : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
      g 0 = metric ∧ (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (g t)) ∧
      (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
          (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
      (∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
        HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) ∧
      ∀ t ∈ Icc 0 τ, ∀ x : E3,
        Real.sqrt (normSq0S (g t) x 4 (metricRm04 (g t) x)) ≤ K := by
  obtain ⟨τ, hτ, B, hB, hdata⟩ := exists_complete_closed_cap_limit_data
  refine ⟨τ, hτ, 567 * B 0, mul_nonneg (by norm_num) (hB 0), ?_⟩
  intro north
  obtain ⟨S, hS, _, _, _, _, hRm, bf, hsrc, htgt, cLow, hcLow, co,
    hbound, hcovTail, hzero, hc, hg, hpde, _⟩ := hdata north
  refine ⟨co.gInf, hzero, hc, hg, hpde, ?_⟩
  have hRicSeq (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (y : S3) :
      ricciNorm (S j) t y ≤ 81 * (B 0) ^ 2 := by
    have hR := hRm 0 j 0 0 (by norm_num) t ht y
    change Real.sqrt (normSq0S ((S j).base.metric t) y 4
      (nablaKRm04Field (S j) t 0 y)) ≤ B 0 at hR
    have hRsq := (Real.sqrt_le_iff.mp hR).2
    have hh := ricTower_normSq_le (S j) t 0 y
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      Nat.reduceAdd, pow_succ, pow_zero] at hh
    change ricciNorm (S j) t y ≤ 81 *
      normSq0S ((S j).base.metric t) y 4 (nablaKRm04Field (S j) t 0 y) at hh
    nlinarith
  intro t ht x
  have hconv := co.ricNorm_convergence_at (compactCapPointedMaps north S hS)
    metric bf hsrc htgt 0 τ cLow hcLow hbound hcovTail ht x
  have hRic : normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x) ≤ 81 * (B 0) ^ 2 := by
    apply le_of_tendsto hconv
    exact Filter.Eventually.of_forall (fun j => hRicSeq (co.φ j) t ht _)
  have hsqrt : Real.sqrt (normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x)) ≤ 9 * B 0 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num) (hB 0), by nlinarith⟩
  have hthree := sqrt_normSq_metricRm04_le_ricci_three (co.gInf t) x
    (by change Module.finrank ℝ E3 = 3; exact finrank_euclideanSpace_fin)
  nlinarith

private theorem equation_through_initial (τ : ℝ) (hτ : 0 < τ)
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (hgram : ∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet))
    (hRF : ∀ t ∈ Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    ∀ t ∈ Ico 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (Ici 0) t := by
  have hjoint := fun x₀ i j => (hgram x₀ i j).mono (prod_mono Ico_subset_Icc_self subset_rfl)
  have hg (x : E3) (v w : TangentSpace (𝓡 3) x) :
      ContinuousOn (fun t => (g t).inner x v w) (Ico 0 τ) := by
    exact (tensor0SEvalCLM (I := 𝓡 3) (vec2 v w)).continuous.comp_continuousOn
      (metricCovDeriv_contDiffOn_time g (Ico 0 τ) hjoint metric 0 x).continuousOn
  have hRicField := ricciCont_of_joint g (Ico 0 τ) (uniqueDiffOn_Ico 0 τ) hjoint
  have hRic (x : E3) (v w : TangentSpace (𝓡 3) x) :
      ContinuousOn (fun t => ricciTensor (g t) x v w) (Ico 0 τ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Ico 0 τ => ricciTensor (g t.val) x v w)
    have hh := hRicField.eval_continuous
      (P := Ico 0 τ) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun t => t.property) continuous_const
      (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using hh
  intro t ht x v w
  by_cases ht0 : t = 0
  · subst t
    exact metric_right_derivative_of_interior hτ g hg hRic hRF x v w
  · exact (hRF t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩ x v w).hasDerivWithinAt

theorem exists_uniform_partial_standard_solution :
    ∃ τ : ℝ, 0 < τ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ _north : S3,
      ∃ S : PartialStandardSolution, S.lifetime = ENNReal.ofReal τ ∧
        (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (S.metric t)) ∧
        ∀ t ∈ Icc 0 τ, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K := by
  obtain ⟨τ, hτ, K, hK, hlimits⟩ := exists_uniform_bounded_complete_cap_limit
  refine ⟨τ, hτ, K, hK, ?_⟩
  intro north
  obtain ⟨g, hzero, hc, hg, hpde, hRm⟩ := hlimits north
  have hdomain : (lifetimeInterval (ENNReal.ofReal τ) (ENNReal.ofReal_pos.mpr hτ)).carrier =
      Ico 0 τ := by rw [lifetimeInterval_ofReal τ hτ]; rfl
  have hregular := cartesian_contDiffOn_of_chartGram g (Icc 0 τ) hg
  let S : PartialStandardSolution :=
    { lifetime := ENNReal.ofReal τ
      lifetime_pos := ENNReal.ofReal_pos.mpr hτ
      metric := g
      smooth := by
        rw [hdomain]
        exact hregular.mono (prod_mono Ico_subset_Icc_self subset_rfl)
      equation := by
        rw [hdomain]
        exact equation_through_initial τ hτ g hg hpde
      initial := hzero
      complete := by
        rw [hdomain]
        exact fun t ht => hc t (Ico_subset_Icc_self ht)
      curvature_bound := by
        intro θ hθ hθτ
        have hθτ' : θ < τ := (ENNReal.ofReal_lt_ofReal_iff hτ).mp hθτ
        exact ⟨K, hK, fun t ht x => hRm t ⟨ht.1, ht.2.trans hθτ'.le⟩ x⟩ }
  exact ⟨S, rfl, hc, hRm⟩
end DifferentialGeometry.PDE.RicciFlow
