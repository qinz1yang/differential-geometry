import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section

open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem metric_right_derivative_of_closed_gram
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hRF : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) t)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (g t).inner x v w)
      (-2 * ricciTensor (g a) x v w) (Ici a) a := by
  have hmetric := metricFamilySmoothOn_of_chartGram g hab
    (fun x₀ i j => (hgram x₀ i j).mono (Set.prod_mono_left Ioo_subset_Icc_self))
    (fun x₀ i j => ((hgram x₀ i j).mono
      (Set.prod_mono_left Ico_subset_Icc_self)).continuousOn)
  have hRicField := ricciCont_of_joint g (Icc a b) (uniqueDiffOn_Icc hab) hgram
  apply metric_right_derivative_of_interior hab g hmetric.coeff_cont ?_ hRF x v w
  intro y u z
  have hRic : ContinuousOn (fun t => ricciTensor (g t) y u z) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Icc a b => ricciTensor (g t.val) y u z)
    have h := hRicField.eval_continuous
      (P := Icc a b) (τ := Subtype.val) (b := fun _ => y)
      continuous_subtype_val (fun t => t.property) continuous_const
      (v := fun i _ => vec2 u z i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using h
  exact hRic.mono Ico_subset_Icc_self

theorem solutionOn_of_closed_gram
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hRF : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) t) :
    IsSolutionOn
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)) := by
  apply solutionOn_of_joint hab g
  · intro x₀ i j
    exact (hgram x₀ i j).mono (Set.prod_mono_left Ico_subset_Icc_self)
  · intro t ht x v w
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · subst t
      exact metric_right_derivative_of_closed_gram hab g hgram hRF x v w
    · exact (hRF t ⟨hlt, ht.2⟩ x v w).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow

end
