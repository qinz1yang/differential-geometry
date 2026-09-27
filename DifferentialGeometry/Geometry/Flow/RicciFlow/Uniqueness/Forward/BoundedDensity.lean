import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.WeightedEnergy
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.ExponentialWeight
import DifferentialGeometry.Analysis.Calculus.Cutoff.RiemannianExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.WeightedIntegrability
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem forward_unique_on_Ioo_of_uniform_bounds_of_bounded_density_tendsto_zero [ConnectedSpace M]
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (g₀ : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g₀)
    (p : M) {q Λ D : ℝ} (hq : 0 ≤ q) (hΛ : 1 ≤ Λ)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow g₀
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hbase : ∀ t ∈ Ioo a b, ∀ x, ∀ v : TangentSpace I x,
      Λ⁻¹ * g₀.inner x v v ≤ (g₁ t).inner x v v ∧
        (g₁ t).inner x v v ≤ Λ * g₀.inner x v v)
    (hD : ∀ t ∈ Ioo a b, ∀ x, forwardUniqueDensity (I := I) g₁ g₂ t x ≤ D)
    (hzero : ∀ x, Tendsto (fun t => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (𝓝[>] a) (𝓝 0)) :
    ∀ t ∈ Ioo a b, g₁ t = g₂ t := by
  let c : ℝ := q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E + 1
  have hc : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * c := by
    have hn : 0 ≤ q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E := by positivity
    dsimp only [c]
    linarith
  obtain ⟨η, hηpos, _, hηgrad, hηsq⟩ :=
    exists_positive_smooth_exp_distance_weight_integrable_sq g₀ hcomplete p hq hRic hc
  let μ : Measure M := ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) •
    riemannianVolumeMeasure (I := I) (M := M) g₀
  have hημ : Integrable (fun x => η x ^ 2) μ := hηsq.smul_measure ENNReal.ofReal_ne_top
  have hμ (t : ℝ) (ht : t ∈ Ioo a b) : riemannianMeasureFamily g₁ t ≤ μ := by
    rw [riemannianMeasureFamily_def]
    exact volumeMeasure_le (I := I) (M := M) g₀ (g₁ t) (zero_lt_one.trans_le hΛ) (fun x v => (hbase t ht x v).2)
  have hηgradAll : ∀ t ∈ Ioo a b, ∀ x,
      normSq0S (g₁ t) x 1 (differential1FormFun η x) ≤
        (Λ * (9 * c ^ 2)) * η x ^ 2 := by
    intro t ht x
    have htensor := normSq0S_upper_le_of_equiv g₀ (g₁ t) x 1 hΛ (hbase t ht x)
      (differential1FormFun η x)
    rw [pow_one] at htensor
    exact (htensor.trans (mul_le_mul_of_nonneg_left (hηgrad x)
      (zero_le_one.trans hΛ))).trans_eq (mul_assoc _ _ _).symm
  let Kex := manifoldCompactExhaustion (I := I) (M := M)
  obtain ⟨L, _, χ, hχsupp, hχrange, hχone, hχgrad⟩ :=
    Geometry.Metric.exists_contMDiff_compactExhaustion_cutoff_of_uniformEquivalent
      g₀ hcomplete p Kex g₁ (Ioo a b) hΛ hbase
  have hweighted (t : ℝ) (ht : t ∈ Ioo a b) :
      Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily g₁ t) := by
    have hdom := hημ.const_mul |D|
    have hdmeas := ((η.contMDiff.continuous.pow 2).mul (dens_continuous g₁ g₂ t)).aestronglyMeasurable (μ := μ)
    apply (hdom.mono' hdmeas ?_).mono_measure (hμ t ht)
    filter_upwards [] with x
    change ‖η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x‖ ≤ |D| * η x ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (density_nonneg g₁ g₂ t x))]
    exact (mul_le_mul_of_nonneg_left ((hD t ht x).trans (le_abs_self D))
      (sq_nonneg _)).trans_eq (mul_comm _ _)
  have htime : ∀ v ∈ Ioo a b, IntervalIntegrable
      (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily g₁ t) volume a v := by
    intro v hv
    have hs : Ioo a v ⊆ Ioo a b := fun t ht => ⟨ht.1, ht.2.trans hv.2⟩
    exact intervalIntegrable_weighted_forwardUniqueDensity_on_Ioo g₁ g₂ η η.contMDiff.continuous hv.1.le
      (fun t ht => hμ t (hs ht)) hημ (fun t ht => hD t (hs ht))
      (fun α i j => (hjoint₁ α i j).mono (prod_mono_left hs))
      (fun α i j => (hjoint₂ α i j).mono (prod_mono_left hs))
  apply forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero
    g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂ η
    (by positivity) hηgradAll Kex χ hχsupp hχone hχrange
    hχgrad hweighted htime (fun _ _ => Eventually.of_forall fun x => (hηpos x).ne')
    μ (fun x => |D| * η x ^ 2)
  · filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact hμ t ht
  · exact hημ.const_mul |D|
  · filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact Eventually.of_forall fun x =>
      (mul_le_mul_of_nonneg_left ((hD t ht x).trans (le_abs_self D))
        (sq_nonneg _)).trans_eq (mul_comm _ _)
  · exact Eventually.of_forall hzero

end DifferentialGeometry.PDE.RicciFlow
