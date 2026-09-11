import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarDecayControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeComparisonReverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMetricLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarBoundAdditiveDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

private local instance ancientVolumeRatioInvariantC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem ancient_asymptoticVolumeRatio_eq_of_later_scalar_decay
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hcomplete : ∀ t ≤ (0 : ℝ), RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurvature : ∀ t ≤ (0 : ℝ), ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (htrace : ∀ t ∈ ancientTimeInterval.carrier, ∀ (x : M) (V : TangentSpace I x),
      0 ≤ derivWithin (fun s : ℝ => S.scalar s x) ancientTimeInterval.carrier t +
        2 * (S.base.metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x) V +
        2 * metricRicci (I := I) (M := M) (S.base.metric t) x (vec2 V V))
    {t₁ t₂ : ℝ} (ht₁₂ : t₁ < t₂) (ht₂ : t₂ ≤ 0) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) (S.base.metric t₂) p x).toReal →
        S.scalar t₂ x ≤ eps) :
    asymptoticVolumeRatio (S.base.metric t₁) p =
      asymptoticVolumeRatio (S.base.metric t₂) p := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have ht₁ : t₁ ≤ 0 := ht₁₂.le.trans ht₂
  have hslab : Icc t₁ t₂ ⊆ ancientTimeInterval.carrier := fun _ hs => hs.2.trans ht₂
  have hregular : Ioo t₁ t₂ ⊆ ancientTimeInterval.regular := fun _ hs => hs.2.trans_le ht₂
  have hRicNonneg (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace I x) :
      0 ≤ S.ricciAt t x (vec2 v v) := by
    change 0 ≤ metricRicciAt (I := I) (S.base.metric t) x (vec2 v v)
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (S.base.metric t) x (hcurvature t ht x) v
  have hRicBelow (t : ℝ) (ht : t ≤ 0) : RicciBoundedBelow (I := I) (S.base.metric t) 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact hRicNonneg t ht x v
  have hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      (S.base.metric t₂).inner x v v ≤ (S.base.metric t₁).inner x v v := by
    intro x v
    have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior S hS
      hslab hregular (fun s hs y w => hRicNonneg s (hs.2.le.trans ht₂) y w) x v
    exact hanti ⟨le_rfl, ht₁₂.le⟩ ⟨ht₁₂.le, le_rfl⟩ ht₁₂.le
  have hdist (x : M) :
      riemannianEDistOf (I := I) (S.base.metric t₂) p x ≤
        riemannianEDistOf (I := I) (S.base.metric t₁) p x :=
    edistOf_mono (S.base.metric t₂) (S.base.metric t₁) hmetric p x
  obtain ⟨C, _, hC, hCslab, hexception⟩ := ancient_scalar_decay_compact_control S hS
    htrace hcurvature (t₁ := t₁) ht₂ (hcomplete t₂ ht₂) p hdecay
  have heps (eps : ℝ) (heps : 0 < eps) :
      ENNReal.ofReal (Real.sqrt (Real.exp (-(2 * eps * (t₂ - t₁))) ^ Module.finrank ℝ E)) *
          asymptoticVolumeRatio (S.base.metric t₁) p ≤
        asymptoticVolumeRatio (S.base.metric t₂) p := by
    obtain ⟨D, _, hcompact, hRsmall⟩ := hexception eps heps
    let K := riemannianClosedBallOf (I := I) (S.base.metric t₂) p D
    have hRicSmall : ∀ s ∈ Ioo t₁ t₂, ∀ x ∈ Kᶜ, ∀ v : TangentSpace I x,
        S.ricciAt s x (vec2 v v) ≤ eps * (S.base.metric s).inner x v v := by
      intro s hs x hx v
      have hR : metricScalarAt (I := I) (S.base.metric s) x ≤ eps :=
        hRsmall s ⟨hs.1.le, hs.2.le⟩ x hx
      have hhalf : metricScalarAt (I := I) (S.base.metric s) x / 2 ≤ eps := by linarith
      have hv : 0 ≤ (S.base.metric s).inner x v v := by
        by_cases hzero : v = 0
        · simp [hzero]
        · exact ((S.base.metric s).pos x v hzero).le
      have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
        (S.base.metric s) x (hcurvature s (hs.2.le.trans ht₂) x) v
      exact hupper.trans (mul_le_mul_of_nonneg_right hhalf hv)
    apply asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact
      (S.base.metric t₁) (S.base.metric t₂) (hcomplete t₁ ht₁) (hcomplete t₂ ht₂)
      (hRicBelow t₁ ht₁) (hRicBelow t₂ ht₂) p hcompact (Real.exp_pos _) hdist
    intro x hx v
    exact metric_inner_lower_bound_of_ricci_upper_interior S hS ht₁₂.le
      hslab hregular hRicSmall hx v
  have hforward : asymptoticVolumeRatio (S.base.metric t₁) p ≤
      asymptoticVolumeRatio (S.base.metric t₂) p := by
    have hc : Continuous (fun eps : ℝ =>
        ENNReal.ofReal (Real.sqrt (Real.exp (-(2 * eps * (t₂ - t₁))) ^ Module.finrank ℝ E))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).mul continuous_const).neg).pow _))
    have hfactor : Tendsto (fun eps : ℝ =>
        ENNReal.ofReal (Real.sqrt (Real.exp (-(2 * eps * (t₂ - t₁))) ^ Module.finrank ℝ E)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero, one_pow,
        Real.sqrt_one, ENNReal.ofReal_one] using
          (hc.tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
    have hlim : Tendsto (fun eps : ℝ =>
        ENNReal.ofReal (Real.sqrt (Real.exp (-(2 * eps * (t₂ - t₁))) ^ Module.finrank ℝ E)) *
          asymptoticVolumeRatio (S.base.metric t₁) p)
        (𝓝[>] (0 : ℝ)) (𝓝 (asymptoticVolumeRatio (S.base.metric t₁) p)) := by
      simpa only [one_mul] using ENNReal.Tendsto.mul_const hfactor (Or.inl one_ne_zero)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with eps hepspos
    exact heps eps hepspos
  have hB : 0 ≤ (10 / 3 : ℝ) *
      Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * C) * (t₂ - t₁) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr ht₁₂.le)
  have hbackward : asymptoticVolumeRatio (S.base.metric t₂) p ≤
      asymptoticVolumeRatio (S.base.metric t₁) p := by
    apply asymptoticVolumeRatio_le_of_additive_distance_and_metric_le
      (S.base.metric t₁) (S.base.metric t₂) (hcomplete t₁ ht₁) (hcomplete t₂ ht₂)
      (hRicBelow t₁ ht₁) (hRicBelow t₂ ht₂) p hB ?_ hmetric
    intro x
    have h := ricciFlow_additive_distance_bound_of_scalar_upper S hS hdim
      (inferInstance : ConnectedSpace M) ht₁₂.le hC hslab hregular
      (fun s hs => hcomplete s (hs.2.trans ht₂))
      (fun s hs => hcurvature s (hs.2.trans ht₂)) (fun s hs x => (hCslab s hs x).2) p x
    linarith [h.2]
  exact le_antisymm hforward hbackward

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
